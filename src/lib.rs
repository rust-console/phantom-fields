// Note(Lokathor): this extern crate is necessary even in 2018 for whatever
// reason that I'm sure is stupid.
extern crate proc_macro;

use core::str::FromStr;
use proc_macro::TokenStream;
use proc_macro2::Span;
use quote::quote;
use syn::{
  parse::{Parse, ParseStream, Result},
  parse_macro_input,
  spanned::Spanned,
  Attribute, Error, Ident, LitInt, Token, Type, TypePath,
};

// Phantom Fields

enum PhantomEntry {
  Enum {
    attributes: Vec<Attribute>,
    name: String,
    start: u64,
    end: u64,
    enum_type: Ident,
    variant_list: Vec<String>,
  },
  Integer {
    attributes: Vec<Attribute>,
    name: String,
    start: u64,
    end: u64,
  },
  Bool {
    attributes: Vec<Attribute>,
    name: String,
    bit: u64,
  },
  Const {
    attributes: Vec<Attribute>,
    name: String,
    const_ident: Ident,
  },
}

struct PhantomFields {
  self_member_type: Type,
  entries: Vec<PhantomEntry>,
}

impl Parse for PhantomFields {
  fn parse(input: ParseStream) -> Result<Self> {
    let _ = input.parse::<Token![self]>()?;
    let _ = input.parse::<Token![.]>()?;
    let lit = input.parse::<LitInt>()?;
    if lit.value() != 0 {
      return Err(Error::new(lit.span(), "Currently only self.0 is supported"));
    }
    let _ = input.parse::<Token![:]>()?;
    let self_member_type: Type = {
      let tp = input.parse::<TypePath>()?;
      let tp_end_string = match tp.path.segments.last().expect("no type given") {
        syn::punctuated::Pair::Punctuated(path_segment, _colon2) => path_segment.ident.to_string(),
        syn::punctuated::Pair::End(path_segment) => path_segment.ident.to_string(),
      };
      match tp_end_string.as_ref() {
        "u8" | "i8" | "u16" | "i16" | "u32" | "i32" | "usize" | "isize" | "u64" | "i64" => Type::Path(tp),
        _ => {
          return Err(Error::new(tp.span(), format!("Unsupported target type: {:?}", tp_end_string)));
        }
      }
    };
    let _ = input.parse::<Token![,]>()?;
    //
    let mut entries: Vec<PhantomEntry> = vec![];
    'entry_loop: loop {
      if input.is_empty() {
        break;
      }
      let attributes = input.call(Attribute::parse_outer)?;
      let name = input.parse::<Ident>()?.to_string();
      let _ = input.parse::<Token![:]>()?;
      let lookahead_int_or_ident = input.lookahead1();
      if lookahead_int_or_ident.peek(LitInt) {
        let start = input.parse::<LitInt>()?.value();
        let lookahead_bool_or_span = input.lookahead1();
        if lookahead_bool_or_span.peek(Token![,]) {
          // bool entry
          entries.push(PhantomEntry::Bool {
            attributes,
            name,
            bit: start,
          });
          let _ = input.parse::<Token![,]>()?;
          continue 'entry_loop;
        } else if lookahead_bool_or_span.peek(Token![-]) {
          // spanning entry
          let _ = input.parse::<Token![-]>()?;
          let end = input.parse::<LitInt>()?.value();
          let lookahead = input.lookahead1();
          if lookahead.peek(Token![=]) {
            // enum span
            let _ = input.parse::<Token![=]>()?;
            let enum_type = input.parse::<Ident>()?;
            let mut variant_list = vec![];
            let _ = input.parse::<Token![<]>()?;
            'variant_gather_loop: loop {
              variant_list.push(input.parse::<Ident>()?.to_string());
              let lookahead = input.lookahead1();
              if lookahead.peek(Token![>]) {
                // end of list
                let _ = input.parse::<Token![>]>()?;
                break 'variant_gather_loop;
              } else if lookahead.peek(Token![,]) {
                // more to gather
                let _ = input.parse::<Token![,]>()?;
                continue 'variant_gather_loop;
              } else {
                return Err(lookahead.error());
              }
            }
            entries.push(PhantomEntry::Enum {
              attributes,
              name,
              start,
              end,
              enum_type,
              variant_list,
            });
            let _ = input.parse::<Token![,]>()?;
            continue 'entry_loop;
          } else if lookahead.peek(Token![,]) {
            // int span
            entries.push(PhantomEntry::Integer {
              attributes,
              name,
              start,
              end,
            });
            let _ = input.parse::<Token![,]>()?;
            continue 'entry_loop;
          } else {
            return Err(lookahead.error());
          }
        } else {
          return Err(lookahead_bool_or_span.error());
        }
      } else if lookahead_int_or_ident.peek(Ident) {
        let const_ident = input.parse::<Ident>()?;
        // constant literal entry
        entries.push(PhantomEntry::Const {
          attributes,
          name,
          const_ident,
        });
        let _ = input.parse::<Token![,]>()?;
        continue 'entry_loop;
      } else {
        return Err(lookahead_int_or_ident.error());
      }
    }
    Ok(PhantomFields { self_member_type, entries })
  }
}

/// Declares a struct to have "phantom" fields. Use within an `impl` block.
///
/// At the moment, this only supports tuple structs and only targets the `0`
/// field of said structs. It's intended for use with newtype'd unsigned
/// integers of various sizes.
///
/// The proc-macro's grammar is fairly simple once you get the hang of it but
/// there's several possibilities you can declare.
///
/// * `self.0: [TYPE],` to declare the type of the `self.0` field.
/// * Then you declare 0 or more phantom fields:
///   * Each phantom field can have attributes, which is mostly intended for
///     allowing rustdoc.
///   * Then the name of the field, followed by `:`
///   * Then you describe "where" the field is with a `,` at the end:
///     * A single integer makes a bool field at that bit.
///     * An `a-b` integer span makes an integer field in that inclusive bit
///       range.
///     * An `a-b=ENUM<TAG1,...,TAG_N>` location makes an enum field of the type
///       given that can be any of the tags you specify. In the decoding method
///       an `_ => unreachable!()` branch is placed after all tags, so if you
///       specify less tags than possible bit patterns (eg: only 3 tags for a
///       2-bit field) your code can potentially panic.
///     * An identifier will assume that the identifier is already a const
///       declared somewhere in scope, and use that as the bit location of a
///       bool-typed field.
/// * Enum and integer phantom fields also get a `FOO_MASK` const added to the
///   struct type for each field named `foo`. This const is what takes on the
///   attributes you specified for that phantom field.
/// * Bool phantom fields get a `FOO_BIT` const added to the struct for each
///   field named foo. This gets the attributes of the field.
/// * Const phantom fields don't get added to the struct, they're already a
///   const somewhere after all.
///
/// Once this is all set up you'll of course want to use the phantom fields:
///
/// * phantom fields can be _read_ using their name as a the method name,
///   similar to normal rust "getters".
/// * phantom fields can be _replaced_ "builder style" by taking `self` and
///   giving a new value using `with_field`. This is `const`, so you can use it
///   to declare a const that has some particular setting combination.
///
/// I think it makes more sense if you see it in action. Here's an extended
/// example of all the situations supported.
///
/// ```rust,no_run
/// use phantom_fields::phantom_fields;
///
/// #[derive(Debug, Clone, Copy, PartialEq, Eq)]
/// #[repr(u32)]
/// pub enum DisplayMode {
///   Good = 0,
///   Bad = 1,
///   Ugly = 2,
/// }
///
/// pub const CONST_TEST_VALUE: u32 = 1 << 13;
///
/// #[derive(Debug, Default, Clone, Copy)]
/// #[repr(transparent)]
/// pub struct PhantomFieldsDemo(u32);
///
/// impl PhantomFieldsDemo {
///   phantom_fields! {
///     self.0: u32,
///     /// enum_example docs
///     enum_example: 0-2=DisplayMode<Good, Bad, Ugly>,
///     bool_example: 3,
///     /// This gives us a 2-bit field
///     int_example: 6-7,
///     const_example: CONST_TEST_VALUE,
///   }
/// }
/// ```
#[proc_macro]
pub fn phantom_fields(input: TokenStream) -> TokenStream {
  let PhantomFields { self_member_type, entries } = parse_macro_input!(input as PhantomFields);

  let mut out_text = String::new();

  for entry in entries.into_iter() {
    match entry {
      PhantomEntry::Enum {
        attributes,
        name,
        start,
        end,
        enum_type,
        variant_list,
      } => {
        for attribute in attributes.into_iter() {
          out_text.push_str(&format!("{}\n", TokenStream::from(quote! { #attribute })));
        }
        let mask_name = Ident::new(&format!("{}_MASK", name.to_uppercase()), Span::call_site());
        let read_name = Ident::new(&name.clone(), Span::call_site());
        let with_name = Ident::new(&format!("with_{}", name), Span::call_site());
        let width = (end - start) + 1;
        out_text.push_str(&format!(
          "{}\n",
          TokenStream::from(quote! {
            #[allow(clippy::identity_op)]
            pub const #mask_name: #self_member_type = ((1<<(#width))-1) << #start;

            #[allow(missing_docs)]
            pub fn #read_name(self) -> #enum_type
          })
        ));
        out_text.push('{');
        out_text.push_str(&format!(
          "{}\n",
          TokenStream::from(quote! {
            match (self.0 & Self::#mask_name) >> #start
          })
        ));
        out_text.push('{');
        let enum_type_string = enum_type.to_string();
        for (i, variant) in variant_list.iter().enumerate() {
          out_text.push_str(&format!("{} => {}::{},\n", i, enum_type_string, variant));
        }
        out_text.push_str("_ => unreachable!(),");
        out_text.push_str("} }\n");
        out_text.push_str(&format!(
          "{}\n",
          TokenStream::from(quote! {
            #[allow(missing_docs)]
            pub const fn #with_name(self, #read_name: #enum_type) -> Self {
              Self((self.0 & !Self::#mask_name) | (((#read_name as #self_member_type) << #start) & Self::#mask_name))
            }
          })
        ));
      }
      PhantomEntry::Integer {
        attributes,
        name,
        start,
        end,
      } => {
        for attribute in attributes.into_iter() {
          out_text.push_str(&format!("{}\n", TokenStream::from(quote! { #attribute })));
        }
        let mask_name = Ident::new(&format!("{}_MASK", name.to_uppercase()), Span::call_site());
        let read_name = Ident::new(&name.clone(), Span::call_site());
        let with_name = Ident::new(&format!("with_{}", name), Span::call_site());
        let width = (end - start) + 1;
        out_text.push_str(&format!(
          "{}\n",
          TokenStream::from(quote! {
            #[allow(clippy::identity_op)]
            pub const #mask_name: #self_member_type = ((1<<(#width))-1) << #start;

            #[allow(missing_docs)]
            pub const fn #read_name(self) -> #self_member_type {
              (self.0 & Self::#mask_name) >> #start
            }

            #[allow(missing_docs)]
            pub const fn #with_name(self, #read_name: #self_member_type) -> Self {
              Self((self.0 & !Self::#mask_name) | ((#read_name << #start) & Self::#mask_name))
            }
          })
        ));
      }
      PhantomEntry::Bool { attributes, name, bit } => {
        for attribute in attributes.into_iter() {
          out_text.push_str(&format!("{}\n", TokenStream::from(quote! { #attribute })));
        }
        let const_name = Ident::new(&format!("{}_BIT", name.to_uppercase()), Span::call_site());
        let read_name = Ident::new(&name.clone(), Span::call_site());
        let with_name = Ident::new(&format!("with_{}", name), Span::call_site());
        out_text.push_str(&format!(
          "{}\n",
          TokenStream::from(quote! {
            #[allow(clippy::identity_op)]
            pub const #const_name: #self_member_type = 1 << #bit;

            #[allow(missing_docs)]
            pub const fn #read_name(self) -> bool {
              (self.0 & Self::#const_name) != 0
            }

            // https://graphics.stanford.edu/~seander/bithacks.html#ConditionalSetOrClearBitsWithoutBranching
            #[allow(missing_docs)]
            pub const fn #with_name(self, bit: bool) -> Self {
              Self(self.0 ^ (((#self_member_type::wrapping_sub(0, bit as #self_member_type) ^ self.0) & Self::#const_name)))
            }
          })
        ));
      }
      PhantomEntry::Const {
        attributes,
        name,
        const_ident,
      } => {
        for attribute in attributes.into_iter() {
          out_text.push_str(&format!("{}\n", TokenStream::from(quote! { #attribute })));
        }
        let read_name = Ident::new(&name.clone(), Span::call_site());
        let with_name = Ident::new(&format!("with_{}", name), Span::call_site());
        out_text.push_str(&format!(
          "{}\n",
          TokenStream::from(quote! {
            #[allow(missing_docs)]
            pub const fn #read_name(self) -> bool {
              (self.0 & #const_ident) != 0
            }

            // https://graphics.stanford.edu/~seander/bithacks.html#ConditionalSetOrClearBitsWithoutBranching
            #[allow(missing_docs)]
            pub const fn #with_name(self, bit: bool) -> Self {
              Self(self.0 ^ (((#self_member_type::wrapping_sub(0, bit as #self_member_type) ^ self.0) & #const_ident)))
            }
          })
        ));
      }
    };
  }

  TokenStream::from_str(&out_text).map_err(|e| panic!("{:?}", e)).unwrap()
}
