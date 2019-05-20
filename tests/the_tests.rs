use phantom_fields::phantom_fields;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u32)]
pub enum DisplayMode {
  Good = 0,
  Bad = 1,
  Ugly = 2,
}

pub const CONST_TEST_VALUE: u32 = 1 << 13;

#[derive(Debug, Default, Clone, Copy)]
#[repr(transparent)]
pub struct PhantomFieldsDemo(u32);

impl PhantomFieldsDemo {
  phantom_fields! {
    self.0: u32,
    /// enum_example docs
    enum_example: 0-2=DisplayMode<Good, Bad, Ugly>,
    bool_example: 3,
    int_example: 6-7,
    enum_example2: 10-12=DisplayMode<Good, Bad, Ugly>,
    const_example: CONST_TEST_VALUE,
  }
}

#[test]
fn enum_example_test() {
  assert_eq!(PhantomFieldsDemo::ENUM_EXAMPLE_MASK, 0b111);
  for &dm in [DisplayMode::Good, DisplayMode::Bad, DisplayMode::Ugly].iter() {
    assert_eq!(PhantomFieldsDemo(dm as u32).enum_example(), dm);
    assert_eq!(PhantomFieldsDemo(0).with_enum_example(dm).enum_example(), dm);
  }
}

#[test]
fn bool_example_test() {
  assert_eq!(PhantomFieldsDemo::BOOL_EXAMPLE_BIT, 1 << 3);
  assert!(!PhantomFieldsDemo(0).bool_example());
  assert!(PhantomFieldsDemo(PhantomFieldsDemo::BOOL_EXAMPLE_BIT).bool_example());
  assert!(PhantomFieldsDemo(0).with_bool_example(true).bool_example());
}

#[test]
fn int_example_test() {
  assert_eq!(PhantomFieldsDemo::INT_EXAMPLE_MASK, 0b11 << 6);
  assert_eq!(PhantomFieldsDemo(0).int_example(), 0);
  assert_eq!(PhantomFieldsDemo(PhantomFieldsDemo::INT_EXAMPLE_MASK).int_example(), 0b11);
  for i in 0..=0b11 {
    assert_eq!(PhantomFieldsDemo(0).with_int_example(i).int_example(), i);
  }
}

#[test]
fn enum_example2_test() {
  assert_eq!(PhantomFieldsDemo::ENUM_EXAMPLE2_MASK, 0b111 << 10);
  for &dm in [DisplayMode::Good, DisplayMode::Bad, DisplayMode::Ugly].iter() {
    assert_eq!(PhantomFieldsDemo((dm as u32) << 10).enum_example2(), dm);
    assert_eq!(PhantomFieldsDemo(0).with_enum_example2(dm).enum_example2(), dm);
  }
}

#[test]
fn const_example_test() {
  assert!(!PhantomFieldsDemo(0).const_example());
  assert!(PhantomFieldsDemo(CONST_TEST_VALUE).const_example());
  assert!(PhantomFieldsDemo(0).with_const_example(true).const_example());
}
