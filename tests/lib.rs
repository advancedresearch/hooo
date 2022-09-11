use hooo::user_input::check_file;

#[test]
fn test_syntax() {
    check_file("source/primitives/and.hooo").unwrap();
}
