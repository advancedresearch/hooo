use hooo::user_input::check_file;

#[test]
fn test_sources() {
    check_file("source/primitives/and.hooo").unwrap();
    check_file("source/and/fst.hooo").unwrap();
    check_file("source/and/snd.hooo").unwrap();
}
