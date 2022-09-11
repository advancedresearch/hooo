use hooo::user_input::check_file;

#[test]
fn test_sources() {
    check_file("source/primitives/and.hooo").unwrap();
    check_file("source/primitives/or.hooo").unwrap();
    check_file("source/primitives/eq.hooo").unwrap();
    check_file("source/primitives/imply.hooo").unwrap();
    check_file("source/primitives/pow.hooo").unwrap();
    check_file("source/primitives/ty.hooo").unwrap();
    check_file("source/primitives/wave.hooo").unwrap();
    check_file("source/primitives/qubit.hooo").unwrap();
    check_file("source/primitives/true.hooo").unwrap();
    check_file("source/primitives/false.hooo").unwrap();
    check_file("source/and/fst.hooo").unwrap();
    check_file("source/and/snd.hooo").unwrap();
    check_file("source/and/and_to_eq.hooo").unwrap();
    check_file("source/and/eq_to_and.hooo").unwrap();
    check_file("source/eq/transport.hooo").unwrap();
    check_file("source/sym/flip.hooo").unwrap();
    check_file("source/imply/modus_ponens.hooo").unwrap();
    check_file("source/imply/modus_tollens.hooo").unwrap();
    check_file("source/hooo/tr_eq.hooo").unwrap();
    check_file("source/hooo/transport_tr.hooo").unwrap();
    check_file("source/qubit/subst.hooo").unwrap();
    check_file("source/sesh/to_qu_not.hooo").unwrap();
    check_file("source/sesh/to_not_qu.hooo").unwrap();
}

#[test]
fn new_test() {
}
