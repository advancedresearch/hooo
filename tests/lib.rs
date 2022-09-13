use hooo::user_input::check_file;

#[test]
fn test_sources() {
    assert_eq!(0, check_file("source/primitives/and.hooo").unwrap());
    assert_eq!(0, check_file("source/primitives/or.hooo").unwrap());
    assert_eq!(0, check_file("source/primitives/eq.hooo").unwrap());
    assert_eq!(0, check_file("source/primitives/imply.hooo").unwrap());
    assert_eq!(0, check_file("source/primitives/pow.hooo").unwrap());
    assert_eq!(0, check_file("source/primitives/ty.hooo").unwrap());
    assert_eq!(0, check_file("source/primitives/wave.hooo").unwrap());
    assert_eq!(0, check_file("source/primitives/qubit.hooo").unwrap());
    assert_eq!(0, check_file("source/primitives/qual.hooo").unwrap());
    assert_eq!(0, check_file("source/primitives/true.hooo").unwrap());
    assert_eq!(0, check_file("source/primitives/false.hooo").unwrap());
    assert_eq!(0, check_file("source/and/fst.hooo").unwrap());
    assert_eq!(1, check_file("source/and/snd.hooo").unwrap());
    assert_eq!(0, check_file("source/and/and_to_eq.hooo").unwrap());
    assert_eq!(1, check_file("source/and/eq_to_and.hooo").unwrap());
    assert_eq!(0, check_file("source/and/and_fst_tr.hooo").unwrap());
    assert_eq!(0, check_file("source/and/and_snd_tr.hooo").unwrap());
    assert_eq!(0, check_file("source/and/and_fst_fa.hooo").unwrap());
    assert_eq!(0, check_file("source/and/and_snd_fa.hooo").unwrap());
    assert_eq!(0, check_file("source/eq/transport.hooo").unwrap());
    assert_eq!(0, check_file("source/sym/flip.hooo").unwrap());
    assert_eq!(0, check_file("source/imply/modus_ponens.hooo").unwrap());
    assert_eq!(2, check_file("source/imply/modus_tollens.hooo").unwrap());
    assert_eq!(0, check_file("source/imply/to_rimply.hooo").unwrap());
    assert_eq!(0, check_file("source/imply/transitivity.hooo").unwrap());
    assert_eq!(0, check_file("source/hooo/tr_eq.hooo").unwrap());
    assert_eq!(0, check_file("source/hooo/transport_tr.hooo").unwrap());
    assert_eq!(0, check_file("source/qubit/subst.hooo").unwrap());
    assert_eq!(0, check_file("source/qubit/to_qual.hooo").unwrap());
    assert_eq!(10, check_file("source/qubit/qual_def.hooo").unwrap());
    assert_eq!(0, check_file("source/sesh/to_qu_not.hooo").unwrap());
    assert_eq!(0, check_file("source/sesh/to_not_qu.hooo").unwrap());
    assert_eq!(0, check_file("source/tauto/tauto_def.hooo").unwrap());
    assert_eq!(0, check_file("source/tauto/para_def.hooo").unwrap());
    assert_eq!(0, check_file("source/tauto/tauto_expand.hooo").unwrap());
    assert_eq!(0, check_file("source/tauto/para_expand.hooo").unwrap());
    assert_eq!(0, check_file("source/tauto/uniform_expand.hooo").unwrap());
    assert_eq!(5, check_file("source/tauto/uniform_def.hooo").unwrap());
}

#[test]
fn new_test() {
}