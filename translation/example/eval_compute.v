Definition my_smt_result : SmtResult :=
    smt_query
        (SmtBoolNot
            (SmtBoolAnd
                (SmtBoolAnd SmtTrue
                    (SmtBoolEq
                        (SmtConditional
                            (SmtBoolEq (SmtConst {| intval := 0; intrange := Z_mod_modulus_range' 0 |})
                                (SmtConst {| intval := 0; intrange := Z_mod_modulus_range' 0 |}))
                            (SmtBitAdd (SmtConst {| intval := 1; intrange := Z_mod_modulus_range' 1 |})
                                (SmtConst {| intval := 0; intrange := Z_mod_modulus_range' 0 |}))
                            (SmtConst {| intval := 0; intrange := Z_mod_modulus_range' 0 |}))
                        (SmtConditional
                            (SmtBoolEq (SmtConst {| intval := 0; intrange := Z_mod_modulus_range' 0 |})
                                (SmtConst {| intval := 0; intrange := Z_mod_modulus_range' 0 |}))
                            (SmtBitAdd (SmtConst {| intval := 1; intrange := Z_mod_modulus_range' 1 |})
                                (SmtConst {| intval := 0; intrange := Z_mod_modulus_range' 0 |}))
                            (SmtConst {| intval := 0; intrange := Z_mod_modulus_range' 0 |})))) SmtTrue)).