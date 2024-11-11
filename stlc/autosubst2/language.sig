exp : Type
typ : Type

exp_abs  : (bind exp in exp) -> exp
exp_app  : exp -> exp -> exp
exp_unit : exp

typ_unit : typ
typ_arr  : typ -> typ -> typ