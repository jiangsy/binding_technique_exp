-- the types
typ : Type
exp : Type

-- the constructors for typ
typ_arr : typ -> typ -> typ
typ_all : (bind typ in typ) -> typ

-- the constructors for exp
exp_app  : exp -> exp -> exp
exp_abs  : typ -> (bind exp in exp) -> exp
exp_tapp : exp -> typ -> exp
exp_tabs : (bind typ in exp) -> exp