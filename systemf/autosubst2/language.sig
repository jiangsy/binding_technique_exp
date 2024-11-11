-- Signature for System F

-- the types
ftyp : Type
fexp : Type

-- the constructors for ftyp
ftyp_arr : ftyp -> ftyp -> ftyp
ftyp_all : (bind ftyp in ftyp) -> ftyp

-- the constructors for fexp
fexp_app  : fexp -> fexp -> fexp
fexp_abs  : ftyp -> (bind fexp in fexp) -> fexp
fexp_tapp : fexp -> ftyp -> fexp
fexp_tabs : (bind ftyp in fexp) -> fexp