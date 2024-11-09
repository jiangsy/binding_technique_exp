-- Signature for System F

-- the types
ty : Type
tm : Type

-- the constructors for ty
arr : ty -> ty -> ty
all : (bind ty in ty) -> ty

-- the constructors for tm
app  : tm -> tm -> tm
lam  : ty -> (bind tm in tm) -> tm
tapp : tm -> ty -> tm
tlam : (bind ty in tm) -> tm