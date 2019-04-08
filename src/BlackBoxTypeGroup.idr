
||| ===========================================================================
||| Universal algebra 
||| ===========================================================================

||| A general n-ary operation on terms of a common type.
data Op n a = List a n -> Maybe a 
||| A general algebraic structure on terms of type a.
data Algebraic a = List Op n a

data Formula a Algebraic a = {x:a} | 



data SLP a {gens:List a} = gens

== : {x:type} -> {y:type} -> type where
    Same x = Refl

record Group a {gens:List a} {==:a->a->type} where
    constructor MkGroup
    * : Op 2 a
    - : Op 1 a
    id : Op 0 a
    gens : List a
    == : {x:type} -> {y:type} -> type where
        Same x = Refl
    ascLaw : (x:SLP gens) -> (y:SLP gens) -> (z:SLP gens) -> x*(y*z) == (x*y)*z
    invLaw : (x:SLP a) -> (x*(-x)) == id
    idLaw : (x:SLP a) -> x*id == x