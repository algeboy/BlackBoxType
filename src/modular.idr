
data DivRem : (m:Nat) -> (n:PosNat) -> Type where   
    Division m
DivisionAlgo : (m:Nat) -> (n:PosNat) -> 

EuclideanAlgo : (a:Nat) -> (b:Nat) ->  
||| ---------------------------------------------------------------------------
||| A GCD type inhabited by proof by Bezout coefficients.
||| ---------------------------------------------------------------------------
data GCD : (a:Nat) -> (b:Nat) -> Type where
    Euclidean (s * a + t * b = c) = 