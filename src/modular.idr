{-------------------------------------------------------------
            Equivlance relation rules mod n.
-------------------------------------------------------------}

|||
||| ModEq n x y is (aweful) prefix notation for a type x == y (mod n).
|||
||| This is a singleton dependent type, and it is inhabited solely
||| by its constructor.  So you can pattern match on tye constructor
||| by there are no values.
|||
data ModEq : (n:Nat) -> (x:Nat) -> (y:Nat) -> Type where
    {- 3 constructors, could be made 2 by symmetry?: 
        reflexive:      x==x (mod n), 
        left-induct:    x == y (mod n) => x+n == y      (mod n)
        right-induct:   x == y (mod n) => x == (y+n)    (mod n)
    -}
  Reflex : (x:Nat) -> ModEq n x x  --- Needs syntatic sugar, for now prefix
  LInd : (ModEq n x y) -> ModEq n (x+n) y
  RInd : (ModEq n x y) -> ModEq n x (y+n)

{- Proof of reflexive property. -}
total
isRefl : (x:Nat) -> ModEq n x x
isRefl x = Reflex x

{----- Proof of symmetric property. -----}
total
isSym : (ModEq n x y) -> ModEq n y x
{- x=x => x=x -}
isSym (Reflex x) = Reflex x
{- (x+n)=y => u={x=y} => y=x (induct) => y=(x+n) -}
isSym (LInd u)   = RInd (isSym u) 
{- x=(y+n) => u={x=y} => y=x (induct) => (y+n)=x -}
isSym (RInd u)   = LInd (isSym u) 

{----- Proof of transitive property. -----}
total
isTrans : (ModEq n x y) -> (ModEq n y z) -> (ModEq n x z)
--isTrans (RInd _) (LInd _) = ?isTrans_rhs_1
{- x=x & x=y => x=y -}
isTrans (Reflex x) v = v
isTrans u (Reflex y) = u
{- ((x=y=>(x+n)=y) & y=z) => x=y & y=z => x=z (induct) => (x+n)=z -}
isTrans (LInd u) v = LInd (isTrans u v)
isTrans u (RInd v) = RInd (isTrans u v)
{- (x=y=>x=(y+n)) & (y=z=>(y+n)=z) => x=y & y=z => x=z (induct) -}
isTrans (RInd u) (LInd v) = isTrans u v  -- Doesn't type-check, not sure why.

{----- Proof of congruence property. -----}
isCong : (ModEq n x y) -> (ModEq n a b) -> (ModEq n (x+a) (y+b))
-- 3 x 3 equivalence patterns.
isCong (Reflex x) (Reflex a) = Reflex (x+a)
{-
isCong (Reflex x) (LInd u) = case u => 
    Reflex a => LInd (Reflex (x+a) )
    LInd v => LInd (isCong (Reflex x) v)
    RInd v => LInd (isCong (Reflex x) v)
-}


{-
isCong (LInd n x y) (Reflex n a) = rewrite (x+n)+a in 
    LInd n (x+a)  -- needs a rewrite of (x+n)+a=(x+a)+n
isCong (LInd n x y) (LInd n a b) = rewrite ((x+n)+a)+n in 
    LInd n (LInd n (x+a)) (y+b) -- rewrite ((x+n)+a)+n=((x+a)+n)+n
isCong (LInd n x y) (RInd n a b) = rewrite ((x+n)+a) in 
    rewrite ((y+n)+b) in LINd n (RInd n (x+a)) (y+b)  -- rewrite ((x+n)+a) and ((y+n)+b)

isCong (RInd n x y) (Reflex n a) = rewrite (y+n)+b in 
    RInd n (y+b)  -- needs a rewrite of (y+n)+a=(x+a)+n
isCong (RInd n x y) (LInd n a b) = rewrite ((x+n)+a)+n in 
    RInd n (LInd n (x+a)) (y+b) -- rewrite ((x+n)+a)+n=((x+a)+n)+n
isCong (RInd n x y) (RInd n a b) = rewrite ((x+n)+a) in 
    rewrite ((y+n)+b) in RINd n (RInd n (x+a)) (y+b)  -- rewrite ((x+n)+a) and ((y+n)+b)
-}