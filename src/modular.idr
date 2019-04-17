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
    {- 3 constructors, we mostly think of n, x, y as implicit.
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
{- 
    (LInd (x=y=>(x+n)=y) 
  & u={x=y}) 
  -------------------
    u={x=y}
  ------------------
    y=x (induct on u) 
   ------------------
    RInd y=x = y=(x+n) 
 -}
isSym (LInd u)   = RInd (isSym u) 
{- x=(y+n) => u={x=y} => y=x (induct) => (y+n)=x -}
isSym (RInd u)   = LInd (isSym u) 

{----- Proof of transitive property. -----}
total isTrans : (ModEq n x y) -> (ModEq n y z) -> (ModEq n x z)
--isTrans (RInd _) (LInd _) = ?isTrans_rhs_1
{- x=x & x=y => x=y -}
isTrans (Reflex x) v = v
isTrans u (Reflex y) = u
{- ((x=y=>(x+n)=y) & y=z) => x=y & y=z => x=z (induct) => (x+n)=z -}
isTrans (LInd u) v = LInd (isTrans u v)
isTrans u (RInd v) = RInd (isTrans u v)
{- (x=y=>x=(y+n)) & (y=z=>(y+n)=z) => x=y & y=z => x=z (induct) -}
isTrans (RInd u) (LInd v) {n} {x} {y=x+n} = isTrans u v  -- Note: need to expose implicit y=x+n

{----- Proof of congruence property. -----}
total isCong : (ModEq n x y) -> (ModEq n a b) -> (ModEq n (x+a) (y+b))
isCong (Reflex x) (Reflex a) = Reflex (x+a)
isCong {n} (LInd {x} u) (Reflex a) = 
    {-
        (x+n) == y (mod n) because u={x == y (mod n)}
        a == a (mod n)
        ---------------------------------------------
        x+a == y+a (mod n)        (induct)
        ---------------------------------------------
        (x+a)+n == y+a (mod n)    (LInd)
        ---------------------------------------------
        x+(a+n) == y+a (mod n)    (Associative)
        ---------------------------------------------
        x+(n+a) == y+a (mod n)    (Commutative)
        ---------------------------------------------
        (x+n)+a == y+a (mod n)    (Associative)
    -}
    let w = (x+a)+n in LInd (isCong u (Reflex a))
    rewrite plusCommutative n x in 
        rewrite plusAssociative n x a in 
            rewrite plusAssociative (x+a) n in w
                
isCong {n} (RInd {y} u) (Reflex a) = 
--    rewrite plusAssociative y n a in 
        rewrite plusCommutative a n in 
            rewrite plusAssociative y a n in
                RInd (isCong u (Reflex a))
isCong {n} {x} u (LInd {x=a} v) =   -- imiplicitly need n, x, a in scope.
    {- 
        u={x == y (mod n) }
        (a+n) == b only if, v={a==b}
        ----------------------
        x+a == y+b by induction on u, v
        ----------------------
        (x+a)+n == y+b by LInd
        x+(a+n) == y+b by associativity
     -}
    rewrite plusAssociative x a n  in LInd (isCong u v)
isCong {n} {y} u (RInd {y=b} v) =   -- imiplicitly need n, x, a in scope.
    {- 
        u={x == y (mod n) }
        a == (b+n) only if, v={a==b}
        ----------------------
        x+a == y+b by induction on u, v
        ----------------------
        x+a == (y+b)+n by RInd
        x+a == y+(b+n) by associativity
    -}
    rewrite plusAssociative y b n  in RInd (isCong u v)
