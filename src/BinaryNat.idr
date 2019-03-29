module BinaryInt

||| A binary representation of integers
data Nat2 = Zbit | Ibit | Times2 Nat2 | Times2Plus1 Nat2

||| Binary addition
(+) : Nat2 -> Nat2 -> Nat2
(+) Zbit y = y                                                      --  0 +  y = y
(+) x Zbit = x                                                      --  x +  0 = x
(+) Ibit Ibit = Times2 Ibit                                         --  1 +  1 = 10
(+) Ibit (Times2 y) = Times2Plus1 y                                 --  1 + y0 = y1
(+) Ibit (Times2Plus1 y) = Times2 ((+) Ibit y)                      --  1 + y1 = (y+1)1
(+) (Times2 x) Ibit = Times2Plus1 x                                 -- x0 +  1 = x1
(+) (Times2 x) (Times2 y) = Times2 ((+) x y)                        -- x0 + y0 = (x+y)0
(+) (Times2 x) (Times2Plus1 y) = Times2Plus1 ((+) x y)              -- x0 + y1 = (x+y)1
(+) (Times2Plus1 x) Ibit = Times2 ((+) x Ibit)                      -- x1 +  1 = (x+1)0
(+) (Times2Plus1 x) (Times2 y) = Times2Plus1 ((+) x y)              -- x1 + y0 = (x+y)1
(+) (Times2Plus1 x) (Times2Plus1 y) = Times2 ((+) x ((+) y Ibit) )  -- x1 + y1 = (x+(y+1))0

||| 0 is additive identity -- an implication defined as function.
--leftPlusId : (x:Nat2) -> ((+) Zbit x) = x  -- Ends in a type "=" inhabited by Refl
--leftPlusId x = Refl
--rightPlusId : (x:Nat2) -> ((+) x Zbit) = x  -- Ends in a type "=" inhabited by Refl
--rightPlusId x = Refl

||| Isomorphism binary natural numbers to unary natural numbers
btou : Nat2 -> Nat
btou Zbit             = Z
btou Ibit             = S Z
btou (Times2 x)       = (btou x) + (btou x)
btou (Times2Plus1 x)  = S ((btou x) + (btou x))

utob : Nat -> Nat2
utob Z = Zbit
utob (S k) = (utob k) + Ibit


ZbitIsZ: utob Z = Zbit  -- This type checks, so inhabited by Refl
--ZbitIsZ = rewrite utob Z in utob Z = Zbit

IbitIsSZ :  utob (S Z) = Ibit  

leftIdBU : (x:Nat2) ->  (utob (btou x)) = x 
leftIdBU Zbit = ZbitIsZ     -- pattern matching on first variable so need to pre-reduce
leftIdBU Ibit = IbitIsSZ

