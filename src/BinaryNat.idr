module BinaryInt

||| A type for binary representation of integers
data Nat2   = Zbit              --  0
            | Ibit              --  1 
            | Times2 Nat2       -- x0
            | Times2Plus1 Nat2  -- x1

||| Binary addition, case by case.
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


||| ---------------------------------------------------------------------------
||| Equality only supported by reflexive constructor `Same`
||| So `Same 5 : EqNat 5 5`  so `EqNat k k` is **always** inhabited.
||| However there is no constructor for `EqNat 4 5` for example, that type
||| exists but is **never** uninhabitted. I.e.
|||
||| *EqNat> the (EqNat 4 4) (Same _)  -- works, 4 replaces _
||| *EqNat> the (EqNat 4 5) (Same _)  -- fails, no solution to _
|||
||| ---------------------------------------------------------------------------
data EqNat : (i:Nat) -> (j:Nat) -> Type where
    Same : (k:Nat) -> EqNat k k

data EqNat2 : (i:Nat2) -> (j:Nat2) -> Type where
    Same : (k:Nat2) -> EqNat k k
    
||| ---------------------------------------------------------------------------
||| Function to lift equality inductively.
||| This isn't total but only used on equal inputs in the type checker.
||| ---------------------------------------------------------------------------
liftEq : (i:Nat) -> (j:Nat) -> (eq:EqNat i j) -> EqNat (S i) (S k)
liftEq k k Same k = Same (S k)

liftEqTimes2 : (i:Nat2) -> (j:Nat2) -> (eq:EqNat2 i j) -> EqNat2 (Times2 i) (Times2 k)
liftEq k k Same k = Same (Times2 k)
liftEqTimes2Plus1 : (i:Nat2) -> (j:Nat2) -> (eq:EqNat2 i j) -> EqNat2 (Times2Plus1 i) (Times2Plus1 k)
liftEq k k Same k = Same (Times2Plus1 k)

||| ---------------------------------------------------------------------------
||| Check equality and convert to Maybe EqNat
||| As usual define checkEqNat on the various constructors of Nat/Nat2
||| where the behavior is clear.  Makes an total function by induction.
|||
||| checkEqNat 4 5 = Nothing : Maybe EqNat 4 5
||| checkEqNat 4 4 = Just Same 4 : Maybe EqNat 4 4
|||
||| ---------------------------------------------------------------------------
checkEqNat : (i:Nat) -> (j:Nat) -> Maybe( i = j )
checkEqNat Z Z          = Just Refl
checkEqNat (S k) Z      = Nothing
checkEqNat Z (S k)      = Nothing
checkEqNat (S k) (S m)  = case checkEqNat k m of
                            Nothing => Nothing
                            Just prfEq  => Just cong prfEq

checkEqNat2 : (i:Nat2) -> (j:Nat2) -> Maybe( EqNat2 i j )
checkEqNat2 Zbit          Zbit               = Just Same Zbit
checkEqNat2 Ibit          Zbit               = Nothing
checkEqNat2 Times2 k      Zbit               = Nothing
checkEqNat2 Times2Plus1 k Zbit               = Nothing
checkEqNat2 Ibit          Ibit               = Just Same Ibit
checkEqNat2 Times2 k      Ibit               = Nothing
checkEqNat2 Times2Plus1 k Ibit               = Nothing
checkEqNat2 Times2 k      Times2 m           = case checkEqNat2 k m of
                                                    Nothing => Nothing
                                                    Just eq => Just (liftEqTimes2 _ _ eq)
checkEqNat2 Times2Plus1 k Times2 m           = Nothing
checkEqNat2 Times2Plus1 k Times2Plus1 m      = case checkEqNat2 k m of
                                                    Nothing => Nothing
                                                    Just eq => Just (liftEqTimes2Plus1 _ _ eq)

    

||| ---------------------------------------------------------------------------
||| The Isomorphism binary natural numbers to unary natural numbers
||| ---------------------------------------------------------------------------

btou : Nat2 -> Nat
btou Zbit             = Z
btou Ibit             = S Z
btou (Times2 x)       = (btou x) + (btou x)
btou (Times2Plus1 x)  = S ((btou x) + (btou x))

utob : Nat -> Nat2
utob Z = Zbit
utob (S k) = (utob k) + Ibit

||| ---------------------------------------------------------------------------
||| The proof of Isomorphism
||| ---------------------------------------------------------------------------
leftIdBU : (x:Nat2) ->  (utob (btou x)) = x 
leftIdBU Zbit = the (checkEqNat2 (utob(btou Zbit)) Zbit)  Same _

