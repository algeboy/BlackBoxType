||| THIS WORKS 
data MyNat = A | Next MyNat

cycABC: MyNat -> MyNat
cycABC A                    = Next A 
cycABC (Next A)             = Next (Next A) 
cycABC (Next(Next A))       = A
cycABC (Next(Next(Next x))) = Next(Next(Next x))

cycACB: MyNat -> MyNat
cycACB A                    = Next(Next A)
cycACB (Next A)             = A
cycACB (Next(Next A))       = Next A
cycACB (Next(Next(Next x))) = Next(Next(Next x))

invPrfMyNat : (x:MyNat) -> cycABC ( cycACB x ) = x
invPrfMyNat A = Refl

||| THIS WORKS
cyc012: Nat -> Nat
cyc012 Z                    = S Z 
cyc012 (S Z)                = S (S Z) 
cyc012 (S(S Z))             = Z
cyc012 (S(S(S x)))          = S(S(S x))

cyc021: Nat -> Nat
cyc021 Z                    = S(S Z)
cyc021 (S Z)                = Z
cyc021 (S(S Z))             = S Z
cyc021 (S(S(S x)))          = S(S(S x))

invPrfNat : (x:Nat) -> cyc012 ( cyc021 x ) = x
invPrfNat Z = Refl

||| Map between

abc120: MyNat -> Nat
abc120 A                    = S Z 
abc120 (Next A)             = S (S Z) 
abc120 (Next(Next A))       = Z
abc120 (Next(Next(Next x))) = S(S(S (abc120 x)))

iabc120: Nat -> MyNat
iabc120 Z                    = Next(Next A) 
iabc120 (S Z)                = A
iabc120 (S(S Z))             = Next A
iabc120 (S(S(S x)))          = Next(Next(Next (iabc120 x)))

invPrfNat : (x:MyNat) -> iabc120 ( abc120 x ) = x
invPrfNat A = Refl

||| THIS DOES WORK, how unexpected.
cyc01: Nat -> Nat
cyc01 Z                    = S Z 
cyc01 (S Z)                = Z
cyc01 (S(S x))             = S(S(x))

invPrfNat2 : (x:Nat) -> cyc01 ( cyc01 x ) = x
invPrfNat2 Z = Refl

