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

||| THIS DOES NOT, I suspect it is implict convertion to integers at fault.
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

invPrfNat : (x:MyNat) -> cyc012 ( cyc021 x ) = x
invPrfNat Z = Refl
