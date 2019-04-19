{-
(+) : Nat -> Nat -> Nat
     Z + y = y
(S k) + y = S(k+y)
 -}
 
 total
ascLaw : (a:Nat) -> (b:Nat) -> (c:Nat) -> (a + (b+c)) = ((a+b)+c)
{-  normal form of LHS: Z+(Z+c) = Z+c = c; 
    Normal form of RHS: (Z+Z)+c = Z+c=c;
   so {c=c}=Refl proves it. -}
ascLaw Z Z c = Refl
 
{-LHS:  Z + ((S k)+ c) = Z+( S( k+c))=Z+(S (k+c)) = S (k+c), 
    RHS: (Z+(S k)) + c = (S k)+c = S(k+c).  Again Refl. -}
ascLaw Z (S k) c = Refl
 
{- So now we have covered Z+(b + c) = (Z+b)+c, now change Z to S j -}
{-  normal form of LHS: (S j)+(b+c) = S(j +(b+c)); 
     normal form of RHS: ((S j)+b)+c = S(j+b) +c= S ( (j+b)+c);
    NOT THE SAME, but we can induct on j+(b+c)=(j+b)+c and then
    Apply S to both sides. Applying S to both side of  and equation is 
    Done by “cong”  -}
ascLaw (S j) b c = cong (ascLaw j b c)


total cmLaw : (a:Nat) -> (b:Nat) -> (a+b) = (b+a)
cmLaw Z Z = Refl
cmLaw Z (S k) = cong {f=S} (left_id k) where
    left_id : (j:Nat) -> j = j+0
    left_id Z = Refl
    left_id (S d) = cong {f=S} (left_id d)
cmLaw (S j) b = rewrite sucMove b j in cong {f=S} (cmLaw j b) where
    sucMove : (j:Nat) -> (k:Nat) -> j + (S k) = S(j+k)
    sucMove Z k = Refl
    sucMove (S j) k = cong {f=S} (sucMove j k)
    
