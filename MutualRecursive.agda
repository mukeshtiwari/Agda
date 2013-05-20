module MutualRecursive where


data Bool : Set where
  true : Bool
  false : Bool

data ℕ : Set where 
  zero : ℕ
  succ : ℕ → ℕ 

data ℕ⁺ : Set where
  one : ℕ⁺ 
  double : ℕ⁺ → ℕ⁺
  double⁺¹ : ℕ⁺ → ℕ⁺


add : ℕ⁺ → ℕ⁺ → ℕ⁺ 
add one one = double one
add one ( double x ) = double⁺¹ x
add one ( double⁺¹ x ) = double ( add x one )
add ( double x ) one =  double⁺¹ x
add ( double x ) ( double y ) = double ( add x y )
add ( double x ) (  double⁺¹ y ) =  double⁺¹ (  add x y )
add (  double⁺¹ x ) one =   double (  add x one )
add (  double⁺¹ x ) (  double y ) =  double⁺¹ (  add x y  )
add (  double⁺¹ x ) (  double⁺¹ y ) = double ( add (  add x y ) one )


mult : ℕ⁺ → ℕ⁺ → ℕ⁺
mult x one = x
mult x ( double y ) = double ( mult x y )
mult x ( double⁺¹ y ) = add x ( double ( mult x y ) )


pow : ℕ⁺ → ℕ⁺ → ℕ⁺
pow one _ = one
pow x  one =  x
pow x ( double one ) = mult x x
pow x ( double y ) =  pow ( pow x y ) ( double one )
pow x ( double⁺¹ y ) =  mult x ( pow ( pow x y ) ( double one ) ) 




