module AgdaDemo where 

data Bool : Set where 
  true : Bool
  false : Bool


-- C-c C-l load the file
-- C-c C-n evaluate the expression
-- C-c C-d type of expression
-- C-c C-f forward to next goal
-- C-c C-b back to previous goal
-- C-c C-t type of current goal
-- C-c C-c case split current goal

¬ : Bool → Bool
¬ true = false
¬ false = true

_^_ : Bool → Bool → Bool
true ^ y = y
false ^ y = false

data ℕ : Set where 
  zero : ℕ 
  suc : ℕ → ℕ 

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}


_⊹_ : ℕ → ℕ → ℕ 
zero ⊹ y = y
suc x ⊹ y = suc (x ⊹ y)

_==_ : ℕ → ℕ → Bool
zero == zero = true
zero == suc y = false
suc x == zero = false
suc x == suc y = x == y 

infixr 5 _::_ 

data List ( A : Set ) : Set where 
  [] : List A
  _::_ : A → List A → List A 

_++_ : ∀ { A } → List A → List A → List A 
[] ++ ys = ys
(x :: xs) ++ ys = x :: xs ++ ys

infixr 5 _:::_ 

data List# ( A : Set ) : ℕ → Set where
  [] : List# A 0
  _:::_ : ∀ { n } → A → List# A n → List# A ( n ⊹ 1 ) 

_+++_ : ∀ { A m n } → List# A m → List# A n → List# A ( m ⊹ n )
[] +++ ys = ys
(x ::: xs) +++ ys = {!x ::: ( xs +++ ys )!}



_<_ : ℕ → ℕ → Bool
zero < zero = false
zero < suc y = true
suc x < zero = false
suc x < suc y = x < y
  

data [_] : Bool → Set where 
  ok : [ true ]
  
test₁ : [ ¬ ( 1 < 1 ) ]
test₁ = ok 

<asym : ∀ X → [ ¬ ( X < X ) ]
<asym zero = ok
<asym ( suc y ) = <asym y


data Maybe ( A : Set ) : Set where 
  nothing : Maybe A
  just : A → Maybe A

_==?_ : Maybe ℕ → Maybe ℕ → Bool
nothing ==? nothing = true
nothing ==? just x = false
just x ==? nothing = false
just x ==? just y = x == y 

index? : ∀ { A } → List A → ℕ → Maybe A
index? [] n = nothing
index?  (x :: xs) zero = just x
index?  (x :: xs) (suc n) = index? xs n

test₂ : [ index? ( 1 :: 2 :: 3 :: 4 :: [] ) 2 ==? just 3 ]
test₂ = ok

test₃ : [ index? ( 1 :: 2 :: 3 :: 4 :: [] ) 6 ==? nothing ]
test₃ = ok

index : ∀ { A m } → List# A m → ∀ n → [ n < m ] → A
index [] n n<m = {!n<m!}
index (x ::: xs) zero n<m = x
index (x ::: xs) (suc y) n<m = {!index xs y n<m!}
