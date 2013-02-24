module Basic where 

data Bool : Set where 
  true : Bool
  false : Bool

not : Bool → Bool 
not true = false 
not false = true 

or : Bool → Bool → Bool
or false false = false 
or _ _ = true 

and : Bool → Bool → Bool
and true true = true 
and _ _ = false  

data ℕ  : Set where 
   zero : ℕ
   suc : ℕ → ℕ
   
_+_ : ℕ → ℕ → ℕ
zero + m = m 
suc n + m = suc ( n + m ) 

_⋆_ : ℕ → ℕ → ℕ 
zero ⋆ m = zero 
suc n ⋆ m =   ( n ⋆ m ) + m 


fold-ℕ : ℕ → ( ℕ → ℕ ) → ℕ → ℕ 
fold-ℕ u _ zero = u   
fold-ℕ u f ( suc n ) = f ( fold-ℕ u f n )

if_then_else_ : { A : Set } → Bool → A → A → A  
if true then x else y = x 
if false then x else y = y 

data List ( A : Set ) : Set where 
  [] : List A 
  _::_ : A → List A -> List A 


identity : ( A : Set ) → A → A 
identity A x = x 

zero′ : ℕ
zero′ = identity ℕ zero

apply : ( A : Set ) ( B : A → Set ) → ( ( x : A ) → B x ) → ( a : A ) → B a 
apply A B f a = f a 

identity₂ : ( A : Set ) → A → A 
identity₂ = \A x → x 

identity₃ : ( A : Set ) → A → A 
identity₃ = \(A : Set ) ( x : A ) → x 

identity₄ : ( A : Set ) → A → A 
identity₄ = \ ( A : Set ) x → x 

id : { A : Set } → A → A 
id x = x 

true′ : Bool
true′ = id true 

one : ℕ
one = identity _ ( suc zero ) 

_∘_ : { A : Set } { B : A → Set } { C : ( x : A ) → B x → Set } 
      ( f : { x : A } ( y : B x ) → C x y ) ( g : ( x : A ) → B x ) ( x : A ) 
       → C x ( g x )
( f ∘ g ) x = f ( g x ) 

plus-two = suc ∘  suc 
plus-three = suc ∘ ( suc ∘ suc ) 

map : { A B : Set } → ( A → B ) → List A → List B 
map f [] = []  
map f ( x :: xs ) = f x :: map f xs 

_++_ : { A : Set } → List A → List A → List A
[] ++ ys = ys 
( x :: xs ) ++ ys = x :: ( xs ++ ys ) 


foldl : { A B : Set } → ( A → B → A ) → A → List B → A 
foldl f val [] = val 
foldl f val ( x :: xs ) = foldl f ( f val x ) xs 

foldr : { A B : Set } → ( A → B → B ) → B → List A → B
foldr f val [] = val 
foldr f val ( x :: xs ) = f x ( foldr f val xs ) 

--type of Vec A is  ℕ → Set. This mean Vec A is family of types indexed by 
-- natural numbers
 
data Vec ( A : Set ) : ℕ →  Set where 
  [] : Vec A zero 
  _::_ : { n : ℕ } → A → Vec A n → Vec A ( suc n ) 


head : { A : Set } { n : ℕ } → Vec A ( suc n )  → A 
head ( x :: xs ) = x 

vmap : { A B : Set } { n : ℕ } → ( A → B ) → Vec A n → Vec B n 
vmap f [] = []
vmap f ( x :: xs ) = f x :: vmap f xs 

data Vec₂ ( A : Set ) : ℕ → Set where 
   nil : Vec₂ A zero 
   cons : ( n : ℕ ) → A → Vec₂ A n → Vec₂ A ( suc n ) 
{--
The rule for when an argument should be dotted is:
if there is a unique
type correct value for the argument it should be dotted
--}

vmap₂ : { A B : Set } ( n : ℕ ) → ( A → B ) → Vec₂ A n → Vec₂ B n 
vmap₂ .zero f nil = nil 
vmap₂ .( suc n ) f ( cons n x xs ) = cons n  ( f x ) ( vmap₂ n f xs )  

vmap₃ : { A B : Set } ( n : ℕ ) → ( A → B ) → Vec₂ A n → Vec₂ B n 
vmap₃ zero f nil = nil 
vmap₃ ( suc n ) f ( cons .n x xs ) = cons n ( f x ) ( vmap₃ n f xs )

pow : ℕ →  ℕ  →  ℕ  
pow _  zero = suc zero 
pow a ( suc n ) =  a ⋆ pow a n  

t : ℕ
t = pow ( suc ( suc  zero ) ) ( suc ( suc ( suc zero ) ) ) 

data Image_∋_ { A B : Set } ( f : A → B ) : B → Set where 
   im : ( x : A ) → Image f ∋ f x 

inv : { A B : Set } ( f : A → B ) ( y : B ) → Image f ∋ y → A 
inv f .( f x ) ( im x ) = x 

data Fin : ℕ → Set where 
  fzero : { n : ℕ } → Fin ( suc n )
  fsuc  : { n : ℕ } → Fin n → Fin ( suc n )

magic : { A : Set } → Fin zero → A 
magic ()

data Empty : Set where 
  empty : Fin zero → Empty

magic′ : { A : Set } → Empty → A 
magic′ ( empty () ) 

_!_ : { n : ℕ }{ A : Set } → Vec A n → Fin n → A 
[] ! () 
( x :: xs ) ! fzero = x 
( x :: xs ) ! ( fsuc i ) = xs ! i 

data False : Set where 
record True : Set where 

trivial : True 
trivial = _ 

isTrue : Bool → Set 
isTrue true = True
isTrue false = False

_<_ : ℕ → ℕ → Bool
_ < zero = false 
zero < suc n = true 
suc m < suc n = m < n 

length : { A : Set } → List A → ℕ
length [] = zero 
length ( x :: xs ) = suc ( length xs )

lookup : { A : Set } ( xs : List A ) ( n : ℕ ) → isTrue ( n < length xs ) → A 
lookup [] n () 
lookup ( x :: xs ) zero  p = x 
lookup ( x :: xs ) ( suc n ) p = lookup xs n p 

{--
For a type A and an element x of A
, we define the the family of proofs
of “being equal to x ”. This family is only inhabited at index
x where the single proof is refl

for understanding the constuctor 
data == { A : Set } ( x : A ) : A → Set where 
   refl : ( == ) x x 
­-}

data _≡_ { A : Set } ( x : A ) : A → Set where 
  refl : x ≡ x 

data _≤_ : ℕ → ℕ → Set where 
   leq-zero : { n : ℕ } → zero ≤ n 
   leq-suc : { m n : ℕ } → m ≤ n → suc m ≤ suc n 

leq-trans : { l m n : ℕ } → l ≤ m → m ≤ n → l ≤ n 
leq-trans leq-zero _ = leq-zero 
leq-trans ( leq-suc p ) ( leq-suc q ) = leq-suc ( leq-trans p q )

min : ℕ → ℕ → ℕ
min x y with x < y 
...| true = x 
...| false = y 

filter : { A : Set } → ( ( x : A )  → Bool ) → List A → List A
filter p [] = []
filter p ( x :: xs ) with p x 
... | true = x :: filter p xs 
... | false = filter p xs 

data _≠_ : ℕ → ℕ → Set where 
  z≠s : { n : ℕ } → zero ≠ suc n 
  s≠z : { n : ℕ } → suc n ≠ zero 
  s≠s : { m n : ℕ } → m ≠ n → suc m ≠ suc n  

data Equal? ( n m : ℕ ) : Set where 
  eq : n ≡ m → Equal? n m 
  neq : n ≠ m → Equal? n m   


halve : ℕ → ℕ 
halve zero = zero 
halve ( suc zero ) = zero
halve ( suc ( suc n ) ) = suc ( halve n )

