module Interpreter where 

open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.Product 
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


infix 3 _≤E_
infix 4 _⊹E_


data Expr : Set where 
  nat : ℕ → Expr
  bool : Bool → Expr 
  _⊹E_ : Expr → Expr → Expr 
  _≤E_ : Expr → Expr → Expr 
  ifE_then_else_ : Expr → Expr → Expr → Expr 
  

e1 : Expr -- if 3 ≤ 4 then 4 + 1 else 0
e1 = ifE (nat 3) ≤E (nat 4) then (nat 4) ⊹E (nat 1) else (nat 0)

e2 : Expr -- 3 ≤ 4 + 5
e2 = (nat 3) ≤E (nat 4) ⊹E (nat 5)

e3 : Expr -- (3 ≤ 4) + 5
e3 = ((nat 3) ≤E (nat 4)) ⊹E (nat 5)


data Val : Set where 
  nat : ℕ → Val
  bool : Bool → Val 

return : { A : Set } → A → Maybe A 
return a = just a 

infix 2 _>>=_ 

_>>=_ : { A B : Set } → Maybe A → ( A → Maybe B ) → Maybe B 
just a >>= f = f a 
nothing >>= f = nothing 

_⊹v_ : Val → Val → Maybe Val 
nat m ⊹v nat n = return ( nat ( m + n ) )
_ ⊹v _ = nothing 

dec2bool : { A : Set } → Dec A → Bool
dec2bool ( yes p ) = true 
dec2bool ( no ¬p ) = false 

_≤v_ : Val → Val → Maybe Val
nat m ≤v nat n = return ( bool ( dec2bool ( m ≤? n ) ) )
_ ≤v _ =  nothing 


ifV_then_else_ : Val → Val → Val → Maybe Val
ifV bool b then v else v' = return ( if b then v else v' )
ifV _ then _ else _ = nothing 


eval : Expr → Maybe Val
eval ( nat n ) = return ( nat n )
eval ( bool b ) = return ( bool b ) 
eval ( e ⊹E e' ) = eval e >>= λ v → 
                   eval e' >>= λ v' → 
                    v ⊹v v' 
eval ( e ≤E e' ) = eval e >>= λ v →
                   eval e' >>= λ v' → 
                    v ≤v v'
eval ( ifE e then e' else e'' ) = eval e >>= λ v → 
                                  eval e' >>= λ v' → 
                                  eval e'' >>= λ v'' →
                                  ifV v then v' else v''


data Ty : Set where 
  nat : Ty
  bool : Ty 

data TVal : Ty → Set where 
  nat : ℕ → TVal nat
  bool : Bool → TVal bool

data TExpr : Ty → Set where 
  nat : ℕ → TExpr nat
  bool : Bool → TExpr bool
  _⊹E_ : TExpr nat → TExpr nat → TExpr nat
  _≤E_ : TExpr nat → TExpr nat → TExpr bool 
  ifE_then_else_ : { σ : Ty } → TExpr bool → TExpr σ → TExpr σ → TExpr σ 


evalT : { σ : Ty } → TExpr σ → TVal σ 
evalT ( nat n ) = nat n 
evalT ( bool b ) = bool b 
evalT ( e ⊹E e' ) with evalT e | evalT e' 
...                 | nat m | nat n = nat ( m + n ) 
evalT ( e ≤E e' ) with evalT e | evalT e' 
...                 | nat m | nat n = bool ( dec2bool ( m ≤? n ) )
evalT ( ifE e then e' else e'' ) with evalT e 
...                 | bool b = if b then evalT e' else evalT e''  

