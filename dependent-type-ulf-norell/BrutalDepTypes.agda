module BrutalDepTypes where 

module ThrowAwayIntroduction where 

data Bool : Set where 
  true : Bool 
  false : Bool 

data ℕ : Set where 
  zero : ℕ 
  suc : ℕ → ℕ 

data Id  ( A : Set ) :  Set where 
  pack : A → Id A 

