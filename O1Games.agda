-- Time-stamp: <2020-06-09 22:48:18 pierre>
{-# OPTIONS --guardedness #-}
module O1Games where

open import Data.Sum using (_⊎_;inj₁;inj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_;refl; cong; sym)
open import Data.Nat using (ℕ; zero; suc)

data AliceBob : Set where
  Alice Bob : AliceBob

data DorR : Set where
  down right : DorR

data _≽_ : ℕ → ℕ → Set where
  z≽z : zero ≽ zero
  s≽z : {n : ℕ} → suc n ≽ zero
  s≽s : {n m : ℕ} → n ≽ m → suc n ≽ suc m

open import StrategyGame AliceBob DorR (λ (a : AliceBob) → ℕ) _≽_

open NodeS
open _≈ˢᵍ_
open _○≈ˢᵍ_
open ○↓
open ○↑
open ○☺_

--============================
-- A1B0 
--============================

-- a utility assignment
uA1B0 : AliceBob → ℕ
uA1B0 Alice = 1
uA1B0 Bob = 0

-- a leaf strategy profile 
A1B0 : StratProf
A1B0 = inj₁ uA1B0

-- convergent
↓A1B0 : ↓ A1B0
↓A1B0 = ↓Leaf

--============
-- A0B1
--============

-- a utility assignment
uA0B1 : AliceBob → ℕ
uA0B1 Alice = 0
uA0B1 Bob = 1

-- a leaf strategy profile 
A0B1 : StratProf
A0B1 = inj₁ uA0B1

-- convergent
↓A0B1 : ↓ A0B1
↓A0B1 = ↓Leaf

--===========================
-- Alice continues, Bob stops
--===========================
mutual 
  AcBs : StratProf
  AcBs = inj₂ ○AcBs

  ○AcBs : NodeS
  ag ○AcBs  = Alice
  ch ○AcBs  = right
  next ○AcBs down = A0B1
  next ○AcBs right =  BsAc
  
  BsAc : StratProf
  BsAc = inj₂ ○BsAc

  ○BsAc : NodeS
  ag ○BsAc = Bob
  ch ○BsAc = down
  next ○BsAc down = A1B0
  next ○BsAc right = AcBs

-- variant of ○AcBs
Var○AcBs : NodeS
ag Var○AcBs  = Alice
ch Var○AcBs  = down
next Var○AcBs down = A0B1
next Var○AcBs right = BsAc

-- BsAc and BsAc have the same game
mutual
  AcBs≈ˢᵍAcBs : AcBs ≈ˢᵍ AcBs
  AcBs≈ˢᵍAcBs =  _≈ˢᵍ_.≈ˢᵍNode AcBs○≈ˢᵍAcBs

  AcBs○≈ˢᵍAcBs : ○AcBs ○≈ˢᵍ ○AcBs
  is○≈ˢᵍ AcBs○≈ˢᵍAcBs refl  = ∀next₁

  ∀next₁ : (c : DorR) → next ○AcBs c ≈ˢᵍ next ○AcBs c
  ∀next₁ down =  _≈ˢᵍ_.≈ˢᵍLeaf
  ∀next₁ right = BsAc≈ˢᵍBsAc

  BsAc≈ˢᵍBsAc : BsAc ≈ˢᵍ BsAc
  BsAc≈ˢᵍBsAc = _≈ˢᵍ_.≈ˢᵍNode BsAc○≈ˢᵍBsAc

  BsAc○≈ˢᵍBsAc : ○BsAc ○≈ˢᵍ  ○BsAc
  is○≈ˢᵍ BsAc○≈ˢᵍBsAc refl = ∀next₂

  ∀next₂ : (c : DorR) → next ○BsAc c ≈ˢᵍ next ○BsAc c
  ∀next₂ down = _≈ˢᵍ_.≈ˢᵍLeaf
  ∀next₂ right = AcBs≈ˢᵍAcBs

-- AcBs and Var○AcBs have the same game
mutual
  AcBs○≈ˢᵍVar○AcBs : ○AcBs ○≈ˢᵍ Var○AcBs
  is○≈ˢᵍ AcBs○≈ˢᵍVar○AcBs refl =  ∀next₃

  ∀next₃ : (c : DorR) → next ○AcBs c ≈ˢᵍ next Var○AcBs c
  ∀next₃ down = _≈ˢᵍ_.≈ˢᵍLeaf
  ∀next₃ right =  BsAc≈ˢᵍBsAc
  
-- convergence
○↓BsAc : ○↓ ○BsAc
○↓BsAc = record {is○↓ = ↓A1B0}

↓BsAc : ↓ BsAc
↓BsAc = ↓Node ○↓BsAc

○↓AcBs : ○↓ ○AcBs
○↓AcBs = record {is○↓ = ↓BsAc}

↓AcBs : ↓ AcBs
↓AcBs = ↓Node ○↓AcBs
  
------------------------------
-- AcBs is a subgame perfect equilibrium
------------------------------
mutual 
  ⇋AcBs : ⇋ AcBs
  ⇋AcBs = ⇋Node AcBs○≈ˢᵍVar○AcBs ⇋BsAc ⇋Leaf ↓BsAc ↓Leaf s≽z
  
  ⇋BsAc : ⇋ BsAc
  ⇋BsAc = ⇋Node BsAc○≈ˢᵍBsAc ⇋Leaf ⇋Leaf ↓Leaf ↓Leaf z≽z

--===========================
-- Alice stops, Bob continues
--===========================
mutual
  AsBc : StratProf
  AsBc = inj₂ ○AsBc

  ○AsBc : NodeS
  ag ○AsBc = Alice
  ch ○AsBc = down
  next ○AsBc down = A0B1
  next ○AsBc right = BcAs

  BcAs : StratProf
  BcAs = inj₂ ○BcAs

  ○BcAs : NodeS
  ag ○BcAs = Bob
  ch ○BcAs = right
  next ○BcAs down = A1B0
  next ○BcAs right = AsBc

-- variant of ○BcAs
Var○BcAs : NodeS
ag Var○BcAs = Bob
ch Var○BcAs = down
next Var○BcAs down = A1B0
next Var○BcAs right = AsBc

-- AsBc and AsBc have the same game
mutual
  AsBc≈ˢᵍAsBc :  AsBc ≈ˢᵍ AsBc
  AsBc≈ˢᵍAsBc =  _≈ˢᵍ_.≈ˢᵍNode AsBc○≈ˢᵍAsBc

  AsBc○≈ˢᵍAsBc :  ○AsBc ○≈ˢᵍ ○AsBc
  is○≈ˢᵍ AsBc○≈ˢᵍAsBc refl = ∀next₄

  ∀next₄ : (c : DorR) → next ○AsBc c ≈ˢᵍ next ○AsBc c
  ∀next₄ down =  _≈ˢᵍ_.≈ˢᵍLeaf
  ∀next₄ right = BcAs≈ˢᵍBcAs

  BcAs≈ˢᵍBcAs : BcAs ≈ˢᵍ BcAs
  BcAs≈ˢᵍBcAs = _≈ˢᵍ_.≈ˢᵍNode BcAs○≈ˢᵍBcAs

  BcAs○≈ˢᵍBcAs : ○BcAs ○≈ˢᵍ ○BcAs
  is○≈ˢᵍ BcAs○≈ˢᵍBcAs refl = ∀next₅

  ∀next₅ : (c : DorR) → next ○BcAs c ≈ˢᵍ next ○BcAs c
  ∀next₅ down = _≈ˢᵍ_.≈ˢᵍLeaf
  ∀next₅ right = AsBc≈ˢᵍAsBc

-- BcAs and VarBcAs have the same game
∀next₆ : (c : DorR) → next ○BcAs c ≈ˢᵍ next Var○BcAs c
∀next₆ down = _≈ˢᵍ_.≈ˢᵍLeaf
∀next₆ right = AsBc≈ˢᵍAsBc

BcAs○≈ˢᵍVarBcAs :  ○BcAs ○≈ˢᵍ Var○BcAs
is○≈ˢᵍ BcAs○≈ˢᵍVarBcAs refl = ∀next₆

-- convergence
mutual
  ↓AsBc : ↓ AsBc
  ↓AsBc = ↓Node ○↓AsBc

  ○↓AsBc : ○↓ ○AsBc
  ○↓AsBc = record {is○↓ = ↓A0B1}

  ↓BcAs : ↓ BcAs
  ↓BcAs = ↓Node ○↓BcAs

  ○↓BcAs : ○↓ ○BcAs
  ○↓BcAs = record{is○↓ = ↓AsBc}

------------------------------
-- AsBc is a subgame perfect equilibrium
------------------------------
mutual
  ⇋AsBc : ⇋ AsBc
  ⇋AsBc = ⇋Node AsBc○≈ˢᵍAsBc ⇋Leaf ⇋Leaf ↓Leaf ↓Leaf z≽z

  ⇋BcAs : ⇋ BcAs
  ⇋BcAs = ⇋Node BcAs○≈ˢᵍVarBcAs ⇋AsBc ⇋Leaf ↓AsBc ↓Leaf s≽z

--==================================
-- Alice continues and Bob continues
--==================================
mutual 
  AcBc : StratProf
  AcBc = inj₂ ○AcBc

  ○AcBc : NodeS
  ag ○AcBc  = Alice
  ch ○AcBc  = right
  next ○AcBc down = A0B1
  next ○AcBc right =  BcAc
  
  BcAc : StratProf
  BcAc = inj₂  ○BcAc

  ○BcAc : NodeS
  ag ○BcAc = Bob
  ch ○BcAc = right
  next ○BcAc down = A1B0
  next ○BcAc right = AcBc

-- AcBc and AsBc have he same game
mutual
  AcBc≈ˢᵍAsBc :  AcBc ≈ˢᵍ AsBc
  AcBc≈ˢᵍAsBc =  _≈ˢᵍ_.≈ˢᵍNode AcBc○≈ˢᵍAsBc

  AcBc○≈ˢᵍAsBc :  ○AcBc ○≈ˢᵍ ○AsBc
  is○≈ˢᵍ AcBc○≈ˢᵍAsBc refl = ∀next₇

  ∀next₇ :  (c : DorR) → next ○AcBc c ≈ˢᵍ next ○AsBc c
  ∀next₇ down =  _≈ˢᵍ_.≈ˢᵍLeaf
  ∀next₇ right = BcAc≈ˢᵍBcAs

  BcAc≈ˢᵍBcAs : BcAc ≈ˢᵍ BcAs
  BcAc≈ˢᵍBcAs =  _≈ˢᵍ_.≈ˢᵍNode BcAc○≈ˢᵍBcAs

  BcAc○≈ˢᵍBcAs : ○BcAc ○≈ˢᵍ ○BcAs
  is○≈ˢᵍ BcAc○≈ˢᵍBcAs refl = ∀next₈

  ∀next₈ : (c : DorR) → next ○BcAc c ≈ˢᵍ next ○BcAs c
  ∀next₈ down =  _≈ˢᵍ_.≈ˢᵍLeaf
  ∀next₈ right = AcBc≈ˢᵍAsBc

-- AcBc and AcBs have he same game
mutual
  AcBc≈ˢᵍAcBs :  AcBc ≈ˢᵍ AcBs
  AcBc≈ˢᵍAcBs =  _≈ˢᵍ_.≈ˢᵍNode AcBc○≈ˢᵍAcBs

  AcBc○≈ˢᵍAcBs :  ○AcBc ○≈ˢᵍ ○AcBs
  is○≈ˢᵍ AcBc○≈ˢᵍAcBs refl = ∀next₉

  ∀next₉ :  (c : DorR) → next ○AcBc c ≈ˢᵍ next ○AcBs c
  ∀next₉ down =  _≈ˢᵍ_.≈ˢᵍLeaf
  ∀next₉ right = BcAc≈ˢᵍBsAc

  BcAc≈ˢᵍBsAc : BcAc ≈ˢᵍ BsAc
  BcAc≈ˢᵍBsAc =  _≈ˢᵍ_.≈ˢᵍNode BcAc○≈ˢᵍBsAc

  BcAc○≈ˢᵍBsAc : ○BcAc ○≈ˢᵍ ○BsAc
  is○≈ˢᵍ BcAc○≈ˢᵍBsAc refl = ∀next₁₀

  ∀next₁₀ : (c : DorR) → next ○BcAc c ≈ˢᵍ next ○BsAc c
  ∀next₁₀ down =  _≈ˢᵍ_.≈ˢᵍLeaf
  ∀next₁₀ right = AcBc≈ˢᵍAcBs

--------------------
-- AcBc is divergent
--------------------
mutual
  ↑AcBc : ↑ AcBc
  ↑AcBc = ↑Node ↑○AcBc

  ↑○AcBc : ○↑ ○AcBc
  is○↑ ↑○AcBc = ↑BcAc

  ↑BcAc : ↑ BcAc
  ↑BcAc = ↑Node ↑○BcAc

  ↑○BcAc : ○↑ ○BcAc
  is○↑ ↑○BcAc = ↑AcBc

--------------------
-- AcBc is good
--------------------
ch○AcBc≡ch○AcBs : ch ○AcBc ≡ ch ○AcBs
ch○AcBc≡ch○AcBs = refl

ch○BcAc≡ch○BcAs : ch ○BcAc ≡ ch ○BcAs
ch○BcAc≡ch○BcAs = refl

mutual
  ☺AcBc : ☺ AcBc
  ☺AcBc = ☺Node ☺○AcBc

  ☺○AcBc : ○☺ ○AcBc
  is○☺ ☺○AcBc ○AcBs ⇋AcBs AcBc≈ˢᵍAcBs ch○AcBc≡ch○AcBs = ☺BcAc

  ☺BcAc : ☺ BcAc
  ☺BcAc = ☺Node ☺○BcAc

  ☺○BcAc : ○☺ ○BcAc
  is○☺ ☺○BcAc ○BcAs ⇋BcAs BcAc≈ˢᵍBcAs ch○BcAc≡ch○BcAs = ☺AcBc
