-- Time-stamp: <2020-06-09 22:48:31 pierre>
{-# OPTIONS --guardedness #-}

module StrategyGame (Agent : Set) (Choice : Set) (Utility : Agent → Set) (_≮_ : ∀ {a : Agent} → Utility a → Utility a → Set) where

open import Data.Bool using (Bool; true; false)
open import Data.Sum using (_⊎_;[_,_];inj₁;inj₂)
open import Data.Product using (_×_;_,_;proj₁;proj₂)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_;_≢_;refl; cong; sym)

mutual
  Game = ((a : Agent) → Utility a) ⊎ NodeG

  record NodeG : Set where
    coinductive
    field
      ag : Agent
      next : Choice → Game

mutual
  StratProf = ((a : Agent) → Utility a) ⊎ NodeS

  record NodeS : Set where
    coinductive
    field
      ag : Agent
      next : Choice → StratProf
      ch : Choice

open NodeS

game : (s : StratProf) → Game
game (inj₁ u) = inj₁ u
game (inj₂ n) = inj₂ (gameN n) where
  gameN : NodeS → NodeG
  NodeG.ag (gameN n) = ag n
  NodeG.next (gameN n) c = game (next n c)

-- s ≈ˢᵍ s' means that s and s' have the 'same game'.  They are bissimilar upto choices
mutual
  data _≈ˢᵍ_ : StratProf → StratProf → Set where
    ≈ˢᵍLeaf : {u : (a : Agent) → Utility a} → inj₁ u ≈ˢᵍ inj₁ u
    ≈ˢᵍNode : {n n' : NodeS} → n ○≈ˢᵍ n' → inj₂ n ≈ˢᵍ inj₂ n'

  record _○≈ˢᵍ_ (n n' : NodeS) : Set where
    coinductive
    field
      is○≈ˢᵍ : ag n ≡ ag n' → ((c : Choice) → next n c ≈ˢᵍ next n' c)

-- Convergent
mutual
  data ↓ : StratProf → Set where
    ↓Leaf : {u : (a : Agent) → Utility a} → ↓ (inj₁ u)
    ↓Node : {n : NodeS} → ○↓ n → ↓ (inj₂ n)

  record ○↓ (n : NodeS) : Set where
    inductive
    field
      is○↓ : ↓ (next n (ch n))

open ○↓

-- Divergent 
mutual
  data ↑_ : StratProf → Set where
    ↑Node :  {n : NodeS} → ○↑ n → ↑ (inj₂ n)

  record ○↑ (n : NodeS) : Set where
    coinductive
    field
      is○↑ : ↑ (next n (ch n))

open ○↑

-- Utility assignment
mutual
  υ : (s : StratProf) → (↓ s) → (a : Agent) → Utility a
  υ (inj₁ u) ↓Leaf = u
  υ (inj₂ n) (↓Node p) = ○υ n p

  ○υ : (n : NodeS) → (○↓ n)  → (a : Agent) → Utility a
  ○υ n p = υ (next n (ch n)) (is○↓ p)


-- Subgame perfect equilibrium
data ⇋_ : StratProf → Set where
  ⇋Leaf : {u : (a : Agent) → Utility a} → ⇋ inj₁ u
  ⇋Node : {n n' : NodeS} →
    n ○≈ˢᵍ n' →
     ⇋ (next n (ch n)) →
     ⇋ (next n' (ch n')) →
    (p : ↓ (next n (ch n))) → (p' : ↓ (next n' (ch n'))) →
    (υ (next n (ch n)) p (ag n)) ≮ (υ (next n' (ch n')) p' (ag n)) →
     ⇋ inj₂ n

-- Good StratProf, i.e.,
-- exists an equilibrium, with same game and same choice
mutual
  data ☺_ : (s : StratProf) → Set where
    ☺Node :  {n : NodeS} → ○☺ n → ☺ (inj₂ n)
  record ○☺_ (n : NodeS) : Set where
    coinductive
    field
      is○☺ : (n' : NodeS) → ⇋ (inj₂ n') → n ○≈ˢᵍ n' → ch n ≡ ch n' →
        ☺ (next n (ch n))
