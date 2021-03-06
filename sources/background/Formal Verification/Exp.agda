open import Data.Nat using (ℕ) renaming (_+_ to _⊕_)
open import Data.Bool using (Bool ; true ; false) renaming (_∧_ to _&&_)

module Exp where

-- Common stuff

data Ty : Set where
  TBool TNum : Ty

-- Extrinsically typed formalization

module EExp where

-- Syntax definition

  data Expr : Set where
    BTrue BFalse  : Expr
    Num           : ℕ → Expr
    _+_ _∧_       : Expr → Expr → Expr

-- Value definition

  data Val : Expr → Set where
    VTrue  : Val BTrue
    VFalse : Val BFalse
    VNum   : ∀ {n} → Val (Num n)

-- Small-step relation

  infix 4 _⟶_
  data _⟶_ : Expr → Expr → Set where
    S-Add₁ : ∀ {e₁ e₁' e₂}
           → e₁ ⟶ e₁'
           → e₁ + e₂ ⟶ e₁' + e₂
    S-Add₂ : ∀ {v₁ e₂ e₂'}
          → Val v₁
          → e₂ ⟶ e₂'
          → v₁ + e₂ ⟶ v₁ + e₂'
    S-Add  : ∀ {n₁ n₂}
          → Val (Num n₁)
          → Val (Num n₂)
          → (Num n₁) + (Num n₂) ⟶ Num (n₁ ⊕ n₂)
    S-And₁ : ∀ {e₁ e₁' e₂}
          → e₁ ⟶ e₁'
          → e₁ ∧ e₂ ⟶ e₁' ∧ e₂
    S-And₂ : ∀ {e₂}
          → Val BTrue
          → BTrue ∧ e₂ ⟶ e₂
    S-And₃ : ∀ {e₂}
          → Val BFalse
          → BFalse ∧ e₂ ⟶ BFalse

  -- Typing

  data ⊢_∶_ : Expr → Ty → Set where
    T-True  : ⊢ BTrue ∶ TBool
    T-False : ⊢ BFalse ∶ TBool
    T-Num   : ∀ {n} → ⊢ Num n ∶ TNum
    T-Add   : ∀ {e₁ e₂}
            → ⊢ e₁ ∶ TNum
            → ⊢ e₂ ∶ TNum
            → ⊢ e₁ + e₂ ∶ TNum
    T-And   : ∀ {e₁ e₂}
            → ⊢ e₁ ∶ TBool
            → ⊢ e₂ ∶ TBool
            → ⊢ e₁ ∧ e₂ ∶ TBool

-- Properties

  data Canonical : Expr → Ty → Set where
    C-True  : Canonical BTrue TBool
    C-False : Canonical BFalse TBool
    C-Num   : ∀ {n} → Canonical (Num n) TNum

  canonical : ∀ {v τ} → ⊢ v ∶ τ → Val v → Canonical v τ
  canonical T-True _ = C-True
  canonical T-False _ = C-False
  canonical T-Num _ = C-Num

  data Progress (e : Expr) : Set where
    Step : ∀ {e'}
        → e ⟶ e'
        → Progress e
    Done : Val e
        → Progress e

  progress : ∀ {e τ} → ⊢ e ∶ τ → Progress e
  progress T-True = Done VTrue
  progress T-False = Done VFalse
  progress T-Num = Done VNum
  progress (T-Add e₁ e₂) with progress e₁
  ... | Step stp₁ = Step (S-Add₁ stp₁)
  ... | Done v₁ with progress e₂
  ...   | Step stp₂ = Step (S-Add₂ v₁ stp₂)
  ...   | Done v₂ with canonical e₁ v₁ | canonical e₂ v₂
  ...     | C-Num | C-Num = Step (S-Add v₁ v₂)
  progress (T-And e₁ e₂) with progress e₁
  ... | Step stp₁ = Step (S-And₁ stp₁)
  ... | Done v₁ with canonical e₁ v₁
  ...   | C-True = Step (S-And₂ v₁)
  ...   | C-False = Step (S-And₃ v₁)

  preservation : ∀ {e e' τ} → ⊢ e ∶ τ → e ⟶ e' → ⊢ e' ∶ τ
  preservation (T-Add r₁ r₂) (S-Add₁ stp) = T-Add (preservation r₁ stp) r₂
  preservation (T-Add r₁ r₂) (S-Add₂ v₁ stp) = T-Add r₁ (preservation r₂ stp)
  preservation (T-Add r₁ r₂) (S-Add v₁ v₂) = T-Num
  preservation (T-And r₁ r₂) (S-And₁ stp) = T-And (preservation r₁ stp) r₂
  preservation (T-And r₁ r₂) (S-And₂ v₁) = r₂
  preservation (T-And r₁ r₂) (S-And₃ v₁) = r₁

-- Intrinsically typed formalization

module IExp where

-- Intrinsically-typed syntax

  data Expr : Ty → Set where
    BTrue  : Expr TBool
    BFalse : Expr TBool
    Num    : ℕ → Expr TNum
    Add    : Expr TNum → Expr TNum → Expr TNum
    And    : Expr TBool → Expr TBool → Expr TBool

-- Definition of values

  Val : Ty → Set
  Val TBool = Bool
  Val TNum = ℕ

-- Definitional interpreter

  eval : ∀ {τ} → Expr τ → Val τ
  eval BTrue = true
  eval BFalse = false
  eval (Num x) = x
  eval (Add e₁ e₂) = eval e₁ ⊕ eval e₂
  eval (And e₁ e₂) = eval e₁ && eval e₂
