open import Data.Nat
open import Data.Fin
open import Data.List using (List)
open import Data.Product
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Vec using (Vec; lookup; allFin)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.All using (All; []; _∷_) renaming (lookup to lookupA)
open import Data.Vec.All renaming (All to AllV ; lookup to lookupV)
open import Data.Vec.Properties using (lookup-allFin)
open import Relation.Binary.PropositionalEquality using (sym)

module itfj (n : ℕ) where

  Ty = Fin n

  Ctx : Set
  Ctx = List Ty

  module ClassTable where

    record MSig : Set where
      constructor mkMSig
      field
        ret    : Ty
        params : List Ty

    record CSig : Set where
      constructor mkCSig
      field
        flds  : List Ty
        signs : List MSig

    CTSig : Set
    CTSig = Vec CSig n

  open ClassTable

  module Auxiliary (Δ : CTSig) where

    fields : Ty → List Ty
    fields τ = CSig.flds (lookup Δ τ)

    signatures : Ty → List MSig
    signatures τ = CSig.signs (lookup Δ τ)

  open ClassTable

  module Syntax (Δ : CTSig) where

    open Auxiliary Δ

    data Expr (Γ : Ctx) : Ty → Set where
      Var   : ∀ {x}   → x ∈ Γ → Expr Γ x
      Field : ∀ {c f} → Expr Γ c → f ∈ (fields c) → Expr Γ f
      Invk  : ∀ {c m} → Expr Γ c → m ∈ (signatures c)
           → All (Expr Γ) (MSig.params m) → Expr Γ (MSig.ret m)
      New   : ∀ c   → All (Expr Γ) (fields c) → Expr Γ c

    data Val : Ty → Set where
      V-New : ∀ c → All Val (fields c) → Val c

  module Implementation (Δ : CTSig) where

    open Syntax Δ
    open Auxiliary Δ

    record MImpl (s : MSig) : Set where
      field
        body : Expr (MSig.params s) (MSig.ret s)

    record CImpl (τ : Ty) : Set where
      field
        impls : All MImpl (CSig.signs (lookup Δ τ))

    CTImpl : Set
    CTImpl = AllV CImpl (allFin n)

    implementations : (τ : Ty) → CTImpl → All MImpl (signatures τ)
    implementations τ δ rewrite sym (lookup-allFin τ) = CImpl.impls (lookupV τ δ)

  module Eval (Δ : CTSig) where

    open Syntax Δ
    open Implementation Δ

    Fuel = ℕ

    Env : Ctx → Set
    Env Γ = All Val Γ

    eval : ∀ {Γ c} → Fuel → CTImpl → Env Γ → Expr Γ c → Maybe (Val c)
    eval-list : ∀ {Γ cs} → Fuel → CTImpl → Env Γ → All (Expr Γ) cs → Maybe (All Val cs)

    eval zero δ γ e = nothing
    eval (suc f) δ γ (Var x) = just (lookupA γ x)
    eval (suc f) δ γ (Field e x) with eval f δ γ e
    ... | nothing = nothing
    ... | just (V-New c cp) = just (lookupA cp x)
    eval (suc f) δ γ (Invk e m mp) with eval f δ γ e
    ... | nothing = nothing
    ... | just (V-New c cp) with eval-list f δ γ mp
    ...   | nothing = nothing
    ...   | just mp' = let mi = lookupA (implementations c δ) m
                         in eval f δ mp' (MImpl.body mi)
    eval (suc f) δ γ (New c cp) with eval-list f δ γ cp
    ... | nothing = nothing
    ... | just cp' = just (V-New c cp')

    eval-list zero δ γ es = nothing
    eval-list (suc f) δ γ [] = just []
    eval-list (suc f) δ γ (e ∷ es) with eval f δ γ e
    ... | nothing = nothing
    ... | just v with eval-list f δ γ es
    ...   | nothing = nothing
    ...   | just vs = just (v ∷ vs)
