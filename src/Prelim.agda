{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --hidden-argument-puns #-}

module Prelim where

open import Cubical.Foundations.Prelude public
  using (Type; Level; Lift) renaming (ℓ-zero to 𝓊₀; ℓ-suc to _⁺; ℓ-max to _⊔_)
𝓊₁ = 𝓊₀ ⁺
𝓊₂ = 𝓊₁ ⁺

variable 𝓊 𝓋 𝓌 𝓊′ 𝓋′ 𝓌′ : Level

open import Cubical.Foundations.Function public
  using (_$_; _∘_; idfun; uncurry)

open import Function public using (it)

open import Cubical.Data.Sigma public
  using (Σ; _,_; fst; snd) renaming (_×_ to infixr 3 _×_)

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ x ∶ A , B

open import Cubical.Data.Empty public
  using (⊥) renaming (rec to ⊥-rec)

open import Cubical.Relation.Nullary public using (¬_)

open import Cubical.Data.Unit public renaming (Unit to ⊤)

open import Cubical.Data.Nat public using (ℕ)

open import Cubical.Foundations.Prelude public
  using (isProp; isSet; isPropIsProp; isProp→isSet)

open import Cubical.Data.Empty public using (isProp⊥)
open import Cubical.Data.Nat public using (isSetℕ)

open import Cubical.Foundations.HLevels public
  using ( isPropΠ; isPropΠ2; isPropΠ3; isPropΠ4; isPropΠ5; isPropΠ6; isProp→
        ; isProp×; isProp×2; isProp×3; isProp×4; isProp×5; isPropΣ
        ; isSetΠ; isSetΣ; isOfHLevelLift)

open import Cubical.Foundations.HLevels public using (hProp; isSetHProp)

open import Cubical.Foundations.HLevels public using (hSet; isGroupoidHSet)

open import Cubical.Foundations.Structure public
  using (TypeWithStr; ⟨_⟩; str)

open import Cubical.HITs.PropositionalTruncation public
  using (∥_∥₁; ∣_∣₁; squash₁)
  renaming ( rec to ∥∥₁-rec; rec2 to ∥∥₁-rec2
           ; map to ∥∥₁-map; map2 to ∥∥₁-map2)

open import Cubical.Data.Sigma public using (∃)

∃-syntax = ∃
infix 2 ∃-syntax
syntax ∃-syntax A (λ x → B) = ∃ x ∶ A , B

open import Cubical.HITs.SetTruncation public
  using (∥_∥₂; ∣_∣₂; squash₂)
  renaming (rec to ∥∥₂-rec; rec2 to ∥∥₂-rec2 ; map to ∥∥₂-map)

open import Cubical.Foundations.Prelude public
  using ( PathP; _≡_; refl; sym; _∙_; cong; cong₂; subst; subst2
        ; transport; funExt; funExt⁻; isProp→PathP)

open import Cubical.Data.Sigma public using (ΣPathP)

Σ≡Prop : {A : Type 𝓊} {B : A → Type 𝓋} → (∀ x → isProp (B x)) →
  {p q : Σ A B} → fst p ≡ fst q → p ≡ q
Σ≡Prop {B} prop path = ΣPathP (path , isProp→PathP (λ i → prop _) _ _)

private variable A B : Type 𝓊

import Cubical.Data.Sum
module ⊎ = Cubical.Data.Sum
open ⊎ public using (_⊎_)

infixr 2 _∨_
_∨_ : Type 𝓊 → Type 𝓋 → Type _
A ∨ B = ∥ A ⊎ B ∥₁

inl : A → A ∨ B
inl x = ∣ ⊎.inl x ∣₁

inr : B → A ∨ B
inr x = ∣ ⊎.inr x ∣₁

open import Iff public

noncontradiction : ¬ (A ↔ (¬ A))
noncontradiction record { to = to ; from = from } = to (from λ x → to x x) (from λ x → to x x)
