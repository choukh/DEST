{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module DEST where
open import Prelim

record Language : Type₁ where
  field
    Domain : Type
    isSetDomain : isSet Domain

    _∈₁_ : Domain → Domain → Type
    isProp∈₁ : ∀ x y → isProp (x ∈₁ y)

    _∈₂_ : Domain → Domain → Type
    isProp∈₂ : ∀ x y → isProp (x ∈₂ y)

  _∉₁_ : Domain → Domain → Type
  x ∉₁ y = ¬ x ∈₁ y

  _∉₂_ : Domain → Domain → Type
  x ∉₂ y = ¬ x ∈₂ y

  _⊆_ : Domain → Domain → Type
  A ⊆ B = ∀ x → (x ∈₁ A → x ∈₁ B) ∨ (x ∈₂ A → x ∈₂ B)

  isUSet : Domain → Type
  isUSet A = ∀ x → x ∈₁ A ↔ x ∈₂ A

  allUSet : Domain → Type
  allUSet A = ∀ x → (x ∈₁ A ∨ x ∈₂ A) → isUSet x

  USet = Σ Domain isUSet

  data Formula : Type where
    ⟨⊥⟩ : Formula
    _⟨∈⟩_ : Domain → Domain → Formula
    _⟨=⟩_ : Domain → Domain → Formula
    _⟨∧⟩_ : Formula → Formula → Formula
    _⟨∨⟩_ : Formula → Formula → Formula
    _⟨→⟩_ : Formula → Formula → Formula
    ⟨∀⟩_ : (USet → Formula) → Formula
    ⟨∃⟩_ : (Domain → Formula) → Formula

  ⟦_⟧₁ : Formula → Type
  ⟦ ⟨⊥⟩ ⟧₁ = ⊥
  ⟦ x ⟨∈⟩ y ⟧₁ = x ∈₁ y
  ⟦ x ⟨=⟩ y ⟧₁ = x ≡ y
  ⟦ φ ⟨∧⟩ ψ ⟧₁ = ⟦ φ ⟧₁ × ⟦ ψ ⟧₁
  ⟦ φ ⟨∨⟩ ψ ⟧₁ = ⟦ φ ⟧₁ ∨ ⟦ ψ ⟧₁
  ⟦ φ ⟨→⟩ ψ ⟧₁ = ⟦ φ ⟧₁ → ⟦ ψ ⟧₁
  ⟦ ⟨∀⟩ φ ⟧₁ = ∀ x → ⟦ φ x ⟧₁
  ⟦ ⟨∃⟩ φ ⟧₁ = ∃ x ∶ Domain , ⟦ φ x ⟧₁

  ⟦_⟧₂ : Formula → Type
  ⟦ ⟨⊥⟩ ⟧₂ = ⊥
  ⟦ x ⟨∈⟩ y ⟧₂ = x ∈₂ y
  ⟦ x ⟨=⟩ y ⟧₂ = x ≡ y
  ⟦ φ ⟨∧⟩ ψ ⟧₂ = ⟦ φ ⟧₂ × ⟦ ψ ⟧₂
  ⟦ φ ⟨∨⟩ ψ ⟧₂ = ⟦ φ ⟧₂ ∨ ⟦ ψ ⟧₂
  ⟦ φ ⟨→⟩ ψ ⟧₂ = ⟦ φ ⟧₂ → ⟦ ψ ⟧₂
  ⟦ ⟨∀⟩ φ ⟧₂ = ∀ x → ⟦ φ x ⟧₂
  ⟦ ⟨∃⟩ φ ⟧₂ = ∃ x ∶ Domain , ⟦ φ x ⟧₂

  isProp⟦⟧₁ : ∀ φ → isProp ⟦ φ ⟧₁
  isProp⟦⟧₁ ⟨⊥⟩ = isProp⊥
  isProp⟦⟧₁ (x ⟨∈⟩ y) = isProp∈₁ x y
  isProp⟦⟧₁ (x ⟨=⟩ y) = isSetDomain x y
  isProp⟦⟧₁ (φ ⟨∧⟩ ψ) = isProp× (isProp⟦⟧₁ φ) (isProp⟦⟧₁ ψ)
  isProp⟦⟧₁ (φ ⟨∨⟩ ψ) = squash₁
  isProp⟦⟧₁ (φ ⟨→⟩ ψ) = isProp→ (isProp⟦⟧₁ ψ)
  isProp⟦⟧₁ (⟨∀⟩ φ) = isPropΠ λ x → isProp⟦⟧₁ (φ x)
  isProp⟦⟧₁ (⟨∃⟩ φ) = squash₁

  isProp⟦⟧₂ : ∀ φ → isProp ⟦ φ ⟧₂
  isProp⟦⟧₂ ⟨⊥⟩ = isProp⊥
  isProp⟦⟧₂ (x ⟨∈⟩ y) = isProp∈₂ x y
  isProp⟦⟧₂ (x ⟨=⟩ y) = isSetDomain x y
  isProp⟦⟧₂ (φ ⟨∧⟩ ψ) = isProp× (isProp⟦⟧₂ φ) (isProp⟦⟧₂ ψ)
  isProp⟦⟧₂ (φ ⟨∨⟩ ψ) = squash₁
  isProp⟦⟧₂ (φ ⟨→⟩ ψ) = isProp→ (isProp⟦⟧₂ ψ)
  isProp⟦⟧₂ (⟨∀⟩ φ) = isPropΠ λ x → isProp⟦⟧₂ (φ x)
  isProp⟦⟧₂ (⟨∃⟩ φ) = squash₁

  infix 30 ⟨¬⟩_
  ⟨¬⟩_ : Formula → Formula
  ⟨¬⟩ φ = φ ⟨→⟩ ⟨⊥⟩

  ⟨⊤⟩ : Formula
  ⟨⊤⟩ = ⟨¬⟩ ⟨⊥⟩

  _⟨∉⟩_ : Domain → Domain → Formula
  x ⟨∉⟩ y = ⟨¬⟩ (x ⟨∈⟩ y)

  record Axiom : Type₁ where
    field
      excludedMiddle₁ : ∀ φ → ⟦ φ ⟨∨⟩ ⟨¬⟩ φ ⟧₁
      excludedMiddle₂ : ∀ φ → ⟦ φ ⟨∨⟩ ⟨¬⟩ φ ⟧₂
      extensionality  : ∀ x y → (∀ z → z ∈₁ x ↔ z ∈₂ y) → x ≡ y
      uniformity      : ∀ A B → A ⊆ B → allUSet B → isUSet A

    commitment : (Domain → Formula) → Type
    commitment P = Σ A ∶ Domain , ∀ x → (x ∈₁ A ↔ ⟦ P x ⟧₂) × (x ∈₂ A ↔ ⟦ P x ⟧₁)
    field
      comprehension  : ∀ P → commitment P

    compreh-syntax : (Domain → Formula) → Domain
    compreh-syntax P = comprehension P .fst
    syntax compreh-syntax (λ x → P) = ｛ x ∣ P ｝

    module _ {P : Domain → Formula} {x : Domain} where
      compI₁ : ⟦ P x ⟧₂ → x ∈₁ ｛ x ∣ P x ｝
      compI₁ = comprehension P .snd x .fst .from

      compI₂ : ⟦ P x ⟧₁ → x ∈₂ ｛ x ∣ P x ｝
      compI₂ = comprehension P .snd x .snd .from

      compE₁ : x ∈₁ ｛ x ∣ P x ｝ → ⟦ P x ⟧₂
      compE₁ = comprehension P .snd x .fst .to

      compE₂ : x ∈₂ ｛ x ∣ P x ｝ → ⟦ P x ⟧₁
      compE₂ = comprehension P .snd x .snd .to

open Language ⦃...⦄
open Axiom ⦃...⦄

module _ ⦃ ℒ : Language ⦄ ⦃ axiom : Axiom ⦄ where

  𝕍 : Domain
  𝕍 = ｛ _ ∣ ⟨⊤⟩ ｝

  ∅ : Domain
  ∅ = ｛ x ∣ ⟨⊥⟩ ｝

  module _ {x : Domain} where
    ∈₁𝕍 : x ∈₁ 𝕍
    ∈₁𝕍 = compI₁ (idfun _)

    ∈₂𝕍 : x ∈₂ 𝕍
    ∈₂𝕍 = compI₂ (idfun _)

    ∉₁∅ : x ∉₁ ∅
    ∉₁∅ = ⊥-rec ∘ compE₁

    ∉₂∅ : x ∉₂ ∅
    ∉₂∅ = ⊥-rec ∘ compE₂

  isUSet𝕍 : isUSet 𝕍
  isUSet𝕍 x = →: (λ _ → ∈₂𝕍) ←: (λ _ → ∈₁𝕍)

  isUSet∅ : isUSet ∅
  isUSet∅ x = →: ⊥-rec ∘ ∉₁∅ ←: ⊥-rec ∘ ∉₂∅

  R : Domain
  R = ｛ x ∣ x ⟨∉⟩ x ｝

  noParadox₁ : R ∈₁ R ↔ R ∉₂ R
  noParadox₁ = R ∈₁ R ↔⟨ comprehension _ .snd R .fst ⟩ R ∉₂ R ↔∎

  noParadox₂ : R ∈₂ R ↔ R ∉₁ R
  noParadox₂ = R ∈₂ R ↔⟨ comprehension _ .snd R .snd ⟩ R ∉₁ R ↔∎

  ¬isUSetR : ¬ isUSet R
  ¬isUSetR isUSetR = noncontradiction $
    R ∈₁ R ↔⟨ isUSetR R ⟩
    R ∈₂ R ↔⟨ noParadox₂ ⟩
    R ∉₁ R ↔∎

  duality : (P : Domain → Formula) (x : Domain) → ⟦ P x ⟧₁ ↔ ⟦ P x ⟧₂
  duality P x = aux
    where
    A = ｛ _ ∣ P x ｝
    𝕍≡A : ⟦ P x ⟧₁ → 𝕍 ≡ A
    𝕍≡A ⟦Px⟧₁ = extensionality _ _ λ z → →: (λ _ → compI₂ ⟦Px⟧₁) ←: (λ _ → ∈₁𝕍)
    A≡𝕍 : ⟦ P x ⟧₂ → A ≡ 𝕍
    A≡𝕍 ⟦Px⟧₂ = extensionality _ _ λ z → →: (λ _ → ∈₂𝕍) ←: (λ _ → compI₁ ⟦Px⟧₂)
    aux : ⟦ P x ⟧₁ ↔ ⟦ P x ⟧₂
    _↔_.to aux ⟦Px⟧₁ = ∥∥₁-rec (isProp⟦⟧₂ _) H (excludedMiddle₂ (P x)) where
      H : ⟦ P x ⟧₂ ⊎ (¬ ⟦ P x ⟧₂) → ⟦ P x ⟧₂
      H (⊎.inl  ⟦Px⟧₂) = ⟦Px⟧₂
      H (⊎.inr ¬⟦Px⟧₂) = ⊥-rec $ ¬⟦Px⟧₂ $ compE₁ x∈₁A where
        x∈₁A : x ∈₁ A
        x∈₁A = subst (x ∈₁_) (𝕍≡A ⟦Px⟧₁) ∈₁𝕍
    _↔_.from aux ⟦Px⟧₂ = ∥∥₁-rec (isProp⟦⟧₁ _) H (excludedMiddle₁ (P x)) where
      H : ⟦ P x ⟧₁ ⊎ (¬ ⟦ P x ⟧₁) → ⟦ P x ⟧₁
      H (⊎.inl  ⟦Px⟧₁) = ⟦Px⟧₁
      H (⊎.inr ¬⟦Px⟧₁) = ⊥-rec $ ¬⟦Px⟧₁ $ compE₂ x∈₂A where
        x∈₂A : x ∈₂ A
        x∈₂A = subst (x ∈₂_) (sym $ A≡𝕍 ⟦Px⟧₂) ∈₂𝕍

  commitment-unique : (P : Domain → Formula) → isProp (commitment P)
  commitment-unique P (A , H₁) (B , H₂) = Σ≡Prop
    (λ _ → isPropΠ λ _ → isProp× (isProp↔ (isProp∈₁ _ _) (isProp⟦⟧₂ _))
                                 (isProp↔ (isProp∈₂ _ _) (isProp⟦⟧₁ _)))
    (extensionality _ _ λ z →
      z ∈₁ A    ↔⟨ H₁ z .fst ⟩
      ⟦ P z ⟧₂  ↔˘⟨ duality P z ⟩
      ⟦ P z ⟧₁  ↔˘⟨ H₂ z .snd ⟩
      z ∈₂ B    ↔∎)
