{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module DEST where
open import Prelim

-- 语言
record Language : Type₁ where
  field
    -- 论域
    Domain : Type
    isSetDomain : isSet Domain

    -- 一类属于
    _∈₁_ : Domain → Domain → Type
    isProp∈₁ : ∀ x y → isProp (x ∈₁ y)

    -- 二类属于
    _∈₂_ : Domain → Domain → Type
    isProp∈₂ : ∀ x y → isProp (x ∈₂ y)

  _∉₁_ : Domain → Domain → Type
  x ∉₁ y = ¬ x ∈₁ y

  _∉₂_ : Domain → Domain → Type
  x ∉₂ y = ¬ x ∈₂ y

  -- 双面包含关系
  _⊆_ : Domain → Domain → Type
  A ⊆ B = ∀ x → (x ∈₁ A → x ∈₁ B) ∨ (x ∈₂ A → x ∈₂ B)

  -- 均质集 (uniform set)
  isUSet : Domain → Type
  isUSet A = ∀ x → x ∈₁ A ↔ x ∈₂ A

  -- 均质集之集 (set of uniform set)
  allUSet : Domain → Type
  allUSet A = ∀ x → (x ∈₁ A ∨ x ∈₂ A) → isUSet x

  -- 均质集之类型
  USet = Σ Domain isUSet

  data Formula : Type where
    ⟨⊥⟩ : Formula
    -- 公式只能由一种属于关系构成
    _⟨∈⟩_ : Domain → Domain → Formula
    _⟨=⟩_ : Domain → Domain → Formula
    _⟨∧⟩_ : Formula → Formula → Formula
    _⟨∨⟩_ : Formula → Formula → Formula
    _⟨→⟩_ : Formula → Formula → Formula
    ⟨∀⟩_ : (Domain → Formula) → Formula
    ⟨∃⟩_ : (Domain → Formula) → Formula

  -- 合式公式
  isWFF : Domain → Formula → Type
  isWFF b ⟨⊥⟩ = ⊤
  isWFF b (x ⟨∈⟩ y) = (isUSet x ∨ x ≡ b) × (isUSet y ∨ y ≡ b)
  isWFF b (x ⟨=⟩ y) = (isUSet x ∨ x ≡ b) × (isUSet y ∨ y ≡ b)
  isWFF b (φ ⟨∧⟩ ψ) = isWFF b φ × isWFF b ψ
  isWFF b (φ ⟨∨⟩ ψ) = isWFF b φ × isWFF b ψ
  isWFF b (φ ⟨→⟩ ψ) = isWFF b φ × isWFF b ψ
  isWFF b (⟨∀⟩ φ) = ∀ x → isWFF b (φ x)
  isWFF b (⟨∃⟩ φ) = ∀ x → isWFF b (φ x)

  -- 一类解释
  ⟦_⟧₁ : Formula → Type
  ⟦ ⟨⊥⟩ ⟧₁ = ⊥
  ⟦ x ⟨∈⟩ y ⟧₁ = x ∈₁ y
  ⟦ x ⟨=⟩ y ⟧₁ = x ≡ y
  ⟦ φ ⟨∧⟩ ψ ⟧₁ = ⟦ φ ⟧₁ × ⟦ ψ ⟧₁
  ⟦ φ ⟨∨⟩ ψ ⟧₁ = ⟦ φ ⟧₁ ∨ ⟦ ψ ⟧₁
  ⟦ φ ⟨→⟩ ψ ⟧₁ = ⟦ φ ⟧₁ → ⟦ ψ ⟧₁
  ⟦ ⟨∀⟩ φ ⟧₁ = ∀ x → ⟦ φ x ⟧₁
  ⟦ ⟨∃⟩ φ ⟧₁ = ∃ x ∶ Domain , ⟦ φ x ⟧₁

  -- 二类解释
  ⟦_⟧₂ : Formula → Type
  ⟦ ⟨⊥⟩ ⟧₂ = ⊥
  ⟦ x ⟨∈⟩ y ⟧₂ = x ∈₂ y
  ⟦ x ⟨=⟩ y ⟧₂ = x ≡ y
  ⟦ φ ⟨∧⟩ ψ ⟧₂ = ⟦ φ ⟧₂ × ⟦ ψ ⟧₂
  ⟦ φ ⟨∨⟩ ψ ⟧₂ = ⟦ φ ⟧₂ ∨ ⟦ ψ ⟧₂
  ⟦ φ ⟨→⟩ ψ ⟧₂ = ⟦ φ ⟧₂ → ⟦ ψ ⟧₂
  ⟦ ⟨∀⟩ φ ⟧₂ = ∀ x → ⟦ φ x ⟧₂
  ⟦ ⟨∃⟩ φ ⟧₂ = ∃ x ∶ Domain , ⟦ φ x ⟧₂

  -- 一类解释为命题
  isProp⟦⟧₁ : ∀ φ → isProp ⟦ φ ⟧₁
  isProp⟦⟧₁ ⟨⊥⟩ = isProp⊥
  isProp⟦⟧₁ (x ⟨∈⟩ y) = isProp∈₁ x y
  isProp⟦⟧₁ (x ⟨=⟩ y) = isSetDomain x y
  isProp⟦⟧₁ (φ ⟨∧⟩ ψ) = isProp× (isProp⟦⟧₁ φ) (isProp⟦⟧₁ ψ)
  isProp⟦⟧₁ (φ ⟨∨⟩ ψ) = squash₁
  isProp⟦⟧₁ (φ ⟨→⟩ ψ) = isProp→ (isProp⟦⟧₁ ψ)
  isProp⟦⟧₁ (⟨∀⟩ φ) = isPropΠ λ x → isProp⟦⟧₁ (φ x)
  isProp⟦⟧₁ (⟨∃⟩ φ) = squash₁

  -- 二类解释为命题
  isProp⟦⟧₂ : ∀ φ → isProp ⟦ φ ⟧₂
  isProp⟦⟧₂ ⟨⊥⟩ = isProp⊥
  isProp⟦⟧₂ (x ⟨∈⟩ y) = isProp∈₂ x y
  isProp⟦⟧₂ (x ⟨=⟩ y) = isSetDomain x y
  isProp⟦⟧₂ (φ ⟨∧⟩ ψ) = isProp× (isProp⟦⟧₂ φ) (isProp⟦⟧₂ ψ)
  isProp⟦⟧₂ (φ ⟨∨⟩ ψ) = squash₁
  isProp⟦⟧₂ (φ ⟨→⟩ ψ) = isProp→ (isProp⟦⟧₂ ψ)
  isProp⟦⟧₂ (⟨∀⟩ φ) = isPropΠ λ x → isProp⟦⟧₂ (φ x)
  isProp⟦⟧₂ (⟨∃⟩ φ) = squash₁

  -- 导出符号
  infix 30 ⟨¬⟩_
  ⟨¬⟩_ : Formula → Formula
  ⟨¬⟩ φ = φ ⟨→⟩ ⟨⊥⟩

  ⟨⊤⟩ : Formula
  ⟨⊤⟩ = ⟨¬⟩ ⟨⊥⟩

  _⟨∉⟩_ : Domain → Domain → Formula
  x ⟨∉⟩ y = ⟨¬⟩ (x ⟨∈⟩ y)

  -- 合式公式实例
  instance
    ⊤-wff : ∀ {x} → isWFF x ⟨⊤⟩
    ⊤-wff = tt , tt

    x∉x-wff : ∀ {x} → isWFF x (x ⟨∉⟩ x)
    x∉x-wff = (inr refl , inr refl) , tt

  -- 公理
  record Axiom : Type₁ where
    field
      -- 一类排中律
      excludedMiddle₁ : ∀ φ → ⟦ φ ⟨∨⟩ ⟨¬⟩ φ ⟧₁
      -- 二类排中律
      excludedMiddle₂ : ∀ φ → ⟦ φ ⟨∨⟩ ⟨¬⟩ φ ⟧₂

    -- 混合外延等价关系
    _≈_ : Domain → Domain → Type
    x ≈ y = ∀ z → z ∈₁ x ↔ z ∈₂ y

    -- 混合外延公理
    field extensionality : ∀ x y → x ≈ y → x ≡ y

    -- 混合外延等价集是均质集
    ≈→isUSet : ∀ {x y} → x ≈ y → isUSet x
    ≈→isUSet {x} {y} x~y z = subst (λ - → (z ∈₁ x) ↔ (z ∈₂ -)) (sym $ extensionality _ _ x~y) (x~y z)

    -- 均质公理
    field uniformity : ∀ A B → A ⊆ B → allUSet B → isUSet A

    -- 均质公理保证了均质集之集是均质集
    allUSet→isUSet : ∀ x → allUSet x → isUSet x
    allUSet→isUSet x = uniformity x x λ y → inl (idfun _)

    -- 概括公理承诺集
    commitment : (Domain → Formula) → Type
    commitment P = Σ A ∶ Domain , ∀ x → isWFF x (P x) → (x ∈₁ A ↔ ⟦ P x ⟧₂) × (x ∈₂ A ↔ ⟦ P x ⟧₁)
    -- 概括公理
    field comprehension : ∀ P → commitment P

    -- 概括的记法
    compreh-syntax : (Domain → Formula) → Domain
    compreh-syntax P = comprehension P .fst
    syntax compreh-syntax (λ x → P) = ｛ x ∣ P ｝

    module _ {P : Domain → Formula} {x : Domain} ⦃ wff : isWFF x (P x) ⦄ where
      -- 一类概括引入
      intro₁ : ⟦ P x ⟧₂ → x ∈₁ ｛ x ∣ P x ｝
      intro₁ = comprehension P .snd x wff .fst .from

      -- 二类概括引入
      intro₂ : ⟦ P x ⟧₁ → x ∈₂ ｛ x ∣ P x ｝
      intro₂ = comprehension P .snd x wff .snd .from

      -- 一类概括消去
      elim₁ : x ∈₁ ｛ x ∣ P x ｝ → ⟦ P x ⟧₂
      elim₁ = comprehension P .snd x wff .fst .to
      
      -- 二类概括消去
      elim₂ : x ∈₂ ｛ x ∣ P x ｝ → ⟦ P x ⟧₁
      elim₂ = comprehension P .snd x wff .snd .to

open Language ⦃...⦄
open Axiom ⦃...⦄

module _ ⦃ ℒ : Language ⦄ ⦃ axiom : Axiom ⦄ where

  -- 大全集
  𝕍 : Domain
  𝕍 = ｛ _ ∣ ⟨⊤⟩ ｝

  -- 空集
  ∅ : Domain
  ∅ = ｛ _ ∣ ⟨⊥⟩ ｝

  module _ {x : Domain} where
    ∈₁𝕍 : x ∈₁ 𝕍
    ∈₁𝕍 = intro₁ (idfun _)

    ∈₂𝕍 : x ∈₂ 𝕍
    ∈₂𝕍 = intro₂ (idfun _)

    ∉₁∅ : x ∉₁ ∅
    ∉₁∅ = ⊥-rec ∘ elim₁

    ∉₂∅ : x ∉₂ ∅
    ∉₂∅ = ⊥-rec ∘ elim₂

  -- 大全集是均质集
  isUSet𝕍 : isUSet 𝕍
  isUSet𝕍 x = →: (λ _ → ∈₂𝕍) ←: (λ _ → ∈₁𝕍)

  -- 空集是均质集
  isUSet∅ : isUSet ∅
  isUSet∅ x = →: ⊥-rec ∘ ∉₁∅ ←: ⊥-rec ∘ ∉₂∅

  -- 罗素集
  R : Domain
  R = ｛ x ∣ x ⟨∉⟩ x ｝

  -- 罗素集无悖论
  noParadox₁ : R ∈₁ R ↔ R ∉₂ R
  noParadox₁ = R ∈₁ R ↔⟨ comprehension _ .snd R it .fst ⟩ R ∉₂ R ↔∎

  noParadox₂ : R ∈₂ R ↔ R ∉₁ R
  noParadox₂ = R ∈₂ R ↔⟨ comprehension _ .snd R it .snd ⟩ R ∉₁ R ↔∎

  -- 罗素集非均质集
  ¬isUSetR : ¬ isUSet R
  ¬isUSetR isUSetR = noncontradiction $
    R ∈₁ R ↔⟨ isUSetR R ⟩
    R ∈₂ R ↔⟨ noParadox₂ ⟩
    R ∉₁ R ↔∎
