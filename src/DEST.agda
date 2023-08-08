{-# OPTIONS --cubical --safe #-}
{-# OPTIONS --lossy-unification #-}

module DEST where
open import Prelim
open import Cubical.Data.Maybe

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

  -- 公式
  data Formula : Type where
    ⟨⊥⟩ : Formula

    -- 公式只能由一种属于关系构成, 非绑定变量要求是均质集
    _⟨∈⟩_ : USet → USet → Formula
    _⟨=⟩_ : USet → USet → Formula
    _⟨∧⟩_ : Formula → Formula → Formula
    _⟨∨⟩_ : Formula → Formula → Formula
    _⟨→⟩_ : Formula → Formula → Formula
    ⟨∀⟩_ : (Domain → Formula) → Formula
    ⟨∃⟩_ : (Domain → Formula) → Formula

    -- 变量绑定
    x⟨∈⟩_ : USet → Formula
    _⟨∈⟩x : USet → Formula
    x⟨∈⟩x : Formula
    x⟨=⟩_ : USet → Formula

  -- 一类解释
  ⟦_⟧₁ : Formula → Domain → Type
  ⟦ ⟨⊥⟩ ⟧₁     _ = ⊥
  ⟦ x ⟨∈⟩ y ⟧₁ _ = fst x ∈₁ fst y
  ⟦ x ⟨=⟩ y ⟧₁ _ = fst x ≡ fst y
  ⟦ φ ⟨∧⟩ ψ ⟧₁ x = ⟦ φ ⟧₁ x × ⟦ ψ ⟧₁ x
  ⟦ φ ⟨∨⟩ ψ ⟧₁ x = ⟦ φ ⟧₁ x ∨ ⟦ ψ ⟧₁ x
  ⟦ φ ⟨→⟩ ψ ⟧₁ x = ⟦ φ ⟧₁ x → ⟦ ψ ⟧₁ x
  ⟦ ⟨∀⟩ φ ⟧₁   x = ∀ x → ⟦ φ x ⟧₁ x
  ⟦ ⟨∃⟩ φ ⟧₁   x = ∃ x ∶ Domain , ⟦ φ x ⟧₁ x
  ⟦ x⟨∈⟩ y ⟧₁ x = x ∈₁ fst y
  ⟦ y ⟨∈⟩x ⟧₁ x = fst y ∈₁ x
  ⟦ x⟨∈⟩x  ⟧₁ x = x ∈₁ x
  ⟦ x⟨=⟩ y ⟧₁ x = x ∈₁ fst y

  -- 二类解释
  ⟦_⟧₂ : Formula → Domain → Type
  ⟦ ⟨⊥⟩ ⟧₂     _ = ⊥
  ⟦ x ⟨∈⟩ y ⟧₂ _ = fst x ∈₂ fst y
  ⟦ x ⟨=⟩ y ⟧₂ _ = fst x ≡ fst y
  ⟦ φ ⟨∧⟩ ψ ⟧₂ x = ⟦ φ ⟧₂ x × ⟦ ψ ⟧₂ x
  ⟦ φ ⟨∨⟩ ψ ⟧₂ x = ⟦ φ ⟧₂ x ∨ ⟦ ψ ⟧₂ x
  ⟦ φ ⟨→⟩ ψ ⟧₂ x = ⟦ φ ⟧₂ x → ⟦ ψ ⟧₂ x
  ⟦ ⟨∀⟩ φ ⟧₂   x = ∀ x → ⟦ φ x ⟧₂ x
  ⟦ ⟨∃⟩ φ ⟧₂   x = ∃ x ∶ Domain , ⟦ φ x ⟧₂ x
  ⟦ x⟨∈⟩ y ⟧₂ x = x ∈₂ fst y
  ⟦ y ⟨∈⟩x ⟧₂ x = fst y ∈₂ x
  ⟦ x⟨∈⟩x  ⟧₂ x = x ∈₂ x
  ⟦ x⟨=⟩ y ⟧₂ x = x ∈₂ fst y

  -- 导出符号
  infix 30 ⟨¬⟩_
  ⟨¬⟩_ : Formula → Formula
  ⟨¬⟩ φ = φ ⟨→⟩ ⟨⊥⟩

  ⟨⊤⟩ : Formula
  ⟨⊤⟩ = ⟨¬⟩ ⟨⊥⟩

  -- 公理的
  record Axiom : Type₁ where
    field
      -- 一类排中律
      excludedMiddle₁ : ∀ φ x → ⟦ φ ⟨∨⟩ ⟨¬⟩ φ ⟧₁ x
      -- 二类排中律
      excludedMiddle₂ : ∀ φ x → ⟦ φ ⟨∨⟩ ⟨¬⟩ φ ⟧₂ x

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

    -- 概括公理承诺
    commitment : Formula → Type
    commitment φ = Σ A ∶ Domain , ∀ x → (x ∈₁ A ↔ ⟦ φ ⟧₂ x) × (x ∈₂ A ↔ ⟦ φ ⟧₁ x)

    -- 概括公理
    field comprehension : ∀ φ → commitment φ

    -- 概括的记法
    compreh-syntax : Formula → Domain
    compreh-syntax φ = comprehension φ .fst
    syntax compreh-syntax φ = ｛x∣ φ ｝

    module _ {φ : Formula} {x : Domain} where
      -- 一类概括引入
      intro₁ : ⟦ φ ⟧₂ x → x ∈₁ ｛x∣ φ ｝
      intro₁ = comprehension φ .snd x .fst .from

      -- 二类概括引入
      intro₂ : ⟦ φ ⟧₁ x → x ∈₂ ｛x∣ φ ｝
      intro₂ = comprehension φ .snd x .snd .from

      -- 一类概括消去
      elim₁ : x ∈₁ ｛x∣ φ ｝ → ⟦ φ ⟧₂ x
      elim₁ = comprehension φ .snd x .fst .to

      -- 二类概括消去
      elim₂ : x ∈₂ ｛x∣ φ ｝ → ⟦ φ ⟧₁ x
      elim₂ = comprehension φ .snd x .snd .to

open Language ⦃...⦄
open Axiom ⦃...⦄

module _ ⦃ ℒ : Language ⦄ ⦃ axiom : Axiom ⦄ where

  -- 大全集
  𝕍 : Domain
  𝕍 = ｛x∣ ⟨⊤⟩ ｝

  -- 空集
  ∅ : Domain
  ∅ = ｛x∣ ⟨⊥⟩ ｝

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
  R = ｛x∣ ⟨¬⟩ x⟨∈⟩x ｝

    -- 罗素集无悖论
  noParadox₁ : R ∈₁ R ↔ R ∉₂ R
  noParadox₁ = R ∈₁ R ↔⟨ comprehension _ .snd R .fst ⟩ R ∉₂ R ↔∎

  noParadox₂ : R ∈₂ R ↔ R ∉₁ R
  noParadox₂ = R ∈₂ R ↔⟨ comprehension _ .snd R .snd ⟩ R ∉₁ R ↔∎

  -- 罗素集非均质集
  ¬isUSetR : ¬ isUSet R
  ¬isUSetR isUSetR = noncontradiction $
    R ∈₁ R ↔⟨ isUSetR R ⟩
    R ∈₂ R ↔⟨ noParadox₂ ⟩
    R ∉₁ R ↔∎
