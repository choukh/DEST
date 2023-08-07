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
    -- 一致性要求: 自由变量是均质集
    ⟨∀⟩_ : (USet → Formula) → Formula
    ⟨∃⟩_ : (Domain → Formula) → Formula

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
    commitment P = Σ A ∶ Domain , ∀ x → (x ∈₁ A ↔ ⟦ P x ⟧₂) × (x ∈₂ A ↔ ⟦ P x ⟧₁)
    -- 概括公理
    field comprehension : ∀ P → commitment P

    -- 概括的记法
    compreh-syntax : (Domain → Formula) → Domain
    compreh-syntax P = comprehension P .fst
    syntax compreh-syntax (λ x → P) = ｛ x ∣ P ｝

    module _ {P : Domain → Formula} {x : Domain} where
      -- 一类概括引入
      compI₁ : ⟦ P x ⟧₂ → x ∈₁ ｛ x ∣ P x ｝
      compI₁ = comprehension P .snd x .fst .from

      -- 二类概括引入
      compI₂ : ⟦ P x ⟧₁ → x ∈₂ ｛ x ∣ P x ｝
      compI₂ = comprehension P .snd x .snd .from

      -- 一类概括消去
      compE₁ : x ∈₁ ｛ x ∣ P x ｝ → ⟦ P x ⟧₂
      compE₁ = comprehension P .snd x .fst .to

      -- 二类概括消去
      compE₂ : x ∈₂ ｛ x ∣ P x ｝ → ⟦ P x ⟧₁
      compE₂ = comprehension P .snd x .snd .to

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
    ∈₁𝕍 = compI₁ (idfun _)

    ∈₂𝕍 : x ∈₂ 𝕍
    ∈₂𝕍 = compI₂ (idfun _)

    ∉₁∅ : x ∉₁ ∅
    ∉₁∅ = ⊥-rec ∘ compE₁

    ∉₂∅ : x ∉₂ ∅
    ∉₂∅ = ⊥-rec ∘ compE₂

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
  noParadox₁ = R ∈₁ R ↔⟨ comprehension _ .snd R .fst ⟩ R ∉₂ R ↔∎

  noParadox₂ : R ∈₂ R ↔ R ∉₁ R
  noParadox₂ = R ∈₂ R ↔⟨ comprehension _ .snd R .snd ⟩ R ∉₁ R ↔∎

  -- 罗素集非均质集
  ¬isUSetR : ¬ isUSet R
  ¬isUSetR isUSetR = noncontradiction $
    R ∈₁ R ↔⟨ isUSetR R ⟩
    R ∈₂ R ↔⟨ noParadox₂ ⟩
    R ∉₁ R ↔∎

  -- 公式的对偶性
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

  -- 概括承诺的唯一性 (意味着概括公理是命题)
  definability : (P : Domain → Formula) → isProp (commitment P)
  definability P (A , H₁) (B , H₂) = Σ≡Prop
    (λ _ → isPropΠ λ _ → isProp× (isProp↔ (isProp∈₁ _ _) (isProp⟦⟧₂ _))
                                 (isProp↔ (isProp∈₂ _ _) (isProp⟦⟧₁ _)))
    (extensionality _ _ λ z →
      z ∈₁ A    ↔⟨ H₁ z .fst ⟩
      ⟦ P z ⟧₂  ↔˘⟨ duality P z ⟩
      ⟦ P z ⟧₁  ↔˘⟨ H₂ z .snd ⟩
      z ∈₂ B    ↔∎)

  -- 能构成一类单集
  S₁ : Domain → Type
  S₁ x = Σ y ∶ Domain , ∀ z → z ∈₁ y ↔ z ≡ x

  -- 能构成二类单集
  S₂ : Domain → Type
  S₂ x = Σ y ∶ Domain , ∀ z → z ∈₂ y ↔ z ≡ x

  -- 任意集合能构成二类单集
  →S₁ : ∀ x → S₁ x
  →S₁ a = ｛ x ∣ x ⟨=⟩ a ｝ , λ x → comprehension _ .snd x .fst

  -- 任意集合能构成二类单集
  →S₂ : ∀ x → S₂ x
  →S₂ a = ｛ x ∣ x ⟨=⟩ a ｝ , λ x → comprehension _ .snd x .snd

  -- 能同时构成两类单集的集合是均质集
  S₁→S₂→isUSet : ∀ x → S₁ x → S₂ x → isUSet x
  S₁→S₂→isUSet a (b , Hb) (c , Hc) = ≈→isUSet a≈a′
    where
    b≈c : b ≈ c
    b≈c x =
      x ∈₁ b ↔⟨ Hb x ⟩
      x ≡ a  ↔˘⟨ Hc x ⟩
      x ∈₂ c ↔∎
    b-uset : isUSet b
    b-uset = ≈→isUSet b≈c
    ｛a｝ = ｛ x ∣ x ⟨=⟩ a ｝
    a′ : Domain
    a′ = ｛ x ∣ ⟨∃⟩ (λ y → (x ⟨∈⟩ y) ⟨∧⟩ (y ⟨∈⟩ ｛a｝)) ｝
    a≈a′ : a ≈ a′
    _↔_.to   (a≈a′ x) x∈₁a  = compI₂ ∣ a , x∈₁a , compI₁ refl ∣₁
    _↔_.from (a≈a′ x) x∈₂a′ = ∥∥₁-rec (isProp∈₁ _ _) aux (compE₂ x∈₂a′) where
      aux : (Σ y ∶ Domain , x ∈₁ y × y ∈₁ ｛a｝) → x ∈₁ a
      aux (y , x∈₁y , y∈₁｛a｝) = subst (x ∈₁_) (compE₁ y∈₁｛a｝) x∈₁y
