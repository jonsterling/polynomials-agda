module Poly where

open import Reasoning
open import Naturals

data Poly : ℕ → Set where
  κ : ∀ {n} → ℕ → Poly n
  ι : ∀ {n} → Poly (su n)
  ↑ : ∀ {n} → Poly n → Poly n
  _⊕_ : ∀ {n} → Poly n → Poly n → Poly n
  times : ∀ {l m n} → Poly l → Poly m → Add l m n → Poly n

⟦_⟧_ : ∀ {n} → Poly n → ℕ → ℕ
⟦ κ n ⟧ x = n
⟦ ι ⟧ x = x
⟦ ↑ p ⟧ x = ⟦ p ⟧ su x
⟦ p ⊕ r ⟧ x = ⟦ p ⟧ x + ⟦ r ⟧ x
⟦ times p r a ⟧ x = ⟦ p ⟧ x * ⟦ r ⟧ x

sul : ∀ {l m n} → Add l m n → Add (su l) m (su n)
sul (zel {ze}) = zer
sul (zel {su n}) = susu zel
sul zer = zer
sul (susu s) = susu (sul s)

add : ∀ l m → Add l m (l + m)
add ze m = zel
add (su l) m = sul (add l m)

_⊗_ : ∀ {l m} → Poly l → Poly m → Poly (l + m)
_⊗_ {l} {m} p r = times p r (add l m)

_^p_ : ∀ {m} → Poly m → (n : ℕ) → Poly (n * m)
p ^p ze = κ 1
p ^p su n = (p ^p n) ⊗ p

ι₁ : Poly 1
ι₁ = ι

κ₀ : ℕ → Poly 0
κ₀ = κ

TestEq : (k : ℕ) {n : ℕ} (p r : Poly n) → Set
TestEq ze p r = ⊤
TestEq (su k) p r = (⟦ p ⟧ ze ≡ ⟦ r ⟧ ze)  × TestEq k (↑ p) (↑ r)

testLem : (n : ℕ) (p r : Poly n) → TestEq (su n) p r → (x : ℕ) → ⟦ p ⟧ x ≡ ⟦ r ⟧ x
testLem = {!!}

NoConf : ℕ → ℕ → Set
NoConf ze ze = ⊤
NoConf ze (su y) = ⊥
NoConf (su x) ze = ⊥
NoConf (su x) (su y) = x ≡ y

noConf : ∀ {x y} → x ≡ y → NoConf x y
noConf {ze} refl = ◆
noConf {su x} refl = refl

¬_ : Set → Set
¬ P = P → ⊥

data Dec (P : Set) : Set where
  yes : P → Dec P
  no : ¬ P → Dec P

decEq : (x y : ℕ) → Dec (x ≡ y)
decEq ze ze = yes refl
decEq ze (su y) = no noConf
decEq (su x) ze = no noConf
decEq (su x) (su y) with decEq x y
decEq (su .y) (su y) | yes refl = yes refl
decEq (su x) (su y) | no nq = no (λ q → nq (noConf q))

testEq : (k : ℕ) {n : ℕ} (p r : Poly n) → Dec (TestEq k p r)
testEq ze p r = yes ◆
testEq (su k) p r with decEq (⟦ p ⟧ 0) (⟦ r ⟧ 0) | testEq k (↑ p) (↑ r)
testEq (su k) p r | yes y | yes z = yes (y , z)
testEq (su k) p r | yes x | no np = no (λ xy → np (snd xy))
testEq (su k) p r | no x | _ = no (λ xy → x (fst xy))
