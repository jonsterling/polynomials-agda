module Reasoning where

data _≡_ {X : Set} (x : X) : X → Set where
  refl : x ≡ x
infix 2 _≡_

_∎ : ∀ {X} (x : X) → x ≡ x
x ∎ = refl

_≡[_⟩_ : ∀ {X} (x : X) {y z} → x ≡ y → y ≡ z → x ≡ z
x ≡[ refl ⟩ q = q

_≡⟨_]_ : ∀ {X} (x : X) {y z} → y ≡ x → y ≡ z → x ≡ z
x ≡⟨ refl ] q = q

infixr 2 _∎ _≡[_⟩_ _≡⟨_]_

_⟨≡⟩_ : ∀ {S T : Set} {f g : S → T} {x y} → f ≡ g → x ≡ y → f x ≡ g y
refl ⟨≡⟩ refl = refl

_≡⟩_ : ∀ {S T : Set} (f : S → T) {x y} → x ≡ y → f x ≡ f y
f ≡⟩ q = refl ⟨≡⟩ q

_⟨≡_ : ∀ {S T : Set} {f g : S → T} → f ≡ g → (x : S) → f x ≡ g x
q ⟨≡ x = q ⟨≡⟩ refl

infixl 0 _⟨≡⟩_ _⟨≡_ _≡⟩_ 

data ⊥ : Set where
record ⊤ : Set where constructor ◆
record _×_ (S T : Set) : Set where
  constructor _,_
  field fst : S; snd : T
open _×_ public

