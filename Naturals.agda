module Naturals where

data ℕ : Set where
  ze : ℕ
  su : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}
{-# BUILTIN ZERO ze #-}
{-# BUILTIN SUC su #-}

_+_ : ℕ → ℕ → ℕ
ze + y = y
su x + y = su (x + y)
infixr 5 _+_

_*_ : ℕ → ℕ → ℕ
ze * y = ze
su x * y = x * y + y
infixr 6 _*_

_^_ : ℕ → ℕ → ℕ
x ^ ze = 1
x ^ su n = (x ^ n) * x

data Add : ℕ → ℕ → ℕ → Set where
  zel : ∀ {n} → Add 0 n n 
  zer : ∀ {n} → Add n ze n
  susu : ∀ {l m n} → Add l m n → Add (su l) (su m) (su (su n))
