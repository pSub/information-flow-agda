open import Data.Bool

module Domain where

data Dom : Set where
  low : Dom
  high : Dom

_=D_ : Dom → Dom → Bool
low =D low = true
low =D high = false
high =D low = false
high =D high = true
