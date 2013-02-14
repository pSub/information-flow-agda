open import Data.Bool

module Domain where

data Dom : Set where
  low : Dom
  high : Dom

postulate
  _=D_ : Dom → Dom → Bool
