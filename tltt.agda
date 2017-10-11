module tltt where


postulate

  is-fibrant : ∀ {i} → Set i → Set i
  instance Π-is-fibrant : ∀ {i}{j}{A : Set i}{B : A → Set j}
                    → ⦃ fibA : is-fibrant A ⦄
                    → ⦃ fibB : (a : A) → is-fibrant (B a) ⦄
                    → is-fibrant ((a : A) → B a)

module _ {i} {A : Set i} ⦃ fibA : is-fibrant A ⦄ where

  postulate

    _~_ : A → A → Set i



module test {i}{j}{A : Set i}{B : A → Set j}

  ⦃ fibA : is-fibrant A ⦄

-- this will work, if we change (a : A) → is-fibrant (B a)
-- to {a : A} → is-fibrant (B a)
  ⦃ fibB : (a : A) → is-fibrant (B a) ⦄ where

  test : (f : (a : A) → B a) → f ~ f
  
  test = ?
