module Patience where
  open import Relation.Binary using (DecTotalOrder; module DecTotalOrder;
    IsDecTotalOrder; module IsDecTotalOrder; Rel; module IsTotalOrder;
    module IsPartialOrder; module IsPreorder)
  open import Relation.Binary.Core hiding (_≡_; module _≡_; refl)
  open import Level hiding (_⊔_ ; suc) renaming (zero to lzero)
  open import Data.Nat using (ℕ; z≤n; s≤s; suc; _+_)
    renaming (decTotalOrder to decTotalOrderℕ; _≤_ to _≤ℕ_)
  open import Data.List using (List; []; _∷_)
  open import Data.Product using (Σ; _,_; _×_)
  open import Function using (_∘_)
  open import Data.Sum using (inj₁; inj₂)
  open import Data.Nat.Properties.Simple using (+-suc; +-assoc; +-comm)
  open import Relation.Binary.PropositionalEquality as PropEq
    using (_≡_; subst; cong; sym)
  open PropEq.≡-Reasoning

  -- A module that will contain a type of ordered "piles", analogous to piles of
  -- cards in Patience (though with the stronger restriction that piles are
  -- ordered by the top element).
  module Piles (dto : DecTotalOrder lzero lzero lzero) where
    open DecTotalOrder dto public renaming (Carrier to X)

    -- Append maximum element to X
    data X⊤ : Set where
      ⊤ : X⊤
      ⟦_⟧ : (x : X) → X⊤

    -- Define an ordering relation on the resulting type
    data _⟦≤⟧_ : Rel X⊤ Level.zero where
      x≤⊤ : ∀ {x} → x ⟦≤⟧ ⊤
      ⟦_⟧ : ∀ {x y} → (x ≤ y) → ⟦ x ⟧ ⟦≤⟧ ⟦ y ⟧

    open _⟦≤⟧_ public

    -- Ensure the order is transitive
    ⟦≤⟧-trans : Transitive _⟦≤⟧_
    ⟦≤⟧-trans _ x≤⊤ = x≤⊤
    ⟦≤⟧-trans ⟦ p ⟧ ⟦ q ⟧ =  ⟦ trans p q ⟧

    -- Define a type of (upper-) bounded, ordered vectors
    data OVec : X⊤ → ℕ → Set where
      ε : OVec ⊤ 0
      cons : ∀ {l n} → (x : X) → ⟦ x ⟧ ⟦≤⟧ l → OVec l n → OVec ⟦ x ⟧ (suc n)

    -- Minimum binary operation
    min : X⊤ → X⊤ → X⊤
    min ⊤ x = x
    min x ⊤ = x
    min ⟦ x ⟧ ⟦ y ⟧ with total x y
    ... | inj₁ x≤y = ⟦ x ⟧
    ... | inj₂ y≤x = ⟦ y ⟧

    -- Prove that the ordering respects min
    ⟦≤⟧-resp-min : ∀ {x y z} → x ⟦≤⟧ y → x ⟦≤⟧ z → x ⟦≤⟧ (min y z)
    ⟦≤⟧-resp-min {⊤} x≤⊤ x≤⊤ = x≤⊤
    ⟦≤⟧-resp-min {⟦ x ⟧} {⊤} _ q = q
    ⟦≤⟧-resp-min {⟦ x ⟧} {⟦ _ ⟧} {⊤} p _ = p
    ⟦≤⟧-resp-min {⟦ x ⟧} {⟦ y ⟧} {⟦ z ⟧} p q with total y z
    ... | inj₁ x≤y = p
    ... | inj₂ y≤x = q

    -- We can insert elements to an OVec
    insertOVec : ∀ {l n} → (x : X) → OVec l n  → OVec (min ⟦ x ⟧ l) (suc n)
    insertOVec x ε = cons x x≤⊤ ε
    insertOVec x (cons l p ls) with total x l
    ... | inj₁ x≤l = cons x ⟦ x≤l ⟧ (cons l p ls)
    ... | inj₂ l≤x = cons l (⟦≤⟧-resp-min ⟦ l≤x ⟧ p) (insertOVec x ls)

    -- Define a type of (upper-) bounded, ordered (by top elem) vectors of
    -- (non-empty) OVecs.
    data Piles : X⊤ → ℕ → Set where
      ε : Piles ⊤ 0
      consP : ∀{x n y m} → OVec ⟦ x ⟧ (suc n) → (⟦ x ⟧ ⟦≤⟧ y) → Piles y m
        → Piles ⟦ x ⟧ (suc n + m)

    -- Given a proof of equivalence between two elements of ℕ, we can transform
    -- Piles with one size to the other.
    cong-Piles : ∀ {n m l} → (n ≡ m) → Piles l n → Piles l m
    cong-Piles {l = l'} p l = subst (Piles l') p l

    -- We can insert a single element into existing Piles...
    insertElemPiles : ∀ {l n} → (x : X) → Piles l n
      → Piles (min ⟦ x ⟧ l) (suc n)
    insertElemPiles x ε = consP (cons x x≤⊤ ε) x≤⊤ ε
    insertElemPiles {⟦ l ⟧} x (consP {n = t} {m = s} ol p ols) with total x l
    ... | inj₁ x≤l = consP (cons x ⟦ x≤l ⟧ ol) (⟦≤⟧-trans ⟦ x≤l ⟧ p) ols
    ... | inj₂ l≤x = cong-Piles (+-suc (suc t) s) xInOLS
      where
        xInOLS : Piles ⟦ l ⟧ (suc (t + suc s))
        xInOLS = consP ol (⟦≤⟧-resp-min ⟦ l≤x ⟧ p) (insertElemPiles x ols)

    -- ...and can insert a single Pile into existing Piles.
    insertPilePiles : ∀ {lv lp n m} → OVec ⟦ lv ⟧ (suc n) → Piles lp m
      → Piles (min ⟦ lv ⟧ lp) (suc n + m)
    insertPilePiles l ε = consP l x≤⊤ ε
    insertPilePiles {lv} {⟦ lp ⟧} v (consP {n = n₁} {m = m₁} x q xs)
      with total lv lp -- Is the head of the pile we want to add smaller than
                       -- the head of the smallest existing pile?
    ... | inj₁ lv≤lp  = consP v ⟦ lv≤lp ⟧ (consP x q xs)
    ... | inj₂ lp≤lv with v
    ... | (cons {n = n₂} .lv _ _) =
        cong-Piles (cong suc ((permute-suc-xyz {n₁} {n₂} {m₁}))) vInPS
      where
        vInPS : Piles ⟦ lp ⟧ (suc (n₁ + suc (n₂ + m₁)))
        vInPS = consP x (⟦≤⟧-resp-min ⟦ lp≤lv ⟧ q) (insertPilePiles v xs)

        -- A useful lemma about ℕ
        permute-suc-xyz : ∀ {x y z} → x + suc (y + z) ≡ y + suc (x + z)
        permute-suc-xyz {x} {y} {z} =
          begin
           x + suc (y + z)
          ≡⟨ +-suc x (y + z) ⟩
           suc (x + (y + z))
          ≡⟨ cong suc (sym (+-assoc x y z)) ⟩
          suc ((x + y) + z)
          ≡⟨ cong suc (cong (λ x → x + z) (+-comm x y)) ⟩
          suc ((y + x) + z)
          ≡⟨ cong suc (+-assoc y x z) ⟩
          suc (y + (x + z))
          ≡⟨ sym (+-suc y (x + z)) ⟩
          y + suc (x + z)
          ∎

    -- From any non-empty Piles, we can remove the smallest element, to obtain
    -- a pair of that element, and a one-smaller Piles.
    removeOne : ∀ {l n} → Piles l (suc n) → X × (Σ X⊤ (λ l' → Piles l' n))
    removeOne (consP {y = remainingPilesLB} (cons x _ xs) _ xss) with xs
    ... | ε = x , remainingPilesLB , xss
    ... | cons firstPileLB _ _ =
      x , min ⟦ firstPileLB ⟧ remainingPilesLB , insertPilePiles xs xss

    -- By repeatedly removing a single element, we can convert Piles in a List.
    pilesToList : ∀ {l n} → Piles l n → List X
    pilesToList ε = []
    pilesToList {n = suc m} p with removeOne p
    ... | x , _ , ps = x ∷ pilesToList ps

    -- We can existentially hide the bound and size of Piles...
    data ∃Piles : Set where
      ∃<_> : ∀ {l n} → Piles l n → ∃Piles

    -- ...and can convert an arbitrary List into a Piles with unknown bound and
    -- size, by repeatedly inserting one element at a time.
    listToPiles : List X → ∃Piles
    listToPiles [] = ∃< ε >
    listToPiles (x ∷ xs) with listToPiles xs
    ... | ∃< ps > = ∃< insertElemPiles x ps >

    -- Finally, patience sort is simply creating Piles from an arbitrary List,
    -- before converting back to an ordered List.
    patienceSort : List X → List X
    patienceSort ls with listToPiles ls
    ... | ∃< ps > = pilesToList ps

  -- Let's create Piles of ℕ
  module Pilesℕ = Piles decTotalOrderℕ

  -- and some test lists.
  xs = Pilesℕ.patienceSort (5 ∷ 4 ∷ 3 ∷ 2 ∷ 1 ∷ [])
  ys = Pilesℕ.patienceSort []
  zs = Pilesℕ.patienceSort (4 ∷ 4 ∷ 1 ∷ 5 ∷ 3 ∷ [])
