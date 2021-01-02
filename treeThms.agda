module treeThms where

open import lib

-- simple Tree type storing natural numbers
data Tree : Set where
  Node : ℕ → Tree → Tree → Tree
  Leaf : Tree

mirror : Tree → Tree
mirror (Node x t1 t2) = Node x (mirror t2) (mirror t1)
mirror Leaf = Leaf

mirror-mirror : ∀ (t : Tree) → mirror (mirror t) ≡ t
mirror-mirror Leaf = refl
mirror-mirror (Node x t1 t2) rewrite mirror-mirror t2 | mirror-mirror t1 = refl


size : Tree → ℕ
size (Node x t t₁) = 1 + size t + size t₁
size Leaf = 1

height : Tree → ℕ
height (Node x t t₁) = 1 + (max (height t) (height t₁))
height Leaf = 0

numLeaves : Tree → ℕ
numLeaves (Node x t t₁) = numLeaves t + numLeaves t₁
numLeaves Leaf = 1

perfect : ℕ → Tree
perfect zero = Leaf
perfect (suc n) = Node 1 (perfect n) (perfect n)

-- I found I needed the +0 theorem from nat-thms.agda in the IAL
perfect-numLeaves : ∀(n : ℕ) → numLeaves (perfect n) ≡ 2 pow n
perfect-numLeaves zero = refl
perfect-numLeaves (suc n) rewrite +0 (2 pow n) |  perfect-numLeaves n  = refl

perfect-size : ∀(n : ℕ) → suc (size (perfect n)) ≡ 2 pow (suc n)
perfect-size zero = refl
perfect-size (suc n) rewrite  sym (perfect-size n) | +0 (size(perfect n)) | sym (+suc(size(perfect n))(size(perfect n)))= refl

-- helper lemma I found I needed below
max-same : ∀ (n : ℕ) → max n n ≡ n
max-same n rewrite <-irrefl n = refl

perfect-height : ∀(n : ℕ) → height (perfect n) ≡ n
perfect-height zero = refl
perfect-height (suc n) rewrite max-same (height(perfect n)) | perfect-height n = refl

numNodes : Tree → ℕ
numNodes (Node x t1 t2) = 1 + numNodes t1 + numNodes t2 
numNodes Leaf = 0

-- flatten a tree into a list of all the values stored at the nodes
prefixFlatten : Tree → 𝕃 ℕ
prefixFlatten (Node x t1 t2) = x :: prefixFlatten t1 ++ prefixFlatten t2
prefixFlatten Leaf = []

-- I found I needed a theorem from list-thms.agda in the IAL
length-flatten : ∀(t : Tree) → numNodes t ≡ length (prefixFlatten t)
length-flatten (Node x t1 t2) rewrite length-++(prefixFlatten t1) (prefixFlatten t2) | length-flatten t1 | length-flatten t2 = refl
length-flatten Leaf = refl
