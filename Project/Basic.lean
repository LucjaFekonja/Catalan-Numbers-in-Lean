import Mathlib
open Nat
open BigOperators
open Finset
open Finset.antidiagonal

/- ================================================================================================ -/
/- =================================         SMALL TASKS         ================================== -/
/- ================================================================================================ -/

/- ============================== TASK 1: CATALAN NUMBERS DEFINITION ============================== -/
-- Recursive definition.
def catalan_number : ℕ → ℕ
| 0 => 1
| (n + 1) => ∑ i : Fin n.succ, catalan_number i * catalan_number (n - i)


/- ================================ TASK 2: PLANE TREES DEFINITION ================================ -/
-- IDEA 1: Plane tree is completely specified by a number of subtrees.
inductive plane_tree1 : Type
| join : (n : ℕ) → (Fin n → plane_tree1) → plane_tree1

-- IDEA 2: Plane tree is defined with a list of children.
inductive plane_tree : Type
| join : List (plane_tree) → plane_tree


/- ============================= TASK 3: FULL BINARY TREES DEFINITION ============================= -/
-- A node can either be a leaf or have exactly two branches.
inductive full_binary_tree : Type
| leaf
| join : (T1 T2 : full_binary_tree) → full_binary_tree

-- Height of a full binary tree.
def full_binary_tree.height : full_binary_tree → ℕ
| .leaf => 0
| .join T1 T2 => max T1.height T2.height + 1

-- Number of leaves of a full binary tree.
def full_binary_tree.number_of_leaves : full_binary_tree → ℕ
| .leaf => 1
| .join T1 T2 => (number_of_leaves T1) + (number_of_leaves T2)

-- Number of nodes without leaves of a full binary tree.
def full_binary_tree.number_of_internal_nodes : full_binary_tree → ℕ
| .leaf => 0
| .join T1 T2 => T1.number_of_internal_nodes + T2.number_of_internal_nodes + 1


/- ======================= TASK 4: FULL BINARY TREES WITH n NODES DEFINITION ====================== -/
-- Definition of a binary tree with n nodes.
inductive binary_tree_with_nodes : ℕ → Type
| leaf : binary_tree_with_nodes 1
| succ : {n : ℕ} → binary_tree_with_nodes n → binary_tree_with_nodes (n + 1)
| join : {n m : ℕ} → binary_tree_with_nodes n → binary_tree_with_nodes m → binary_tree_with_nodes (n + m + 1)

-- Definition of a full binary tree with n nodes.
inductive full_binary_tree_with_nodes : ℕ → Type
| leaf : full_binary_tree_with_nodes 1
| join : {n m : ℕ} → full_binary_tree_with_nodes n → full_binary_tree_with_nodes m → full_binary_tree_with_nodes (n + m + 1)


/- ============================== TASK 5: BALLOT SEQUENCE DEFINITION ============================== -/
-- Sequence of votes where candidate A is always ahead or is tied with candidate B.
-- In this definition we use True to represent a vote for A and False to represent a vote for B.
inductive ballot_sequence : List Bool → Prop
| empty : ballot_sequence []
| add_A (w : List Bool) (h : ballot_sequence w) : ballot_sequence (w ++ [tt])
| add_B (w : List Bool) (h : ballot_sequence w) (hw : w.count tt > w.count ff) : ballot_sequence (w ++ [ff])



/- ================================================================================================ -/
/- =================================         LARGE TASKS         ================================== -/
/- ================================================================================================ -/

/- =============== TASK 4: ISOMORPHISM BETWEEN PLANE TREES AND A LIST OF PLANE TREES ============== -/
-- Construct a list of plane trees from a list of children.
def plane_to_list : plane_tree → List plane_tree
| .join L => L

-- Construct a plane tree by defining a list as children of root node.
def list_to_plane : List plane_tree → plane_tree
| L => .join L


/- ================================= TASK 5: ROTATING ISOMORPHISM ================================= -/
-- Leaf of a full binary tree is a plane tree with an empty list of subnodes.
-- Other nodes have two subnodes, which are recursively mapped into a list of children of a plane tree.
def full_to_plane : full_binary_tree → plane_tree
| full_binary_tree.leaf => plane_tree.join []
| (full_binary_tree.join left right) => plane_tree.join [full_to_plane left, full_to_plane right]

-- Plane tree with an empty list of subnodes is mapped to a full binary tree with only one node - root.
-- Otherwise, list of subnodes is not empty, and we set head of a list as the left subnode and
-- everything else as the right, recurively calling plane_to_full on both sides.
def plane_to_full : plane_tree → full_binary_tree
| (plane_tree.join []) => full_binary_tree.leaf
| (plane_tree.join (h :: t)) =>
  full_binary_tree.join (plane_to_full h) (plane_to_full (plane_tree.join t))


/- ================================= TASK 6: Bin(2n, n) is divisible by n + 1 ================================= -/

-- First we prove that n+1 | (2n choose n) for n=0
theorem one_div_zero_choose_zero : ((2 * 0).choose 0) % (0 + 1) = 0 := by
  rw [mul_zero, zero_add, choose_zero_right, mod_self]

-- Proof of 2n-n=n
theorem two_n_minus_n_is_n (n : ℕ) : (2 * n - n = n) := by
  nth_rewrite 2 [← one_mul n]
  rw [← Nat.mul_sub_right_distrib]
  ring

-- We can rewrite Bin(2n, n)/(n+1) as Bin(2n, n+1)/n.
theorem binom_div_eq_binom_succ (n : ℕ) (h : 0 < n) : ((2 * n).choose n) / (n + 1) = ((2 * n).choose (n + 1)) / n := by
 rw [choose_eq_factorial_div_factorial]
 . rw [two_n_minus_n_is_n, Nat.div_div_eq_div_mul]
   rw [mul_assoc, mul_comm (n !), mul_comm (n !), ← Nat.factorial_succ]
   nth_rewrite 3 [← Nat.mul_factorial_pred, mul_comm]
   rw [← mul_assoc, ← Nat.div_div_eq_div_mul]
   nth_rewrite 3 [← two_n_minus_n_is_n n]
   rw [Nat.sub_sub, ← choose_eq_factorial_div_factorial]
   . rw [two_mul]
     apply add_le_add_left
     rw [Nat.succ_le_iff]
     apply h
   . apply h
 . rw [two_mul]
   exact (Nat.le_add_left n n)


-- IDEA: We can rewrite Bin(2n, n)/(n+1) = Bin(2n, n) - Bin(2n, n+1).
--       Since binomial coefficient is an integer by its definition and
--       subtraction of integers is an integer, the right side is an integer.
--       Thus (n + 1) divides Bin(2n, n).

-- Here is how we want to prove that Bin(2n, n)/(n+1) = Bin(2n, n) - Bin(2n, n+1):
-- Bin(2n, n+1) = Bin(2n, n) - Bin(2n, n)/(n+1)
--              = (1 - 1/(n+1)) Bin(2n, n)
--              = n/(n+1) Bin(2n, n)
-- Therefore Bin(2n, n+1)/n = Bin(2n, n)/(n+1), which is exactly theorem "binom_div_eq_binom_succ".


-- this holds also for a, b, c ∈ ℕ
lemma aux1 (a b c : ℚ) : a - b = c ↔ a - c = b := by
  rw [sub_eq_iff_eq_add, add_comm, sub_eq_iff_eq_add]

-- this holds also for n ∈ ℕ, n ≠ -1
lemma aux2 (n : ℚ) (h : n + 1 ≠ 0) : 1 - 1 / (n + 1) = n / (n + 1) := by
  have h1 : (1 : ℚ) = (n + 1) / (n + 1) := by exact (div_self h).symm
  nth_rewrite 2 [← add_sub_cancel 1 n, sub_eq_add_neg]
  rw [← add_assoc, ← div_add_div_same]
  rw [add_comm 1 n, ← h1]
  rw [← one_mul (-1 / (n + 1)), mul_div_left_comm]
  simp
  rw [sub_eq_add_neg]

-- this holds also for a, b, c ∈ ℕ
lemma aux3 (a b c : ℚ) : a * (b/c) = b * (a/c) := by
  rw [mul_div_left_comm]

-- this holds also for a, b, c ∈ ℕ
lemma aux4 (a b c : ℚ) (h : c ≠ 0) : c * a = b ↔ a = b / c:= by
  rw [eq_div_iff_mul_eq, mul_comm]
  apply h

-- Now we use aux1 ... aux4 to prove that we can express Bin(2n, n)/(n+1) as a subtraction of two binomial coefficients
theorem binom_div_eq_sub_binom (n : ℕ) (h : 0 < n) : (Nat.choose (2 * n) n) - (Nat.choose (2 * n) (n + 1)) = 1 / (n + 1) * (Nat.choose (2 * n) n) := by
 have H1 : Nat.choose (2 * n) n - Nat.choose (2 * n) (n + 1) = 1 / (n + 1) * Nat.choose (2 * n) n ↔
           Nat.choose (2 * n) n - 1 / (n + 1) * Nat.choose (2 * n) n = Nat.choose (2 * n) (n + 1) := by sorry -- Holds by aux1
 rw [H1]
 nth_rewrite 1 [← one_mul (Nat.choose (2 * n) n)]
 rw [← Nat.mul_sub_right_distrib]
 have H2 : 1 - 1 / (n + 1) = n / (n + 1) := by sorry -- Holds by aux2
 rw [H2, mul_comm]
 have H3 : Nat.choose (2 * n) n * (n / (n + 1)) = n * (Nat.choose (2 * n) n / (n + 1)) := by sorry -- Holds by aux3
 rw [H3]
 have H4 : n * (Nat.choose (2 * n) n / (n + 1)) = Nat.choose (2 * n) (n + 1) ↔
          (Nat.choose (2 * n) n / (n + 1)) = Nat.choose (2 * n) (n + 1) / n := by sorry -- Holds by aux4
 rw [H4, binom_div_eq_binom_succ]
 . apply h
