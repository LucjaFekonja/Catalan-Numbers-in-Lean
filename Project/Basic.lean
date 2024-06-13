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
| 0 => 0
| (n + 1) => ∑ i : Fin n.succ, catalan_number i * catalan_number (n - i)


/- ================================ TASK 2: PLANE TREES DEFINITION ================================ -/
-- IDEA 1: Plane tree is completely specified by a number of subtrees.
inductive plane_tree1 : Type
| make_plane_tree : (n : ℕ) → (Fin n → plane_tree1) → plane_tree1

-- IDEA 2: Plane tree is defined with a list of children.
inductive plane_tree : Type
| make_plane_tree : List (plane_tree) → plane_tree


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

/- ================================= TASK 5: ROTATING ISOMORPHISM ================================= -/
-- Leaf of a full binary tree is a plane tree with an empty list of subnodes.
-- Other nodes have two subnodes, which are recursively mapped into a list of children of a plane tree.
def full_to_plane : full_binary_tree → plane_tree
| full_binary_tree.leaf => plane_tree.make_plane_tree []
| (full_binary_tree.join left right) => plane_tree.make_plane_tree [full_to_plane left, full_to_plane right]

-- Plane tree with an empty list of subnodes is mapped to a full binary tree with only one node - root.
-- Otherwise, list of subnodes is not empty, and we set head of a list as the left subnode and
-- everything else as the right, recurively calling plane_to_full on both sides.
def plane_to_full : plane_tree → full_binary_tree
| (plane_tree.make_plane_tree []) => full_binary_tree.leaf
| (plane_tree.make_plane_tree (h :: t)) =>
  full_binary_tree.join (plane_to_full h) (plane_to_full (plane_tree.make_plane_tree t))


/- ================================= TASK 6: Bin(2n, n) is divisible by n + 1 ================================= -/
-- Proof of 2n-n=n
theorem two_n_minus_n_is_n (n : ℕ) : (2 * n - n = n) := by
  nth_rewrite 2 [← one_mul n]
  rw [← Nat.mul_sub_right_distrib]
  ring

-- We can rewrite Bin(2n, n)/(n+1) as Bin(2n, n+1)/n.
theorem binom_div_eq_binom_succ (n : ℕ) (h : 0 < n) : (Nat.choose (2 * n) n) / (n + 1) = (Nat.choose (2 * n) (n + 1)) / n := by
 rw [choose_eq_factorial_div_factorial]
 . rw [two_n_minus_n_is_n, Nat.div_div_eq_div_mul, mul_assoc, mul_comm (n !), mul_comm (n !), ← Nat.factorial_succ]
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

-- Here is how we wanted to prove that Bin(2n, n)/(n+1) = Bin(2n, n) - Bin(2n, n+1):
-- Bin(2n, n+1) = Bin(2n, n) - Bin(2n, n)/(n+1)
--              = (1 - 1/(n+1)) Bin(2n, n)
--              = n/(n+1) Bin(2n, n)
-- Therefore Bin(2n, n+1)/n = Bin(2n, n)/(n+1), which is exactly theorem "binom_div_eq_binom_succ".

theorem binom_div_eq_sub_binom (n : ℕ) (h : 0 < n) : (Nat.choose (2 * n) n) - (Nat.choose (2 * n) (n + 1)) = 1 / (n + 1) * (Nat.choose (2 * n) n) := by
 -- rw [Nat.sub_eq_iff_eq_add, add_comm, ← Nat.sub_eq_iff_eq_add]
 -- nth_rewrite 1 [← one_mul (Nat.choose (2 * n) n)]
 -- rw [← Nat.mul_sub_right_distrib]
 sorry
