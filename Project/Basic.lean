import Mathlib
open Nat
open Rat
open BigOperators
open Finset
open Finset.antidiagonal

/- ================================================================================================ -/
/- =================================         SMALL TASKS         ================================== -/
/- ================================================================================================ -/

/- ============================== TASK 1: CATALAN NUMBERS DEFINITION ============================== -/
def catalan_number : ℕ → ℕ
| 0 => 0
| (n + 1) => ∑ i : Fin n.succ, catalan_number i * catalan_number (n - i)


/- ================================ TASK 2: PLANE TREES DEFINITION ================================ -/
/- IDEA 1: plane tree is completely specified by a number of subtrees -/
inductive plane_tree1 : Type
| make_plane_tree : (n : ℕ) → (Fin n → plane_tree1) → plane_tree1

/- IDEA 2: plane tree is defined with a list of children -/
inductive plane_tree : Type
| make_plane_tree : List (plane_tree) → plane_tree


/- ============================= TASK 3: FULL BINARY TREES DEFINITION ============================= -/
/- Nodes can only be zero or two branches -/
inductive full_binary_tree : Type
| root
| join : (T1 T2 : full_binary_tree) → full_binary_tree

/- Height of a full binary tree -/
def full_binary_tree.height : full_binary_tree → ℕ
| .root => 0
| .join T1 T2 => max T1.height T2.height + 1

/- Number of leaves of a full binary tree -/
def full_binary_tree.number_of_leaves : full_binary_tree → ℕ
| .root => 1
| .join T1 T2 => (number_of_leaves T1) + (number_of_leaves T2)

/- Number of nodes without leaves of a full binary tree -/
def full_binary_tree.number_of_internal_nodes : full_binary_tree → ℕ
| .root => 0
| .join T1 T2 => T1.number_of_internal_nodes + T2.number_of_internal_nodes + 1


/- ======================= TASK 4: FULL BINARY TREES WITH n NODES DEFINITION ====================== -/
inductive binary_tree_with_nodes : ℕ → Type
| root : binary_tree_with_nodes 1
| succ : {n : ℕ} → binary_tree_with_nodes n → binary_tree_with_nodes (n + 1)
| join : {n m : ℕ} → binary_tree_with_nodes n → binary_tree_with_nodes m → binary_tree_with_nodes (n + m + 1)

inductive full_binary_tree_with_nodes : ℕ → Type
| root : full_binary_tree_with_nodes 1
| join : {n m : ℕ} → full_binary_tree_with_nodes n → full_binary_tree_with_nodes m → full_binary_tree_with_nodes (n + m + 1)


/- ============================== TASK 5: BALLOT SEQUENCE DEFINITION ============================== -/
/- Sequence of votes where candidate A is always ahead or is tied with candidate B -/
/- There are equal number of As and Bs -/
/- We will use True to represent a vote for A and False to represent a vote for B -/
inductive ballot_sequence : List Bool → Prop
| empty : ballot_sequence []
| add_A (w : List Bool) (h : ballot_sequence w) : ballot_sequence (w ++ [tt])
| add_B (w : List Bool) (h : ballot_sequence w) (hw : w.count tt > w.count ff) : ballot_sequence (w ++ [ff])



/- ================================================================================================ -/
/- =================================         LARGE TASKS         ================================== -/
/- ================================================================================================ -/

/- ======================= TASK 4: BIJECTION List PLANE TREE == PLANE TREE ======================== -/
def bijection_list_plane_tree_and_plane_tree : List plane_tree ≃ plane_tree := Equiv.mk
  ( plane_tree.make_plane_tree )
  ( λ (plane_tree.make_plane_tree t) => t )
  ( λ _ => rfl )
  ( λ (plane_tree.make_plane_tree _) => rfl )


/- ================================= TASK 5: ROTATING ISOMORPHISM ================================= -/
def full_to_plane : full_binary_tree → plane_tree
| full_binary_tree.root => plane_tree.make_plane_tree []
| (full_binary_tree.join left right) => plane_tree.make_plane_tree [full_to_plane left, full_to_plane right]

def plane_to_full : plane_tree → full_binary_tree
| (plane_tree.make_plane_tree []) => full_binary_tree.root
| (plane_tree.make_plane_tree (h :: t)) =>
  full_binary_tree.join (plane_to_full h) (plane_to_full (plane_tree.make_plane_tree t))


/- ================================= TASK 6: Bin(2n, n) is divisible by n + 1 ================================= -/
-- Prove that 2n-n=n
theorem two_n_minus_n_is_n (n : ℕ) : (2 * n - n = n) := by
  nth_rewrite 2 [← one_mul n]
  rw [← Nat.mul_sub_right_distrib]
  ring

-- Prove that (2n choose n) is divisible by (n + 1)
theorem binom_divisible_by_n_plus_one (n : ℕ) : (Nat.choose (2 * n) n) / (n + 1) = (Nat.choose (2 * n) (n + 1)) / n := by
 rw [choose_eq_factorial_div_factorial]
 . rw [two_n_minus_n_is_n, Nat.div_div_eq_div_mul, mul_assoc, mul_comm (n !), mul_comm (n !), ← Nat.factorial_succ]
   nth_rewrite 3 [← Nat.mul_factorial_pred]





/- ================================================================================================ -/
/- ============================         AUXILIARY DEFINITIONS         ============================= -/
/- ================================================================================================ -/

/- ======================  BINARY TREES  ====================== -/
/- Induktivno generirane: root (.), succ(T - .). jount (T1 - . - T2) -/
inductive binary_tree : Type
| root
| succ : binary_tree → binary_tree
| join : (T1 T2 : binary_tree) → binary_tree

/- The height of binary tree -/
def binary_tree.height : binary_tree -> ℕ
| .root => 0
| .succ T => T.height + 1
| .join T1 T2 => max T1.height T2.height + 1

/- The number of leaves in binary tree -/
def binary_tree.number_of_leaves : binary_tree → ℕ
| .root => 1
| .succ T => T.number_of_leaves
| .join T1 T2 => T1.number_of_leaves + T2.number_of_leaves


/- ======================  FULL BINARY TREES AND BINARY TREES CONVERSTION  ====================== -/
/- Converting a binary tree into a full binary tree, by forgetting its unary branching -/
def binary_to_full : binary_tree → full_binary_tree
| .root => .root
| .succ T => (binary_to_full T)
| .join T1 T2 => .join (binary_to_full T1) (binary_to_full T2)

/- Converting a full binary tree into a binary tree -/
def full_to_binary : full_binary_tree → binary_tree
| .root => .root
| .join T1 T2 => .join (full_to_binary T1) (full_to_binary T2)


/- ======================  PROOF: HEIGHTS OF FULL BINARY AND BINARY TREES ARE EQUAL  ====================== -/
/- First way: -/
/- Razdeli na root (rfl) in join (rewrite + induction) case -/
def eq_height_binary_tree_of_full_binary_tree :
  (T : full_binary_tree) →
  T.height = (full_to_binary T).height := by
intro T
induction' T with T1 T2 T1_H T2_H
. rfl
simp [full_binary_tree.height]
simp [binary_tree.height]
rw [T1_H, T2_H]

/- Second way: -/
def eq_height_binary_tree_of_full_binary_tree' :
  (T : full_binary_tree) →
  T.height = (full_to_binary T).height := by
intro T
induction T with
| root => rfl
| join T1 T2 HT1 HT2 =>
  simp [full_binary_tree.height, binary_tree.height]
  rw [HT1, HT2]


/- ======================  PROOF: FULL BINARY AND BINARY TREES HAVE SAME NUMBER OF LEAVES  ====================== -/
def eq_number_of_leaves_binary_tree_of_full_binary_tree :
  (T : full_binary_tree) →
  T.number_of_leaves = (full_to_binary T).number_of_leaves := by
  intro T
  induction T with
  | root => rfl
  | join T1 T2 HT1 HT2 =>
  simp [full_binary_tree.number_of_leaves, binary_tree.number_of_leaves]
  rw [HT1, HT2]


/- ======================  BINARY TREES WITH NODES  ====================== -/
/- Convert binary tree with nodes to a binary tree -/
def binary_tree_of_binary_tree_with_nodes (n : ℕ) : binary_tree_with_nodes n → binary_tree
| .root => .root
| .succ T => .succ (binary_tree_of_binary_tree_with_nodes _ T)
| .join T1 T2 => .join (binary_tree_of_binary_tree_with_nodes _ T1) (binary_tree_of_binary_tree_with_nodes _ T2)




/- def plane_to_full : plane_tree → full_binary_tree
| (plane_tree.make_plane_tree []) => full_binary_tree.root
| (plane_tree.make_plane_tree [t]) => full_binary_tree.join (plane_to_full t) full_binary_tree.root
| (plane_tree.make_plane_tree subtrees) => full_binary_tree.join
    (plane_to_full (.make_plane_tree (List.take (List.length subtrees / 2) subtrees)))
    (plane_to_full (.make_plane_tree (List.drop (List.length subtrees / 2) subtrees))) -/

/- Reference: Richard Stanley, Catalan Numbers -/
/- Use: List (A) izomorfno 1 + A + List(A) -/
/-      List(plane_tree) izomorfno plane_tree -/
/- => List(plane_tree) == 1 + plane_tree + List(plane_tree) == 1 + plane_tree^2 = full_binary_tree-/


/- ======================  CATALAN NUMBERS  ====================== -/
/- Deduce than Cn is the number of full binary trees with n nodes (excluding the leaves)
def num_of_full_binary_to_catalan (n : ℕ) : List (full_binary_trees) → Fin (catalan_numbers n)
| {} => Fin 0
|  => _ -/

def num_full_binary_trees : ℕ → ℕ
| 0 => 1
| 1 => 1
| (n + 2) => ∑ i : Fin (n + 1), num_full_binary_trees i * num_full_binary_trees (n - i)



-- theorem full_binary_trees_catalan_eq : ∀ (n : ℕ), catalan_number n = num_full_binary_trees n := by
--   -- We'll prove this by induction on n
--   intro n
--   induction n with
--   | 0 =>
--     simp [catalan_number, num_full_binary_trees]
--   | (n + 1) =>
--    -- Inductive step: Assume it holds for n, prove it for n + 1
--     -- We need to show catalan_number (n + 1) = num_full_binary_trees (n + 1)
--
--     -- We start by expanding the sum in catalan_number (n + 1)
--     rw catalan_number,
--     -- We need to prove that the sum of catalan numbers up to n is the same as the number of full binary trees up to n
--     rw sum_congr rfl,
--     intro i,
--     -- Now we unfold the definition of num_full_binary_trees
--     rw [num_full_binary_trees],
--     -- The number of full binary trees with i nodes as left subtree and n - i nodes as right subtree is F_i * F_(n - i)
--     rw [←ih i, ←ih (n - i)],
--     -- So, the sum becomes the sum of all such combinations
--     rw [←sum_mul_sum],
--     -- Which is the definition of the (n + 1)th Catalan number
--     refl,
