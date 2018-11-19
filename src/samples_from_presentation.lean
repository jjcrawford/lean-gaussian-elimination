import ring_theory.matrix
import tactic.linarith
theorem and_commutative {p q : Prop} : p ∧ q → q ∧ p :=
begin
    intro h,
    cases h with hp hq,
    constructor,
    repeat {assumption},
end

namespace example1

inductive or (p q : Prop) : Prop
| mk_left  : p → or
| mk_right : q → or

example {p q : Prop} : or p q → or q p:=
begin
    intro h,
    cases h with hp hq,
    from or.mk_right _ hp,
    from or.mk_left _ hq,
end

inductive binary_tree (α : Type)
| leaf : α → binary_tree
| node : α → binary_tree → binary_tree → binary_tree

def sum_tree {α : Type} [field α] : (binary_tree α) → α
| (binary_tree.leaf a) := a
| (binary_tree.node a t₁ t₂) := a + (sum_tree t₁) + (sum_tree t₂)

--variables {m n : ℕ} {α : Type} [field α]

def scale {α : Type} [field α] {m : ℕ} (i₁ : fin m) (s : α) (hs : s ≠ 0) : (matrix (fin m) (fin m) α) := 
λ i j, if (i = j) then (if (i = i₁) then s else 1) else 0

def swap {α : Type} [field α] {m : ℕ} (i₁ i₂ : fin m) : (matrix (fin m) (fin m) α) := 
λ i j, if (i = i₁) then (if i₂ = j then 1 else 0) else if (i = i₂) then (if i₁ = j then 1 else 0) else if (i = j) then 1 else 0

def linear_add {α : Type} [field α] {m : ℕ} (i₁ : fin m) (s : α) (i₂ : fin m) (h : i₁ ≠ i₂) : (matrix (fin m) (fin m) α) := 
λ i j, if (i = i₁) then (if i₂ = j then 1 else 0) else if (i = i₂) then (if i₁ = j then 1 else 0) else if (i = j) then 1 else 0


variables {m n : ℕ} {α : Type} [field α]

def is_scale (M : matrix (fin m) (fin m) α) : Prop := ∃ (i₁ : fin m) (s : α) (hs : s ≠ 0), M = scale i₁ s hs
def is_swap (M : matrix (fin m) (fin m) α) : Prop := ∃ (i₁ i₂ : fin m), M = swap i₁ i₂
def is_linear_add (M : matrix (fin m) (fin m) α) : Prop := ∃ (i₁ i₂ : fin m) (s : α) (h : i₁ ≠ i₂), M = linear_add i₁ s i₂ h

def is_row_operation (M : matrix (fin m) (fin m) α) := is_scale M ∨ is_swap M ∨ is_linear_add M

class row_equivalence (M N : (matrix (fin m) (fin n) α)) :=
(steps : list (matrix (fin m) (fin m) α))
(steps_implement : list.foldr (matrix.mul) M steps = N)
(steps_row_operations : ∀ (k : fin steps.length), is_row_operation (list.nth_le steps k.val (k.is_lt)))


def example_algorithm (M : matrix (fin m) (fin n) α) (i₁ i₂ : fin m) : (matrix (fin m) (fin n) α) :=
begin
    from (swap i₁ i₂).mul M
end

example {M : matrix (fin m) (fin n) α} {i₁ i₂ : fin m} : row_equivalence M (example_algorithm M i₁ i₂) :=
begin
    constructor,
    show list _,
    from list.cons (swap i₁ i₂) list.nil, -- Provide the list. Easy.
    refl, -- Prove that folding the list achieves the right result. Easy.
    intros,
    apply or.inr,
    apply or.inl, -- Unfolding is_row_operation to get is_swap as the goal
    constructor,
    constructor,
    show fin m, from i₂,
    show fin m, from i₁, --Instantiate the ∃ in is_swap with our indices
    simp,
    have k_eq_zero : k.val = 0, -- I have to prove that < 1 → k.val = 0
    cases k,                    -- just so I can prove that the kth elmt
    simp,                       -- in the list is also the zeroth elmt
    cases k_val,                -- so that I can simplify the statement
    simp,           -- ⊢ list.nth_le [swap i₁ i₂] (k.val) _ = swap i₁ i₂
    exfalso,                  -- to ⊢ swap i₁ i₂ = swap i₁ i₂
    from nat.not_lt_zero k_val (nat.lt_of_succ_lt_succ k_is_lt),
    have H₁ : list.nth_le [swap i₁ i₂] (k.val) _ = list.nth_le [swap i₁ i₂] (0) _,
    congr,
    assumption,
    rw H₁,
    simp, -- There we go
    simp,
    from nat.zero_lt_succ 0 -- and a proof that 0 < 1, for some reason.
end



def scaled (M : matrix (fin m) (fin n) α) (i₁ : fin m) (s : α) (hs : s ≠ 0) : matrix (fin m) (fin n) α :=
    (λ i j, if (i = i₁) then (s * (M i₁ j)) else (M i j))

def swapped (M : matrix (fin m) (fin n) α) (i₁ i₂ : fin m) : matrix (fin m) (fin n) α :=
    (λ i j, if (i=i₁) then M i₂ j else if (i=i₂) then M i₁ j else M i j)

def linear_added (M : matrix (fin m) (fin n) α) (i₁ : fin m) (s : α) (i₂ : fin m) : matrix (fin m) (fin n) α :=
    (λ i j, if (i=i₁) then (M i j) + (s * (M i₂ j)) else M i j)

inductive row_equivalent_step : matrix (fin m) (fin n) α → matrix (fin m) (fin n) α → Type
| scale : Π (M : matrix (fin m) (fin n) α) (i₁ : fin m) (s : α) (hs : s ≠ 0), 
    row_equivalent_step M (scaled M i₁ s hs)
| swap : Π (M : matrix (fin m) (fin n) α) (i₁ i₂ : fin m), 
    row_equivalent_step M (swapped M i₁ i₂)
| linear_add : Π (M : matrix (fin m) (fin n) α) (i₁ : fin m) (s : α) (i₂ : fin m) (h : i₁ ≠ i₂), 
    row_equivalent_step M (linear_added M i₁ s i₂)

def row_equivalent_step.elementary : 
    Π {M N :  matrix (fin m) (fin n) α}, row_equivalent_step M N → matrix (fin m) (fin m) α
| M _ (row_equivalent_step.scale _ i₁ s h) := scale i₁ s h
| M _ (row_equivalent_step.swap _ i₁ i₂) := swap i₁ i₂
| M _ (row_equivalent_step.linear_add _ i₁ s i₂ h) := linear_add i₁ s i₂ h

inductive row_equivalent : matrix (fin m) (fin n) α → matrix (fin m) (fin n) α → Type
| nil : Π {N M : matrix (fin m) (fin n) α} (h : row_equivalent_step N M), row_equivalent N M
| cons : Π {N M L : matrix (fin m) (fin n) α} (h₁ : row_equivalent N M) (h₂ : row_equivalent_step M L), row_equivalent N L


def elementary_implements : -- This is actually not trivial, but let's assume we've shown it.
  Π {M N :  matrix (fin m) (fin n) α} (h : row_equivalent_step M N),  matrix.mul (row_equivalent_step.elementary h) M = N 
    := sorry

example {M : matrix (fin m) (fin n) α} {i₁ i₂ : fin m} : row_equivalent M (example_algorithm M i₁ i₂) :=
begin
    constructor, -- Construct a row_equivalent from a row_equivalent_step
    dsimp[example_algorithm], -- Unfolds the algorithm as a swap statement
    have H₁, from elementary_implements (row_equivalent_step.swap M i₁ i₂),
    dsimp[row_equivalent_step.elementary] at H₁,
    rw H₁, -- Rewrite the (M.mul swap i₁ i₂) in the goal as (swapped M i₁ i₂) 
    from row_equivalent_step.swap M i₁ i₂, -- yields row_equivalent M (swapped M i₁ i₂)
end


def example_algorithm2 (M : matrix (fin m) (fin n) α) (i₁ i₂ : fin m) : (matrix (fin m) (fin n) α) :=
(row_equivalent_step.swap M i₁ i₂).elementary.mul M

example {M : matrix (fin m) (fin n) α} {i₁ i₂ : fin m} : row_equivalent M (example_algorithm2 M i₁ i₂) :=
begin
    constructor, -- Construct a row_equivalent from a row_equivalent_step
    dsimp[example_algorithm2], -- Unfolds the algorithm as a swap statement
    rw elementary_implements, -- We can now jump straight to a rw
    apply row_equivalent_step.swap, -- ⊢ row_equivalent_step M (swapped M i₁ i₂)
end

end example1

namespace example2

universes u
variables {m n : ℕ} (α : Type u) [ring α] [decidable_eq α]

inductive elementary (m : ℕ)
| scale : Π (i₁ : fin m) (s : α) (hs : s ≠ 0), elementary
| swap : Π (i₁ i₂ : fin m), elementary
| linear_add : Π (i₁ : fin m) (s : α) (i₂ : fin m) (h : i₁ ≠ i₂), elementary

variable {α}
def elementary.to_matrix {m : ℕ} : elementary α m → matrix (fin m) (fin m) α
| (elementary.scale i₁ s hs) := λ i j, if (i = j) then (if (i = i₁) then s else 1) else 0
| (elementary.swap _ i₁ i₂) :=  λ i j, if (i = i₁) then (if i₂ = j then 1 else 0) else if (i = i₂) then (if i₁ = j then 1 else 0) else if (i = j) then 1 else 0--if (i ≠i₁ ∧i ≠i₂) then (if i = j then 1 else 0) else (if i = i₁ then (if i₂ = j then 1 else 0) else (if i₁ = j then 1 else 0))
| (elementary.linear_add i₁ s i₂ h) := λ i j, if (i = j) then 1 else if (i = i₁) then if (j = i₂) then s else 0 else 0

def elementary.apply :  elementary α m →  (matrix (fin m) (fin n) α) →  matrix (fin m) (fin n) α
| (elementary.scale i₁ s hs) M := λ i j, if (i = i₁) then s * M i j else M i j
| (elementary.swap _ i₁ i₂) M := λ i j, if (i = i₁) then M i₂ j else if (i = i₂) then M i₁ j else M i j
| (elementary.linear_add i₁ s i₂ h) M := λ i j, if (i = i₁) then M i j + s * M i₂ j else M i j

structure row_equivalent_step (M N : matrix (fin m) (fin n) α) :=
(elem : elementary α m)
(implements : matrix.mul (elem.to_matrix) M = N)

inductive row_equivalent : matrix (fin m) (fin n) α → matrix (fin m) (fin n) α → Type u
| nil : Π {N : matrix (fin m) (fin n) α}, row_equivalent N N
| cons : Π {N M L : matrix (fin m) (fin n) α} (h₁ : row_equivalent N M) (h₂ : row_equivalent_step M L), row_equivalent N L

lemma elementary.mul_eq_apply : 
  Π {M : matrix (fin m) (fin n) α} (e : elementary α m), ((e.to_matrix).mul M) = (e.apply M) :=
    sorry -- We still haven't handled this yet. It will come.

def row_equivalent_step.of_elementary : 
  Π {M : matrix (fin m) (fin n) α} (e : elementary α m), row_equivalent_step M ((e.to_matrix).mul M) :=
    λ _ _, ⟨_, by refl⟩

def row_equivalent_step.of_elementary_apply : 
  Π {M : matrix (fin m) (fin n) α} (e : elementary α m), row_equivalent_step M (e.apply M) :=
begin
  intros,
  rw ←elementary.mul_eq_apply,
  apply row_equivalent_step.of_elementary
end


def example_algorithm3 (M : matrix (fin m) (fin n) α) (i₁ i₂ : fin m) : (matrix (fin m) (fin n) α) :=
(elementary.swap α i₁ i₂).to_matrix.mul M

example {M : matrix (fin m) (fin n) α} {i₁ i₂ : fin m} : row_equivalent M (example_algorithm3 M i₁ i₂) :=
begin
    constructor, constructor,
    unfold example_algorithm3,
    apply row_equivalent_step.of_elementary,
end

lemma finset.sum_ite_zero 
  {α : Type*} [fintype α] [decidable_eq α] (a₀ : α) {β : Type*} [add_comm_monoid β] [decidable_eq β] (f : α → β) :
  finset.sum finset.univ (λ a, ite (a₀ = a) (f a) 0) = f a₀ := sorry



@[simp] lemma mul_swap_swapped_1 {i₁ i₂ : fin m} {j : fin n} {M : matrix (fin m) (fin n) α} : 
  (matrix.mul (elementary.swap _ i₁ i₂).to_matrix M) i₁ j = M i₂ j := sorry

@[simp] lemma mul_swap_swapped_2 {i₁ i₂ : fin m} {j : fin n} {M : matrix (fin m) (fin n) α} : 
  (matrix.mul (elementary.swap _ i₁ i₂).to_matrix M) i₂ j = M i₁ j := sorry

@[simp] lemma mul_linear_add_added {i₁ i₂ : fin m} {s : α} {j : fin n} {h : i₁ ≠ i₂} {M : matrix (fin m) (fin n) α} : 
  (matrix.mul (elementary.linear_add i₁ s i₂ h).to_matrix M) i₁ j = M i₁ j + s * M i₂ j := sorry

end example2