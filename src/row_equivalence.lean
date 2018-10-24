import ring_theory.matrix
import .finset_sum

open relation

universes u v
variables {m n : ℕ}
variable (α : Type u)
variable [ring α]
variable [decidable_eq α]

inductive elementary (m : ℕ)
| scale : Π (i₁ : fin m) (s : α) (hs : s ≠ 0), elementary
| swap : Π (i₁ i₂ : fin m), elementary
| linear_add : Π (i₁ : fin m) (s : α) (i₂ : fin m) (h : i₁ ≠ i₂), elementary

variable {α}
def elementary.to_matrix {m : ℕ} : elementary α m → matrix (fin m) (fin m) α
| (elementary.scale i₁ s hs) := λ i j, if (i = j) then (if (i = i₁) then s else 1) else 0
| (elementary.swap _ i₁ i₂) :=  λ i j, if (i = i₁) then (if i₂ = j then 1 else 0) else if (i = i₂) then (if i₁ = j then 1 else 0) else if (i = j) then 1 else 0--if (i ≠i₁ ∧i ≠i₂) then (if i = j then 1 else 0) else (if i = i₁ then (if i₂ = j then 1 else 0) else (if i₁ = j then 1 else 0))
| (elementary.linear_add i₁ s i₂ h) := λ i j, if (i = j) then 1 else if (i = i₁) then if (j = i₂) then s else 0 else 0
-- λ i j, if (i = j) then (if i = i₁ then s else 1) else 0 
--λ i j, if (i ≠ i) then (if i = j then 1 else 0) else (if j = i₁ then 1 else if j = i₂ then s else 0)

def elementary.apply :  elementary α m →  (matrix (fin m) (fin n) α) →  matrix (fin m) (fin n) α
| (elementary.scale i₁ s hs) M := λ i j, if (i = i₁) then s * M i j else M i j
| (elementary.swap _ i₁ i₂) M := λ i j, if (i = i₁) then M i₂ j else if (i = i₂) then M i₁ j else M i j
| (elementary.linear_add i₁ s i₂ h) M := λ i j, if (i = i₁) then M i j + s * M i₂ j else M i j

structure row_equivalent_step (M N : matrix (fin m) (fin n) α) :=
(elem : elementary α m)
(implements : matrix.mul (elem.to_matrix) M = N)


-- #exit

@[simp] lemma mul_scale_scaled {i : fin m} {j : fin n} {s : α} {h : s ≠ 0} {M : matrix (fin m) (fin n) α} : 
  (matrix.mul (elementary.scale i s h).to_matrix M) i j = s * M i j :=
begin
  dsimp [matrix.mul],
  dsimp [elementary.to_matrix],
  simp,
  rw finset.sum_ite_zero,
end

@[simp] lemma mul_swap_swapped_1 {i₁ i₂ : fin m} {j : fin n} {M : matrix (fin m) (fin n) α} : 
  (matrix.mul (elementary.swap _ i₁ i₂).to_matrix M) i₁ j = M i₂ j :=
begin
  rw matrix.mul,
  dsimp [elementary.to_matrix],
  simp,
  rw finset.sum_ite_zero,
end

#check decidable_of_decidable_of_iff

@[simp] lemma decidable_of_decidable_of_iff_refl {p : Prop} (hp : decidable p) (h : p ↔ p) :
  decidable_of_decidable_of_iff hp h = hp :=
begin
  dsimp [decidable_of_decidable_of_iff],
  tactic.unfreeze_local_instances,
  cases hp,
  dsimp [dite],
  refl,
  dsimp [dite],
  refl,
end

-- set_option pp.implicit true
@[simp] lemma mul_swap_swapped_2 {i₁ i₂ : fin m} {j : fin n} {M : matrix (fin m) (fin n) α} : 
  (matrix.mul (elementary.swap _ i₁ i₂).to_matrix M) i₂ j = M i₁ j :=
begin
  dsimp [matrix.mul],
  dsimp [elementary.to_matrix],
  simp,
  by_cases h : (i₂ = i₁);
  simp[h],
    swap,
    rw finset.sum_ite_zero,
    -- simp,
    cases h,
    conv { -- This is still gross, and we should ask for help...
      congr,congr,skip,funext,
      rw decidable_of_decidable_of_iff_refl,
      rw decidable_of_decidable_of_iff_refl,
    },
    rw finset.sum_ite_zero,
  -- can't believe this is necessary
  -- have H₁ : (@finset.sum (fin m) α (@semiring.to_add_comm_monoid α (@ring.to_semiring α _inst_1))
  --     (@finset.univ (fin m) (fin.fintype m))
  --     (λ (x : fin m),
  --        @ite (i₁ = x)
  --          (@decidable_of_decidable_of_iff (i₂ = x) (i₁ = x)
  --             (@decidable_of_decidable_of_iff (i₂ = x) (i₂ = x) (fin.decidable_eq m i₂ x) _)
  --             _)
  --          α
  --          (M x j)
  --          0) =
  --   M i₁ j) = (@finset.sum (fin m) α (@semiring.to_add_comm_monoid α (@ring.to_semiring α _inst_1))
  --     (@finset.univ (fin m) (fin.fintype m))
  --     (λ (x : fin m),
  --        @ite (i₁ = x) (@decidable_of_decidable_of_iff (i₁ = x) (i₁ = x) (fin.decidable_eq m i₁ x) _) α (M x j)
  --          0) =
  --   M i₁ j),
  --   congr,
  --   funext,
  --   by_cases h₂ : (i₁ = x);
  --   simp[h₂],
  --   rw H₁,
  --   show i₁ = x ↔ i₁ = x, refl,
  -- --   --
  --   repeat{rw finset.sum_ite_zero},
end

  
  -- set_option pp.all true
@[simp] lemma mul_linear_add_added {i₁ i₂ : fin m} {s : α} {j : fin n} {h : i₁ ≠ i₂} {M : matrix (fin m) (fin n) α} : (matrix.mul (elementary.linear_add i₁ s i₂ h).to_matrix M) i₁ j = M i₁ j + s * M i₂ j := 
begin
  dsimp[matrix.mul],
  dsimp[elementary.to_matrix],
  simp,
  -- have H₁ : (λ (x : fin m), ite (i₁ = x) (M x j) (ite (x = i₂) (s * M x j) 0)) = (λ (x : fin m), ite (i₁ = x) (M x j) (ite (i₂ = x) (s * M x j) 0)),
  -- funext,
  -- by_cases h₁ : (i₁ = x); simp[h₁],
  -- by_cases h₂ : (x = i₂); simp[h₂],
  -- simp[λ x, h₂ (eq.symm x)],
  have H₁ : finset.sum finset.univ (λ (x : fin m), ite (i₁ = x) (M x j) (ite (x = i₂) (s * M x j) 0)) = finset.sum finset.univ (λ (x : fin m), ite (i₁ = x) (M x j) (ite (i₂ = x) (s * M x j) 0)),
  congr,
  funext,
  by_cases h₁ : (i₁ = x); simp[h₁],
  by_cases h₂ : (x = i₂); simp[h₂],
  simp[λ x, h₂ (eq.symm x)],
  apply eq.trans,
  show α, from finset.sum finset.univ (λ (x : fin m), ite (i₁ = x) (M x j) (ite (i₂ = x) (s * M x j) 0)),

  -- from H₁,
-- erw H₁,
  
  have H₂ : (@finset.sum (fin m) α
      (@semimodule.to_add_comm_monoid α α (@ring.to_semiring α _inst_1)
         (@semiring.to_semimodule α (@ring.to_semiring α _inst_1)))
      (@finset.univ (fin m) (fin.fintype m))
      (λ (x : fin m),
         @ite (i₁ = x) (fin.decidable_eq m i₁ x) α (M x j)
           (@ite (x = i₂) (fin.decidable_eq m x i₂) α (s * M x j) 0)) =
    @finset.sum (fin m) α
      (@semimodule.to_add_comm_monoid α α (@ring.to_semiring α _inst_1)
         (@semiring.to_semimodule α (@ring.to_semiring α _inst_1)))
      (@finset.univ (fin m) (fin.fintype m))
      (λ (x : fin m),
         @ite (i₁ = x) (fin.decidable_eq m i₁ x) α (M x j)
           (@ite (i₂ = x) (fin.decidable_eq m i₂ x) α (s * M x j) 0))
)=(
  @finset.sum (fin m) α
      (@semimodule.to_add_comm_monoid α α (@ring.to_semiring α _inst_1)
         (@semiring.to_semimodule α (@ring.to_semiring α _inst_1)))
      (@finset.univ (fin m) (fin.fintype m))
      (λ (x : fin m),
         @ite (i₁ = x)
           (@decidable_of_decidable_of_iff (i₁ = x) (i₁ = x)
              (@decidable_of_decidable_of_iff (i₁ = x) (i₁ = x) (fin.decidable_eq m i₁ x) _)
              _)
           α
           (M x j)
           (@ite (x = i₂) (@decidable_of_decidable_of_iff (x = i₂) (x = i₂) (fin.decidable_eq m x i₂) _) α
              (s * M x j)
              0)) =
    @finset.sum (fin m) α
      (@semimodule.to_add_comm_monoid α α (@ring.to_semiring α _inst_1)
         (@semiring.to_semimodule α (@ring.to_semiring α _inst_1)))
      (@finset.univ (fin m) (fin.fintype m))
      (λ (x : fin m),
         @ite (i₁ = x) (fin.decidable_eq m i₁ x) α (M x j)
           (@ite (i₂ = x) (fin.decidable_eq m i₂ x) α (s * M x j) 0))),
  
  congr,
  funext,
  by_cases h₁ : (i₁ = x); simp[h₁],
  by_cases h₂ : (x = i₂); simp[h₂],
  simp[H₂] at H₁,
  from H₁,
  clear H₁,
  have H₁, from @finset.sum_ite_zero₂ (fin m) _ _ i₁ i₂ α _ _ (λ i, M i j) (λ i, s * (M i j)) h,
  simp at H₁,
  apply eq.trans,
  from H₁,
  simp,
end

lemma row_equivalent_step.mul_eq_apply : Π {M : matrix (fin m) (fin n) α} (e : elementary α m), ((e.to_matrix).mul M) =  (e.apply M) :=
begin
  intros,
  cases e with i₁ s hs i₁ i₂ i₁ s i₂,
  -- scale case
  by {
    funext i j,
    simp[matrix.mul,elementary.apply,elementary.to_matrix,finset.sum_ite_zero],
    by_cases h : (i = i₁); simp[h],
  },

  -- swap case
  by {
    funext i j,
    by_cases h : (i = i₁),
    simp[h, elementary.apply],
    by_cases h₁ : (i = i₂),
    simp[h₁, elementary.apply],
    rw ←h₁,
    repeat{simp[h, h₁, matrix.mul, elementary.apply,elementary.to_matrix, finset.sum_ite_zero]}
  },

 -- linear_add case
 by {
  funext i j,
  by_cases h : (i = i₁),
  simp[h,elementary.apply],
  simp[matrix.mul, elementary.apply, elementary.to_matrix, h,finset.sum_ite_zero],
 }
end


lemma row_equivalent_step.of_elementary : 
  Π {M : matrix (fin m) (fin n) α} (e : elementary α m), row_equivalent_step M ((e.to_matrix).mul M) :=
begin
  intros,
  cases e; 
  {constructor,
  refl}
end

lemma row_equivalent_step.of_elementary_apply : 
  Π {M : matrix (fin m) (fin n) α} (e : elementary α m), row_equivalent_step M (e.apply M) :=
begin
  intros,
  have H₃ : row_equivalent_step M (elementary.apply e M) = row_equivalent_step M (matrix.mul (elementary.to_matrix e) M),
  congr,
  from eq.symm(@row_equivalent_step.mul_eq_apply m n α _ _ M e),
  rw H₃,
  from @row_equivalent_step.of_elementary m n α _ _ M e,
end

def row_equivalent_step.to_matrix : 
  Π {M N : matrix (fin m) (fin n) α} (r : row_equivalent_step M N), matrix (fin m) (fin m) α :=
λ M N r, r.elem.to_matrix

def row_equivalent_step.apply : 
  Π (L : matrix (fin m) (fin n) α) {M N : matrix (fin m) (fin n) α} (r : row_equivalent_step M N), matrix (fin m) (fin n) α :=
λ L M N r, r.elem.apply L

-- def row_equivalent_step.of_elementary : Π 

@[simp] lemma row_equivalent_step.matrix_implements : Π {M N : matrix (fin m) (fin n) α} (r : row_equivalent_step M N), (r.to_matrix).mul M = N :=
begin
  intros,
  cases r with elem implements,
  unfold row_equivalent_step.to_matrix,
  simp,
  assumption
end

@[simp] lemma row_equivalent_step.apply_implements : Π {M N : matrix (fin m) (fin n) α} (r : row_equivalent_step M N), r.apply M = N :=
begin
  intros,
  cases r with elem implements,
  unfold row_equivalent_step.apply,
  simp,
  rw ←row_equivalent_step.mul_eq_apply,
  assumption,
end

inductive row_equivalent : matrix (fin m) (fin n) α → matrix (fin m) (fin n) α → Type u
| nil : Π {N : matrix (fin m) (fin n) α}, row_equivalent N N
| cons : Π {N M L : matrix (fin m) (fin n) α} (h₁ : row_equivalent N M) (h₂ : row_equivalent_step M L), row_equivalent N L

def row_equivalent.to_matrix : Π {M N : matrix (fin m) (fin n) α} (r : row_equivalent M N), matrix (fin m) (fin m) α 
| M N (row_equivalent.nil) := (1  : matrix (fin m) (fin m) α)
| M N (row_equivalent.cons r₁ r₂) := (row_equivalent_step.to_matrix r₂).mul (row_equivalent.to_matrix r₁)

def row_equivalent.apply (L : matrix (fin m) (fin n) α) : Π {M N : matrix (fin m) (fin n) α} (r : row_equivalent M N), matrix (fin m) (fin n) α
| M N (row_equivalent.nil) := L
| M N (row_equivalent.cons r₁ r₂) := (@elementary.apply m n α _ _ (row_equivalent_step.elem r₂)) (row_equivalent.apply r₁)

@[simp] lemma row_equiv_nil {M : matrix (fin m) (fin n) α} : row_equivalent.to_matrix (@row_equivalent.nil m n α _ _ M) = (1  : matrix (fin m) (fin m) α) := by simp[row_equivalent.to_matrix]

@[simp] lemma row_equiv_cons {M N L : matrix (fin m) (fin n) α} {r₁ : row_equivalent N M} {r₂ : row_equivalent_step M L}: row_equivalent.to_matrix (@row_equivalent.cons m n α _ _ N M L r₁ r₂) = (row_equivalent_step.to_matrix r₂).mul (row_equivalent.to_matrix r₁) := by simp[row_equivalent.to_matrix]

@[simp] lemma row_equivalent.matrix_implements : Π {M N : matrix (fin m) (fin n) α} (r : row_equivalent M N), (r.to_matrix).mul M = N 
| M N (row_equivalent.nil) := by simp[row_equiv_nil, matrix.one_mul]
| M N (row_equivalent.cons r₁ r₂) := begin
  rw row_equiv_cons,
  rw matrix.mul_assoc,
  rw row_equivalent.matrix_implements,
  apply row_equivalent_step.matrix_implements,
end

-- set_option pp.all true
@[simp] lemma row_equivalent.apply_implements : Π {M N : matrix (fin m) (fin n) α} (r : row_equivalent M N), r.apply M = N 
| M N (row_equivalent.nil) := by simp[row_equivalent.apply]
| M N (@row_equivalent.cons _ _ _ _ _ _ L _ r₁ r₂) := begin
  simp[row_equivalent.apply],
  have H₁, from row_equivalent.apply_implements r₁,
  have H₂ : elementary.apply (r₂.elem) (row_equivalent.apply M r₁) = elementary.apply (r₂.elem) L,
  congr,
  from H₁,
  rw H₂,
  apply row_equivalent_step.apply_implements,
end

theorem row_equivalent.mul_eq_apply : Π {M N : matrix (fin m) (fin n) α} (r₁ : row_equivalent M N), r₁.to_matrix.mul M = r₁.apply M :=
begin
  intros,
  cases r₁,
  simp[row_equivalent.to_matrix, row_equivalent.apply, matrix.one_mul],
  simp[row_equivalent.to_matrix, matrix.mul_assoc],
end
























#exit

inductive row_equivalent_step : matrix (fin m) (fin n) α → matrix (fin m) (fin n) α → Type u
| scale : Π (a : matrix (fin m) (fin n) α) (i₁ : fin m) (s : α) (hs : s ≠ 0), row_equivalent_step a (λ i j, if (i = i₁) then (s * (a i₁ j)) else (a i j))
| swap : Π (a : matrix (fin m) (fin n) α) (i₁ i₂ : fin m), row_equivalent_step a (λ i j, if (i=i₁) then a i₂ j else if (i=i₂) then a i₁ j else a i j)
| linear_add : Π (a : matrix (fin m) (fin n) α) (i₁ : fin m) (s : α) (i₂ : fin m) (h : i₁ ≠ i₂), row_equivalent_step a (λ i j, if (i=i₁) then (a i j) + (s * (a i₂ j)) else a i j)
| absurd : Π (M₁ M₂ : matrix (fin m) (fin n) α) (h_z : m = 0), row_equivalent_step M₁ M₂

namespace row_equivalent_step
def elementary : Π {M N :  matrix (fin m) (fin n) α}, row_equivalent_step M N → matrix (fin m) (fin m) α
| M _ (scale _ i₁ s h) := λ i j, if (i.val=j.val) then (if (i.val = i₁.val) then s else 1) else 0
| M _ (swap _ i₁ i₂) := λ i j, if (i.val≠i₁.val∧i.val≠i₂.val) then (if i.val=j.val then 1 else 0) else (if i.val = i₁.val then (if i₂.val = j.val then 1 else 0) else (if i₁.val = j.val then 1 else 0))
| M _ (linear_add _ i₁ s i₂ h₁) := λ i j, if (i.val ≠ i₁.val) then (if i.val = j.val then 1 else 0) else (if j.val = i₁.val then 1 else if j.val = i₂.val then s else 0)
| M₁ M₂ (absurd _ _ _) := λ i j, 0

@[simp] lemma elementary_scale_scaled {M : matrix (fin m) (fin n) α} {i j : fin m} {s : α} {h : s≠0}: elementary (scale M i s h) i j = s * M i j := rfl

-- Needs to take a (fin m) as proof that the matrix actually has any rows, otherwise row_equivalent_step isn't well-defined
def refl : Π (M : matrix (fin m) (fin n) α), row_equivalent_step M M :=
begin -- need to clean this up
  intros,
  cases m,
  from row_equivalent_step.absurd M M (by refl),
  have H₁ : row_equivalent_step M (λ (i_1 : fin (nat.succ m)) (j : fin n), ite (i_1 = ⟨m, nat.lt_succ_self m⟩) (M ⟨m, nat.lt_succ_self m⟩ j) (ite (i_1 = ⟨m, nat.lt_succ_self m⟩) (M ⟨m, nat.lt_succ_self m⟩ j) (M i_1 j))) = row_equivalent_step M M,
  congr,
  funext,
  by_cases h:(i_1 = ⟨m, nat.lt_succ_self m⟩); simp[h],
  rw ←H₁,
  from (row_equivalent_step.swap M ⟨m, nat.lt_succ_self m⟩ ⟨m, nat.lt_succ_self m⟩),
end

def absurd₂ : Π (M N : matrix (fin m) (fin n) α) (h_z : n = 0), row_equivalent_step M N :=
begin
  intros M N h_z,
  cases m,
  apply row_equivalent_step.absurd M N (by refl),
  
  have H₁, from @row_equivalent_step.swap (nat.succ m) n α _ M ⟨m, nat.lt_succ_self m⟩ ⟨m, nat.lt_succ_self m⟩,
  have H₂ : N = (λ (i : fin (nat.succ m)) (j : fin n),
       ite (i = ⟨m, _⟩) (M ⟨m, _⟩ j) (ite (i = ⟨m, _⟩) (M ⟨m, _⟩ j) (M i j))),
  funext i₁ j₁,
  rw h_z at j₁,
  exfalso,
  from nat.not_lt_zero j₁.val (fin.is_lt j₁),
  rw H₂,
  from H₁,
end

-- set_option pp.proofs true
-- set_option pp.implicit true

def elementary_implements : 
  Π {M N :  matrix (fin m) (fin n) α} (h : row_equivalent_step M N),  matrix.mul (elementary h) M = N
| _ _ (scale M i₁ s h) := begin
  ext,
  split_ifs,
  cases h_1,
  unfold matrix.mul,
  -- simp[elementary],
--   unfold elementary,
--   funext i j,
--   -- by_cases h₁ : (i = i₁),

--   -- simp[h₁],

--   -- erw @quot.lift_beta,
--   unfold matrix.mul,
--   rw finset.sum_eq_fold,

--   -- erw[sum_eq_fold],
--   dsimp [finset.fold, multiset.fold, multiset.foldr, quot.lift_on],

  

--   erw @quot.lift_beta (list α) (@setoid.r (list α) (list.perm.setoid α)) _ _ (@multiset.foldr._proof_1 α α
--          (@has_add.add α
--             (@add_semigroup.to_has_add α
--                (@add_monoid.to_add_semigroup α
--                   (@add_comm_monoid.to_add_monoid α
--                      (@semiring.to_add_comm_monoid α (@ring.to_semiring α _inst_1))))))
--          (@multiset.fold._proof_1 α
--             (@has_add.add α
--                (@add_semigroup.to_has_add α
--                   (@add_monoid.to_add_semigroup α
--                      (@add_comm_monoid.to_add_monoid α
--                         (@semiring.to_add_comm_monoid α (@ring.to_semiring α _inst_1))))))
--             (@add_comm_semigroup_to_is_commutative α
--                (@add_comm_monoid.to_add_comm_semigroup α
--                   (@semiring.to_add_comm_monoid α (@ring.to_semiring α _inst_1))))
--             (@add_semigroup_to_is_associative α
--                (@add_monoid.to_add_semigroup α
--                   (@add_comm_monoid.to_add_monoid α
--                      (@semiring.to_add_comm_monoid α (@ring.to_semiring α _inst_1))))))
--          0),

--   -- funext,
--   dsimp [list.range, list.range_core],


--   -- dsimp [list.foldr],
--   simp,

--   by_cases h₃ : (i = i₁),

--   simp[h₃],

--   -- have k, from list.range_core,


--   clear elementary_implements,
--   induction m with m m_h,
--   exfalso,
--   from nat.not_lt_zero i.val (fin.is_lt i),

--   induction n with n n_h,
--   exfalso,
--   from nat.not_lt_zero j.val (fin.is_lt j),
  

--   simp[list.range_core],



--   have H₃ : (list.foldr (has_add.add ∘ λ (j_1 : fin (nat.succ m)), ite (i₁.val = j_1.val) s 0 * (M j_1 j)) 0
--       (list.pmap fin.mk (list.range_core m [m]) _)) = (list.foldr (has_add.add ∘ λ (j_1 : fin (nat.succ m)), ite (i₁.val = j_1.val) s 0) 0
--       (list.pmap fin.mk (list.range_core m [m]) _)),
--   congr,
--   funext,

--   by_cases h₄ : (i₁ = j_1),
--   subst h₄,
  
--   -- simp,
--   simp,




--   -- have H, from @m_h M i₁,
--   -- rw m_h,

--   repeat{sorry},

-- --   congr,
-- --   sorry,
-- --   -- simp at H₄,
-- --   -- have H₅ : ∀ k₁ k₂, (0 * M k₁ k₂ = 0),
--   from H₄,

--   sorry,




--   -- by_cases h₄ : (i₁.val = j_1.val),
--   -- have H₄ : (0:α) * M j_1 j = (0:α), 
--   -- simp[zero_mul],
--   -- simp[H₄],

--   -- congr,
--   simp,
--   -- congr,
--   simp,
--   -- rw H₄,
--   -- simp[h₄],
-- -- cases list.range_core,
  
--  /- (@multiset.foldr._proof_1 α α
--          (@has_add.add α
--             (@add_semigroup.to_has_add α
--                (@add_monoid.to_add_semigroup α
--                   (@add_comm_monoid.to_add_monoid α
--                      (@semiring.to_add_comm_monoid α (@ring.to_semiring α _inst_1))))))
--          (@multiset.fold._proof_1 α
--             (@has_add.add α
--                (@add_semigroup.to_has_add α
--                   (@add_monoid.to_add_semigroup α
--                      (@add_comm_monoid.to_add_monoid α
--                         (@semiring.to_add_comm_monoid α (@ring.to_semiring α _inst_1))))))
--             (@add_comm_semigroup_to_is_commutative α
--                (@add_comm_monoid.to_add_comm_semigroup α
--                   (@semiring.to_add_comm_monoid α (@ring.to_semiring α _inst_1))))
--             (@add_semigroup_to_is_associative α
--                (@add_monoid.to_add_semigroup α
--                   (@add_comm_monoid.to_add_monoid α
--                      (@semiring.to_add_comm_monoid α (@ring.to_semiring α _inst_1))))))
--          0)
--          -/


--   show list α → list α → Prop,
--   -- from eq,
--   from (@setoid.r (list α) (list.perm.setoid α)),

--   -- skip,
--   show ∀ (a b : list α), a = b → list.foldr has_add.add 0 a = list.foldr has_add.add 0 b,
--   intros,
--   rw a_1,

--   simp[list.range, list.pmap, list.map, list.foldr],
--   -- simp[list.range_core],

--   by_cases h₁ : (i = i₁),
--   simp[h₁],




--   -- unfold list.foldr,

-- /-

-- quot.lift (list.foldr has_add.add 0) _
--       (multiset.map (λ (j_1 : fin m), ite (i.val = j_1.val) (ite (i.val = i₁.val) s 1) 0 * M j_1 j)
--          (finset.univ.val)) =
--     ite (i = i₁) (s * M i₁ j) (M i j)

-- -/

--   -- show list α → list β → Prop, 

--   have H₁ : ∀ x j, 0 * M x j = 0, --from @zero_mul,
--   simp,



--   -- -- have H₂ : finset.sum finset.univ (λ (x : fin m), ite (i₁.val = x.val) s 0 * M x j)
--   -- have H₂ : (finset.sum finset.univ (λ (x : fin m), ite (i₁.val = x.val) s 0 * M x j)) = (finset.sum finset.univ (λ (x : fin m), ite (i₁.val = x.val) s 0)),
--   -- congr,
--   -- funext,
  
--   -- by_cases h₂ : (i₁.val = x.val),
--   -- simp[h₂],
--   -- simp[H₁],
end
| M _ (swap _ i₁ i₂) := begin 
-- clear elementary_implements,
-- induction m,
-- exfalso,
-- from nat.not_lt_zero _ i₁.is_lt,
-- induction n,
-- funext j k,
-- exfalso,
-- from nat.not_lt_zero _ k.is_lt,


-- -- have H, from @n_ih,
-- -- simp,
-- -- congr at H,
-- unfold elementary, simp, unfold matrix.mul, funext, 
-- apply eq.trans,
-- apply finset.sum_eq_fold,
-- unfold has_mul.mul,
-- unfold finset.fold,
-- unfold multiset.fold,
-- unfold multiset.foldr,
-- unfold multiset.map,
-- unfold finset.univ,
-- unfold quot.lift_on,
-- simp,
-- -- dsimp,
-- sorry,
end
| M _ (linear_add _ i₁ s i₂ h₁) := sorry
| M N (absurd _ _ h_z) := begin
  funext,
  exfalso,
  rw h_z at i,
  from nat.not_lt_zero i.val (fin.is_lt i),
end

end row_equivalent_step

inductive row_equivalent : matrix (fin m) (fin n) α → matrix (fin m) (fin n) α → Type u
| nil : Π {N M : matrix (fin m) (fin n) α} (h : row_equivalent_step N M), row_equivalent N M
| cons : Π {N M L : matrix (fin m) (fin n) α} (h₁ : row_equivalent N M) (h₂ : row_equivalent_step M L), row_equivalent N L

namespace row_equivalent
def get_matrix
: Π {M N : (matrix (fin m) (fin n) α)}, row_equivalent M N → matrix (fin m) (fin m) α
 | a b (row_equivalent.nil h) := h.elementary
 | a b (row_equivalent.cons h₁ h₂) := matrix.mul (h₂.elementary) (get_matrix h₁) 

def matrix_implements : 
  Π {M N :  matrix (fin m) (fin n) α} (h : row_equivalent M N), matrix.mul (row_equivalent.get_matrix h) M = N := 
begin
    intros,
    induction h;
    simp[row_equivalent.get_matrix,row_equivalent_step.elementary_implements],

    apply eq.trans,
    from eq.symm (matrix.mul_assoc (row_equivalent_step.elementary h_h₂) (row_equivalent.get_matrix h_h₁) h_N),
    rw h_ih,
    simp[row_equivalent.get_matrix,row_equivalent_step.elementary_implements],
end

def trans {M N L : (matrix (fin m) (fin n) α)} : (row_equivalent M N) → (row_equivalent N L) → row_equivalent M L :=
begin
  intros r₁ r₂,
  induction r₂ with M₁ N₁ h₁ M₁ N₂ L₁ h₁ h₂ h₃,
  from cons r₁ h₁,
  from cons (h₃ r₁) (h₂),
end

def refl : Π (M : matrix (fin m) (fin n) α), row_equivalent M M := 
λ M, nil (row_equivalent_step.refl M)

def precons : Π {M N L : matrix (fin m) (fin n) α}, row_equivalent_step M N → row_equivalent N L → row_equivalent M L :=
begin
  intros M N L r₀ r₁,
  induction r₁ with N₁ M₁ h₁ N₁ M₁ L₁ h₁ h₂ h₃,
  from (cons (nil r₀) h₁),
  from (cons (h₃ r₀) h₂),
end

end row_equivalent








-- open tactic


-- set_option trace.eqn_compiler.elim_match true

-- meta def requiv : tactic unit :=
-- do tgt ← target, t ← infer_type tgt,
-- match tgt with
-- | `(row_equivalent_step %%M (matrix.mul %%N %%L)) :=
--   if h₀ : (L=M) then 
--     match N with
--     | `(row_equivalent_step.elementary %%h₁) :=
--       match h₁ with
--       | `(row_equivalent_step.scale %%a %%i₁ %%s %%hs) := rewrite_target h₁
--       | `(row_equivalent_step.swap %%a %%i₁ %%i₂) := failure
--       | `(row_equivalent_step.linear_add %%a %%i₁ %%s %%i₂ %%h) := failure
--       | _ := failure
--       end
--     | _ := failure
--     end
--   else failure
-- | _ := failure
