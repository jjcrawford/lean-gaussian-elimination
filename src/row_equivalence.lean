import ring_theory.matrix
import .finset_sum


universes u
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
  simp, -- ⊢ finset.sum finset.univ (λ (x : fin m), ite (i = x) (s * M x j) 0) = s * M i j
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

lemma elementary.mul_eq_apply : Π {M : matrix (fin m) (fin n) α} (e : elementary α m), ((e.to_matrix).mul M) =  (e.apply M) :=
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


def row_equivalent_step.of_elementary : 
  Π {M : matrix (fin m) (fin n) α} (e : elementary α m), row_equivalent_step M ((e.to_matrix).mul M) :=
    λ _ e, ⟨e, by refl⟩

def row_equivalent_step.of_elementary_apply : 
  Π {M : matrix (fin m) (fin n) α} (e : elementary α m), row_equivalent_step M (e.apply M) :=
begin
  intros,
  rw ←elementary.mul_eq_apply,
  apply row_equivalent_step.of_elementary
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
  rw ←elementary.mul_eq_apply,
  assumption,
end

inductive row_equivalent : matrix (fin m) (fin n) α → matrix (fin m) (fin n) α → Type u
| nil : Π {N : matrix (fin m) (fin n) α}, row_equivalent N N
| cons : Π {N M L : matrix (fin m) (fin n) α} (h₁ : row_equivalent N M) (h₂ : row_equivalent_step M L), row_equivalent N L

def row_equivalent.of_step : Π {M N : matrix (fin m) (fin n) α} (r : row_equivalent_step M N), row_equivalent M N := λ _ _ r, row_equivalent.cons (row_equivalent.nil) r

instance row_equivalent_step.has_coe_row_equivalent : Π {M N : matrix (fin m) (fin n) α}, has_coe (row_equivalent_step M N) (row_equivalent M N) := λ M N, ⟨λ r, row_equivalent.of_step r⟩

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


def row_equivalent.trans {M N L : (matrix (fin m) (fin n) α)} : (row_equivalent M N) → (row_equivalent N L) → row_equivalent M L :=
begin
  intros r₁ r₂,
  induction r₂ with M₁ M₁ N₁ L₁ h₁ h₂ h₃,
  from r₁,
  from row_equivalent.cons (h₃ r₁) h₂,
end


def row_equivalent.precons : Π {M N L : matrix (fin m) (fin n) α}, row_equivalent_step M N → row_equivalent N L → row_equivalent M L :=
begin
  intros M N L r₀ r₁,
  induction r₁ with M₁ M₁ N₁ L₁ h₁ h₂ h₃,
  from r₀,
  from row_equivalent.cons (h₃ r₀) h₂,
end

