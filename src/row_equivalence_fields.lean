import ring_theory.matrix
import row_equivalence
import .finset_sum

universes u v
variables {m n : ℕ}
variable {α : Type u}
variable [division_ring α]
variable [decidable_eq α]


def elementary.inv : (elementary α m) → (elementary α m) :=
begin
    intros e,
    cases e with i₁ s hs i₁ i₂ i₁ s i₂ h_ne,

    from elementary.scale i₁ s⁻¹ (inv_ne_zero hs),
    from @elementary.swap α _ _ _ i₂ i₁,
    from @elementary.linear_add α _ _ m i₁ (-s) i₂ h_ne,
end

instance elementary.has_inv : has_inv (elementary α m) := ⟨elementary.inv⟩

@[simp] lemma elementary.inv_inv : Π {e : elementary α m}, (e⁻¹)⁻¹ = e :=
begin
    intros e,
    cases e;{simp[has_inv.inv, elementary.inv],
    try{apply division_ring.inv_inv,
    assumption}}
end

theorem elementary.inv_apply_implements : Π {M N : matrix (fin m) (fin n) α} {e : elementary α m},  (elementary.apply e) M = N → M = (elementary.apply e⁻¹) N :=
begin
    intros M N e h,
    rw ←h,
    cases e with i₁ s hs i₁ i₂ i₁ s i₂ i_ne,

    -- scale case
    {
    simp[has_inv.inv, elementary.inv],
    simp[elementary.apply],
    funext i j,
    split_ifs with h₁,
    rw ←mul_assoc,
    erw inv_mul_cancel hs,
    simp,
    },

    -- swap case
    {
    simp[has_inv.inv, elementary.inv],
    simp[elementary.apply],
    funext i j,
    split_ifs with h₁ h₂ h₃; {try{simp[h₁]}, try{simp[h₂], try{simp[h₃]}}},
    },

    -- linear_add case
    {
    simp[has_inv.inv, elementary.inv],
    simp[elementary.apply],
    funext i j,
    split_ifs with h₁ h₂;try{try{simp[h₁]}, try{simp[h₂]}},
    exfalso,
    subst h₁,
    from i_ne (eq.symm h₂)
    }
end

theorem elementary.inv_apply_implements_iff_apply_implements : Π {M N : matrix (fin m) (fin n) α} {e : elementary α m},  (elementary.apply e) M = N ↔ M = (elementary.apply e⁻¹) N  :=
begin
    intros M N e,
    split,
    apply elementary.inv_apply_implements,
    let e₁ := e⁻¹,
    have h₁ : e = e₁⁻¹,
    simp[e₁],
    rw h₁,
    simp,
    have H₁, from λ h₂, eq.symm ((@elementary.inv_apply_implements m n α _ _ N M (e⁻¹)) (eq.symm h₂)),
    rw elementary.inv_inv at H₁,
    from H₁
end

theorem inv_matrix_implements : Π {M N : matrix (fin m) (fin n) α} {e : elementary α m}, matrix.mul (elementary.to_matrix e) M = N → M = matrix.mul (elementary.to_matrix e⁻¹) N :=
begin
    intros M N e,
    simp[elementary.mul_eq_apply],
    apply elementary.inv_apply_implements,
end

theorem elementary.inv_matrix_implements_iff_matrix_implements : Π {M N : matrix (fin m) (fin n) α} {e : elementary α m}, matrix.mul (elementary.to_matrix e) M = N ↔ M = matrix.mul (elementary.to_matrix e⁻¹) N :=
begin
    intros M N e,
    simp[elementary.mul_eq_apply],
    apply elementary.inv_apply_implements_iff_apply_implements,
end

def row_equivalent_step.symm : Π {M N : matrix (fin m) (fin n) α} (r : row_equivalent_step M N), row_equivalent_step N M := begin
    intros,
    cases r with elem implements,
    constructor,
    from eq.symm (inv_matrix_implements implements),
end

def row_equivalent.symm : Π {M N : matrix (fin m) (fin n) α} (r : row_equivalent M N), row_equivalent N M
| M N (row_equivalent.nil) := row_equivalent.nil
| M N (@row_equivalent.cons _ _ _ _ _ _ L _ r₁ r₂) := r₁.symm.precons r₂.symm

