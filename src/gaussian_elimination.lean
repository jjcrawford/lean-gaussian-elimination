import ring_theory.matrix
import .row_equivalence

universes u
variables {m n : ℕ}
variable {α : Type u}
variable [division_ring α]
variable [decidable_eq α]


def ge_aux_findpivot : 
  (fin m) → (fin m) → (fin n) → (matrix (fin m) (fin n) α) → (matrix (fin m) (fin n) α)
| ⟨0, h₁⟩        i₀ j₀ M := M
| ⟨(k + 1), h₁⟩ i₀ j₀ M := 
        if k ≥ i₀.val then 
            if M ⟨k+1, h₁⟩ j₀ ≠ 0 
                then matrix.mul (elementary.swap α ⟨k+1, h₁⟩ i₀).to_matrix M
            else ge_aux_findpivot ⟨k, nat.lt_of_succ_lt h₁⟩ i₀ j₀ M
        else M

def ge_aux_improvepivot : 
  (fin m) → (fin n) → (matrix (fin m) (fin n) α) → (matrix (fin m) (fin n) α) :=
λ i₀ j₀ M, if h : M i₀ j₀ ≠ 0 
    then matrix.mul (elementary.scale i₀ ((M i₀ j₀)⁻¹) (inv_ne_zero h)).to_matrix M else M

def ge_aux_eliminate : 
  Π (k : fin m) (i : fin m) (j : fin n) (M : matrix (fin m) (fin n) α) (h : M i j = 1), (matrix (fin m) (fin n) α) :=
λ k i j M h, if h₀ : k≠i then matrix.mul (elementary.linear_add k (-(M k j)) i h₀).to_matrix M else M
 
def ge_aux_eliminatecolumn : 
  Π (k : fin m) (i : fin m) (j : fin n) (M : matrix (fin m) (fin n) α), (matrix (fin m) (fin n) α) 
| ⟨0,h₁⟩ i j M := M
| ⟨k+1, h₁⟩ i j M := begin
    from if h : k < i.val then M else begin
        apply ge_aux_eliminatecolumn ⟨k, nat.lt_of_succ_lt h₁⟩ i j _ ,
        have h_ne : fin.mk (k+1) h₁ ≠ i,
        intros h_eq, apply h, cases h_eq, simp[nat.lt_succ_self 0],
        from matrix.mul (elementary.linear_add ⟨k+1, h₁⟩ (-(M ⟨k+1,h₁⟩ j)) i h_ne).to_matrix M,
    end
end

def ge_aux_findpivot_row_equivalent : 
  Π (i : fin m) (i₀ : fin m) (j₀ : fin n) (M : matrix (fin m) (fin n) α), row_equivalent M (ge_aux_findpivot i i₀ j₀ M)
| ⟨0, h₀⟩   i₀ j₀ M := 
begin 
    simp[ge_aux_findpivot],
    from row_equivalent.nil,
end
| ⟨k+1, h₀⟩ i₀ j₀ M := begin
    unfold ge_aux_findpivot,
    split_ifs,
    from @row_equivalent_step.of_elementary m n α _ _ M (elementary.swap α ⟨k + 1, h₀⟩ i₀),
    apply ge_aux_findpivot_row_equivalent,
    from row_equivalent.nil,
end

def ge_aux_improvepivot_row_equivalent : 
  Π (i₀ : fin m) (j₀ : fin n) (M : matrix (fin m) (fin n) α), row_equivalent M (ge_aux_improvepivot i₀ j₀ M)
| i₀ j₀ M := 
begin
    simp[ge_aux_improvepivot],
    split_ifs,
    from @row_equivalent_step.of_elementary m n α _ _ M (elementary.scale i₀ (M i₀ j₀)⁻¹ (ge_aux_improvepivot._proof_1 i₀ j₀ M h)),
    from row_equivalent.nil
end

def ge_aux_eliminate_row_equivalent : 
  Π (i : fin m) (i₀ : fin m) (j₀ : fin n) (M : matrix (fin m) (fin n) α) (h : M i₀ j₀ = 1), row_equivalent M (ge_aux_eliminate i i₀ j₀ M h) 
| i i₀ j₀ M h :=
begin
    unfold ge_aux_eliminate,
    split_ifs,
    from @row_equivalent_step.of_elementary m n α _ _ M (elementary.linear_add i (-M i j₀) i₀ h_1),
    from row_equivalent.nil,
end

def ge_aux_eliminatecolumn_row_equivalent : 
  Π (i : fin m) (i₀ : fin m) (j₀ : fin n) (M : matrix (fin m) (fin n) α), row_equivalent M (ge_aux_eliminatecolumn i i₀ j₀ M)
| ⟨0, h₀⟩ i₀ j₀ M :=
begin
    unfold ge_aux_eliminatecolumn,
    from row_equivalent.nil,
end
| ⟨k+1, h₀⟩ i₀ j₀ M :=
begin
    unfold ge_aux_eliminatecolumn,
    split_ifs,
    from row_equivalent.nil,
    apply row_equivalent.trans,
    show matrix (fin m) (fin n) α,
    from (matrix.mul
          (elementary.to_matrix
             (elementary.linear_add ⟨k + 1, h₀⟩ (-M ⟨k + 1, h₀⟩ j₀) i₀
                (ge_aux_eliminatecolumn._main._pack._proof_1 k h₀ i₀ h)))
          M),
    from @row_equivalent_step.of_elementary m n α _ _ M (elementary.linear_add ⟨k + 1, h₀⟩ (-M ⟨k + 1, h₀⟩ j₀) i₀
             (ge_aux_eliminatecolumn._main._pack._proof_1 k h₀ i₀ h)),
    apply ge_aux_eliminatecolumn_row_equivalent,
end


lemma nat.sub_lt_succ_of_lt_succ {a b : ℕ} : a < (nat.succ b) → b - a < (nat.succ b) :=
begin
    intro h,
    cases a,
    from nat.lt_succ_self b,
    from nat.lt_trans ((nat.sub_lt_of_pos_le (nat.succ a) b (nat.zero_lt_succ a)) (nat.le_of_lt_succ h)) (nat.lt_succ_self b),
end

@[simp] lemma nat.pred_lt_of_ne_zero {n : ℕ} : n ≠ 0 → nat.succ (nat.pred n) = n :=
begin
    intros h_nz,
    apply nat.succ_pred_eq_of_pos,
    have H₁, from @nat.eq_or_lt_of_le 0 n (nat.zero_le n),
    cases H₁,
    exfalso,
    from h_nz (eq.symm H₁),
    assumption,
end

lemma nat.pred_sub_lt {a b : ℕ} : b ≠ 0 → a < b → (nat.pred b) - a < b :=
begin
    intros h_n h,
    rw ←nat.pred_lt_of_ne_zero h_n,
    apply nat.sub_lt_succ_of_lt_succ,
    simp[nat.pred_lt_of_ne_zero h_n],
    from h,
end

lemma nat.lt_succ_of_succ_lt {a b : ℕ} : nat.succ a < b → a < nat.succ b :=
begin
    intros h,
    have ha, from nat.lt_succ_self a,
    have hb, from nat.lt_succ_self b,
    apply nat.lt_trans ha,
    apply nat.lt_trans,
    swap,
    from hb,
    from h
end

lemma nat.pred_pred_sub_lt_of_lt : Π {a b : ℕ}, nat.succ a < b → (nat.pred b) - a - 1 < b :=
begin
    intros a b h,
    have H₁, from @nat.sub_lt_succ_of_lt_succ (nat.succ a) (nat.pred b),
    rw nat.pred_lt_of_ne_zero at H₁,
    have H₂,
    from H₁ h,
    have H₃ : nat.pred b - nat.succ a = nat.pred b - a - 1,
    refl,
    rw ←H₃,
    from H₂,
    
    intros h₁,
    have H₂, from @nat.zero_lt_succ a,
    have H₃, from nat.lt_trans H₂ h,
    subst h₁,
    from nat.not_lt_zero 0 H₃,
end

lemma nat.lt_succ_pred : Π {n : ℕ}, (n ≠ 0) → (nat.pred n) < n :=
begin
    intros n h,
    have : (nat.pred n < nat.succ (nat.pred n)) = (nat.pred n < n),
    congr,
    from nat.pred_lt_of_ne_zero h,
    rw ←this,
    from nat.lt_succ_self (nat.pred n),
end


def ge_aux : Π (j : fin n) (i : fin m) (h_n : n ≠ 0) (h_m : m ≠ 0) (M : matrix (fin m) (fin n) α), (matrix (fin m) (fin n) α)
|     ⟨k₂, h₂⟩  ⟨0, h₁⟩  h_n h_m    M       := 
        begin  -- If we're on the last row, all we need to do is improve the pivot if we can
            from if M ⟨0, h₁⟩ ⟨k₂, h₂⟩ ≠ 0 then 
                begin
                    apply ge_aux_improvepivot,
                    from ⟨nat.pred m, nat.pred_lt h_m⟩,

                    from ⟨(nat.pred n) - k₂, nat.pred_sub_lt h_n h₂⟩,
                    from M,
                end
            else M,
        end
|  ⟨0, h₂⟩  ⟨k₁+1, h₁⟩ h_n h_m   M    := 
        begin  -- If we're in the last column, all we need to do is eliminate that column

            -- have H₁, from @nat.sub_lt_succ_of_lt_succ k₁ (nat.pred m) (nat.lt_of_succ_lt h₁),
            let toplefti : fin m := ⟨(nat.pred m)-k₁-1, nat.pred_pred_sub_lt_of_lt h₁⟩,
            let topleftj : fin n := ⟨nat.pred n, nat.pred_lt h_n⟩,

            let bottomrow : fin m := ⟨nat.pred m, nat.pred_lt h_m⟩,

            have M₁ : matrix (fin m) (fin n) α,
            apply ge_aux_findpivot bottomrow toplefti topleftj M,

            from if H₁ : (M₁ toplefti topleftj ≠ 0) then begin
                apply ge_aux_eliminatecolumn,
                from bottomrow,
                from toplefti,
                from topleftj,

                apply ge_aux_improvepivot,
                from toplefti,
                from topleftj,

                from M₁,
                repeat {assumption},
            end else M₁,
        end
| ⟨k₂+1, h₂⟩  ⟨k₁+1, h₁⟩ h_n h_m  M   := 
        begin
            apply ge_aux,
            show matrix (fin m) (fin n) α,

            let toplefti : (fin m) := ⟨(nat.pred m)-k₁-1, nat.pred_pred_sub_lt_of_lt h₁⟩,
            let topleftj : (fin n) := ⟨(nat.pred n)-k₂-1, nat.pred_pred_sub_lt_of_lt h₂⟩,

            let bottomrow : fin (m) := ⟨nat.pred m, nat.pred_lt h_m⟩,

            have M₁ : matrix (fin m) (fin n) α,
            from ge_aux_findpivot bottomrow toplefti topleftj M,

            from if H₁ : (M₁ toplefti topleftj ≠ 0) then begin
                apply ge_aux_eliminatecolumn,
                from bottomrow,
                from toplefti,
                from topleftj,
  
                -- show matrix _ _ α,
                apply ge_aux_improvepivot,
                from toplefti,
                from topleftj,


                from M₁,
                repeat {assumption},
            end else M₁,

            
            from ⟨k₂, nat.lt_of_succ_lt h₂⟩,

            let toplefti : fin m := ⟨(nat.pred m)-k₁-1, nat.pred_pred_sub_lt_of_lt h₁⟩,
            let topleftj : fin n := ⟨(nat.pred n)-k₂-1, nat.pred_pred_sub_lt_of_lt h₂⟩,

            let bottomrow : fin m := ⟨nat.pred m, nat.pred_lt h_m⟩,

            have M₁ : matrix (fin m) (fin n) α,
            from ge_aux_findpivot bottomrow toplefti topleftj M,

            from if H₁ : (M₁ toplefti topleftj ≠ 0) 
            then ⟨k₁, nat.lt_of_succ_lt h₁⟩
            else ⟨k₁+1, h₁⟩,                
            from h_n,
            from h_m,
        end


def gaussian_elimination (M : matrix (fin m) (fin n) α) : matrix (fin m) (fin n) α :=
begin
    by_cases h_m : m = 0,
    from M,
    by_cases h_n : n = 0,
    from M,

    have h₁, from nat.pred_lt_of_ne_zero h_m,
    have h₂, from nat.pred_lt_of_ne_zero h_n,
    
    apply ge_aux,
    from ⟨nat.pred n, nat.lt_succ_pred h_n⟩,
    from ⟨nat.pred m, nat.lt_succ_pred h_m⟩,
    from h_n,
    from h_m,
    from M,
end


def ge_aux_row_equivalent : Π (j : fin n) (i : fin m) (h_n : n ≠ 0) (h_m : m ≠ 0) (M : matrix (fin m) (fin n) α), row_equivalent M (ge_aux j i h_n h_m M)
| ⟨0, j_is_lt⟩ ⟨0, i_is_lt⟩ h_n h_m M :=
begin
    simp[ge_aux],
    split_ifs,
    from row_equivalent.nil,
    apply row_equivalent.trans,

    swap,
    apply ge_aux_improvepivot_row_equivalent,
    from row_equivalent.nil,
end
| ⟨j+1, j_is_lt⟩ ⟨0, i_is_lt⟩ h_n h_m M :=
begin
    simp[ge_aux],
    split_ifs,
    from row_equivalent.nil,

    apply row_equivalent.trans,
    swap,
    apply ge_aux_improvepivot_row_equivalent,
    from row_equivalent.nil,
end
| ⟨0, j_is_lt⟩ ⟨i+1, i_is_lt⟩ h_n h_m M :=
begin
    simp[ge_aux],
    split_ifs,
    apply ge_aux_findpivot_row_equivalent,

    apply row_equivalent.trans,
    show row_equivalent M (ge_aux_findpivot ⟨nat.pred m, _⟩ ⟨nat.pred m - i - 1, _⟩ ⟨nat.pred n, _⟩ M),
    apply ge_aux_findpivot_row_equivalent,
    apply row_equivalent.trans,
    show row_equivalent _ (ge_aux_improvepivot ⟨nat.pred m - i - 1, _⟩ ⟨nat.pred n, _⟩
          (ge_aux_findpivot ⟨nat.pred m, _⟩ ⟨nat.pred m - i - 1, _⟩ ⟨nat.pred n, _⟩ M)),
    apply ge_aux_improvepivot_row_equivalent,
    apply ge_aux_eliminatecolumn_row_equivalent,
end
| ⟨j + 1, j_is_lt⟩ ⟨i + 1, i_is_lt⟩ h_n h_m M := 
begin
    simp[ge_aux],
    split_ifs,
    apply row_equivalent.trans,
    swap,
    apply ge_aux_row_equivalent,
    apply ge_aux_findpivot_row_equivalent,

    apply row_equivalent.trans,
    show row_equivalent M (ge_aux_findpivot ⟨nat.pred m, _⟩ ⟨nat.pred m - i - 1, _⟩ ⟨nat.pred n - j - 1, _⟩ M),
    apply ge_aux_findpivot_row_equivalent,
    apply row_equivalent.trans,
    show row_equivalent _  (ge_aux_improvepivot ⟨nat.pred m - i - 1, _⟩ ⟨nat.pred n - j - 1, _⟩
             (ge_aux_findpivot ⟨nat.pred m, _⟩ ⟨nat.pred m - i - 1, _⟩ ⟨nat.pred n - j - 1, _⟩ M)),
    apply ge_aux_improvepivot_row_equivalent,
    apply row_equivalent.trans,
    show row_equivalent _ (ge_aux_eliminatecolumn ⟨nat.pred m, _⟩ ⟨nat.pred m - i - 1, _⟩ ⟨nat.pred n - j - 1, _⟩
          (ge_aux_improvepivot ⟨nat.pred m - i - 1, _⟩ ⟨nat.pred n - j - 1, _⟩
             (ge_aux_findpivot ⟨nat.pred m, _⟩ ⟨nat.pred m - i - 1, _⟩ ⟨nat.pred n - j - 1, _⟩ M))),
    apply ge_aux_eliminatecolumn_row_equivalent,
    apply ge_aux_row_equivalent,
end

def gaussian_elimination.row_equivalent : Π (M : matrix (fin m) (fin n) α), row_equivalent M (gaussian_elimination M) :=
begin
    intros,
    simp[gaussian_elimination],
    split_ifs,
    from row_equivalent.nil,
    from row_equivalent.nil,
    apply ge_aux_row_equivalent,
end