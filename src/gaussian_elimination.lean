import ring_theory.matrix
import .row_equivalence
import .row_equivalence_fields

universes u
variables {m n : ℕ}
variable {α : Type u}
variable [division_ring α]
variable [decidable_eq α]


def ge_aux_findpivot : (fin m) → (fin m) → (fin n) → (matrix (fin m) (fin n) α) → (matrix (fin m) (fin n) α)
| ⟨0, h₁⟩        i₀ j₀ M := M
| ⟨(k + 1), h₁⟩ i₀ j₀ M := 
        if k ≥ i₀.val then 
            if M ⟨k+1, h₁⟩ j₀ ≠ 0 
                then matrix.mul (elementary.swap α ⟨k+1, h₁⟩ i₀).to_matrix M
            else ge_aux_findpivot ⟨k, nat.lt_of_succ_lt h₁⟩ i₀ j₀ M
        else M

def ge_aux_improvepivot : (fin m) → (fin n) → (matrix (fin m) (fin n) α) → (matrix (fin m) (fin n) α) :=
λ i₀ j₀ M, if h : M i₀ j₀ ≠ 0 
    then matrix.mul (elementary.scale i₀ ((M i₀ j₀)⁻¹) (inv_ne_zero h)).to_matrix M
    else M

def ge_aux_eliminate : Π (k : fin m) (i : fin m) (j : fin n) (M : matrix (fin m) (fin n) α) (h : M i j = 1), (matrix (fin m) (fin n) α) :=
λ k i j M h, if h₀ : k≠i then matrix.mul (elementary.linear_add k (-(M k j)) i h₀).to_matrix M else M
 
def ge_aux_eliminatecolumn : Π (k : fin m) (i : fin m) (j : fin n) (M : matrix (fin m) (fin n) α), (matrix (fin m) (fin n) α) 
| ⟨0,h₁⟩ i j M := M
| ⟨k+1, h₁⟩ i j M := begin
    from if h : k < i.val then M else begin
        apply ge_aux_eliminatecolumn ⟨k, nat.lt_of_succ_lt h₁⟩ i j _ ,
        -- show matrix (fin m) (fin n) α,
        -- clear ge_aux_eliminatecolumn,
        -- cases n,
        -- exfalso,
        -- from nat.not_lt_zero j.val j.is_lt,
        -- cases m,
        -- exfalso,
        -- from nat.not_lt_zero i.val i.is_lt,
        -- have h₂, from (iff.elim_left nat.lt_iff_le_not_le),
        have h_ne : fin.mk (k+1) h₁ ≠ i,
        intros h_eq,
        apply h,
        cases h_eq,
        simp[nat.lt_succ_self 0],

        from matrix.mul (elementary.linear_add ⟨k+1, h₁⟩ (-(M ⟨k+1,h₁⟩ j)) i h_ne).to_matrix M,
        end
end


inductive row_reduction_step : (fin m) → (fin n) → matrix (fin m) (fin n) α → matrix (fin m) (fin n) α → Type u
| findpivot : Π (i : fin m) (j : fin n) (M : matrix (fin m) (fin n) α) (i₀ : fin m), row_reduction_step i j M (ge_aux_findpivot i₀ i j M)
| improvepivot : Π (i : fin m) (j : fin n) (M : matrix (fin m) (fin n) α), row_reduction_step i j M (ge_aux_improvepivot i j M)
| eliminate : Π (i : fin m) (j : fin n) (M : matrix (fin m) (fin n) α) (i₀ : fin m) (h : M i j = 1), row_reduction_step i j M (ge_aux_eliminate i₀ i j M h)




lemma ge_aux_findpivot_row_equivalent : Π (i : fin m) (i₀ : fin m) (j₀ : fin n) (M : matrix (fin m) (fin n) α), row_equivalent M (ge_aux_findpivot i i₀ j₀ M)
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

set_option pp.proofs true

lemma ge_aux_improvepivot_row_equivalent : Π (i₀ : fin m) (j₀ : fin n) (M : matrix (fin m) (fin n) α), row_equivalent M (ge_aux_improvepivot i₀ j₀ M)
| i₀ j₀ M := 
begin
    simp[ge_aux_improvepivot],
    split_ifs,
    from @row_equivalent_step.of_elementary m n α _ _ M (elementary.scale i₀ (M i₀ j₀)⁻¹ (ge_aux_improvepivot._proof_1 i₀ j₀ M h)),
    from row_equivalent.nil
end

lemma ge_aux_eliminate_row_equivalent : Π (i : fin m) (i₀ : fin m) (j₀ : fin n) (M : matrix (fin m) (fin n) α) (h : M i₀ j₀ = 1), row_equivalent M (ge_aux_eliminate i i₀ j₀ M h) 
| i i₀ j₀ M h :=
begin
    unfold ge_aux_eliminate,
    split_ifs,
    from @row_equivalent_step.of_elementary m n α _ _ M (elementary.linear_add i (-M i j₀) i₀ h_1),
    from row_equivalent.nil,
end

lemma ge_aux_eliminatecolumn_row_equivalent : Π (i : fin m) (i₀ : fin m) (j₀ : fin n) (M : matrix (fin m) (fin n) α), row_equivalent M (ge_aux_eliminatecolumn i i₀ j₀ M)
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

-- TODO: Why does bytecode generation fail?
def row_reduction_step.to_row_equivalent : Π {j : fin n} {i : fin m} {M N :  matrix (fin m) (fin n) α} (r : row_reduction_step i j M N), row_equivalent M N :=
begin
    intros _ _ _ _ r,
    induction r with i j M i₀ i j M i j M i₀ h,
    from @ge_aux_findpivot_row_equivalent m n α _ _ i₀ i j M,
    from @ge_aux_improvepivot_row_equivalent m n α _ _ i j M,
    from @ge_aux_eliminate_row_equivalent m n α _ _ i₀ i j M h,
end

-- Note that bytecode generation fails even more seriously here! (Because they choose a red underline?)
-- def to_row_equivalent : Π {j : fin n} {i : fin m} {M N :  matrix (fin m) (fin n) α} (r : row_reduction_step i j M N), row_equivalent M N
-- | _ _ _ _ (findpivot i j M i₀) :=  @ge_aux_findpivot_row_equivalent m n α _ _ i₀ i j M
-- | _ _ _ _ (improvepivot i j M) :=  @ge_aux_improvepivot_row_equivalent m n α _ _ i j M
-- | _ _ _ _ (eliminate i j M i₀ h) := @ge_aux_eliminate_row_equivalent m n α _ _ i₀ i j M h


lemma sub_lt_succ_of_lt_succ {a b : ℕ} : a < (b + 1) → b - a < (b + 1) :=
begin
    intro h,
    cases a,
    from nat.lt_succ_self b,
    from nat.lt_trans ((nat.sub_lt_of_pos_le (nat.succ a) b (nat.zero_lt_succ a)) (nat.le_of_lt_succ h)) (nat.lt_succ_self b),
end

def ge_aux : Π (j : fin n) (i : fin m) (M : matrix (fin m) (fin n) α), (matrix (fin m) (fin n) α)
|     ⟨k₂, h₂⟩  ⟨0, h₁⟩     M       := 
        begin  -- If we're on the last row, all we need to do is improve the pivot if we can
            from if M ⟨0, h₁⟩ ⟨k₂, h₂⟩ ≠ 0 then 
                begin
                    apply ge_aux_improvepivot,
                    clear ge_aux,
                    cases m, 
                    exfalso,
                    from nat.not_lt_zero 0 h₁,

                    from ⟨m, nat.lt_succ_self m⟩,

                    clear ge_aux,
                    cases n,
                    exfalso,
                    from nat.not_lt_zero k₂ h₂,

                    constructor,

                    from sub_lt_succ_of_lt_succ h₂,

                    from M,
                end
            else M,
        end
|  ⟨0, h₂⟩  ⟨k₁+1, h₁⟩   M    := 
        begin  -- If we're in the last column, all we need to do is eliminate that column
            clear ge_aux,
            cases m,
            exfalso,
            from nat.not_lt_zero (k₁+1) h₁,

            cases n,
            exfalso,
            from nat.not_lt_zero 0 h₂,

            let toplefti : fin (m+1) := ⟨m-k₁-1, sub_lt_succ_of_lt_succ h₁⟩,
            let topleftj : fin (n+1) := ⟨n, nat.lt_succ_self n⟩,

            let bottomrow : fin (m+1) := ⟨m, nat.lt_succ_self m⟩,

            have M₁ : matrix (fin (nat.succ m)) (fin (nat.succ n)) α,
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
| ⟨k₂+1, h₂⟩  ⟨k₁+1, h₁⟩   M   := 
        begin
            apply ge_aux;clear ge_aux,

            show matrix _ _ α,
            cases m,
            exfalso,
            from nat.not_lt_zero (k₁ + 1) h₁,
            cases n,
            exfalso,
            from nat.not_lt_zero (k₂ + 1) h₂,

            let toplefti : fin (m+1) := ⟨m-k₁-1, sub_lt_succ_of_lt_succ h₁⟩,
            let topleftj : fin (n+1) := ⟨n-k₂-1, sub_lt_succ_of_lt_succ h₂⟩,

            let bottomrow : fin (m+1) := ⟨m, nat.lt_succ_self m⟩,

            have M₁ : matrix (fin (nat.succ m)) (fin (nat.succ n)) α,
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

            cases m,
            exfalso,
            from nat.not_lt_zero (k₁ + 1) h₁,
            cases n,
            exfalso,
            from nat.not_lt_zero (k₂ + 1) h₂,

            let toplefti : fin (m+1) := ⟨m-k₁-1, sub_lt_succ_of_lt_succ h₁⟩,
            let topleftj : fin (n+1) := ⟨n-k₂-1, sub_lt_succ_of_lt_succ h₂⟩,

            let bottomrow : fin (m+1) := ⟨m, nat.lt_succ_self m⟩,

            have M₁ : matrix (fin (nat.succ m)) (fin (nat.succ n)) α,
            from ge_aux_findpivot bottomrow toplefti topleftj M,

            from if H₁ : (M₁ toplefti topleftj ≠ 0) 
            then ⟨k₁, nat.lt_of_succ_lt h₁⟩
            else ⟨k₁+1, h₁⟩,                
        end


def gaussian_elimination (M : matrix (fin m) (fin n) α) : matrix (fin m) (fin n) α :=
begin
    cases m,
    from M,
    cases n,
    from M,

    apply ge_aux,
    from ⟨n, nat.lt_succ_self n⟩,
    from ⟨m, nat.lt_succ_self m⟩,
    from M,
end


theorem ge_aux_row_equivalent : Π (j : fin n) (i : fin m) (M : matrix (fin m) (fin n) α), row_equivalent M (ge_aux j i M)
| ⟨0, j_is_lt⟩ ⟨0, i_is_lt⟩ M :=
begin
    simp[ge_aux],
    split_ifs,
    from row_equivalent.nil,
    conv {
        congr,
        skip,
        congr,
        skip,
    },
    sorry,
    -- apply ge_aux_row_equivalent,
end
| _ _ _ := sorry
-- | ⟨i_val, j_is_lt⟩ ⟨j_val, i_is_lt⟩ M :=
-- begin
--     cases j_val; cases i_val,

--     simp[ge_aux],

--     by_cases h : (M ⟨0, eq.rec i_is_lt nat.nat_zero_eq_zero⟩
--               ⟨0, eq.rec (eq.rec j_is_lt nat.nat_zero_eq_zero) nat.nat_zero_eq_zero⟩ =
--             0),

--     simp[h],
--     from row_equivalent.nil,
--     simp[h],
--     apply row_reduction_step.ge_aux_improvepivot_row_equivalent,
    

--     simp[ge_aux],
--     by_cases h: (M ⟨0, eq.rec i_is_lt nat.nat_zero_eq_zero⟩ ⟨nat.succ i_val, j_is_lt⟩ = 0),
--     simp[h],
--     from row_equivalent.nil,
--     simp[h],
--     apply row_reduction_step.ge_aux_improvepivot_row_equivalent,

    
-- end


