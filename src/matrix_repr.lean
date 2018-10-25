import ring_theory.matrix

@[pattern] def vector.mk {α : Type*} {n : ℕ} (l : list α) (pr : l.length = n) :
  vector α n := ⟨l, pr⟩

notation `![` l:(foldr `, ` (h t, list.cons h t) list.nil `]`) :=
  vector.mk l (refl _)

universes u
variables {m n : ℕ} {α : Type u}

def matrix.bang : (vector (vector α n) m) → (matrix (fin m) (fin n) α) :=
λ M i j, (M.nth i).nth j


variables {β : Type u}

def matrix.fold_row_aux (M : matrix (fin m) (fin n) α) : Π (j : fin n) (i : fin m) (f : fin m → fin n → α → β → β) (b : β), β
| ⟨0, h₁⟩ k₂ f b := f k₂ ⟨0, h₁⟩ (M k₂ ⟨0, h₁⟩) b
| ⟨k₁ + 1, h₁⟩ k₂ f b := matrix.fold_row_aux ⟨k₁, nat.lt_of_succ_lt h₁⟩ k₂ f (f k₂ ⟨k₁ + 1, h₁⟩ (M k₂ ⟨k₁ + 1, h₁⟩) b)

def matrix.fold_row (M : matrix (fin m) (fin n) α) : Π (i : fin m) (f : fin m → fin n → α → β → β) (b : β), β :=
begin
    intros,
    cases n,
    from b,
    from matrix.fold_row_aux M ⟨n, nat.lt_succ_self n⟩ i f b,
end

def matrix.list_of_row (M : matrix (fin m) (fin n) α) : Π (i : fin m), list α :=
 λ j, matrix.fold_row M j (λ _ _ (b : α) (l : list α), l.cons b) list.nil

def matrix.to_list_of_lists_aux (M : matrix (fin m) (fin n) α) : Π (i : fin m) (b : list (list α)), list (list α)
| ⟨0, h₁⟩ b := b.cons (M.list_of_row ⟨0, h₁⟩)
| ⟨k+1, h₁⟩ b := matrix.to_list_of_lists_aux ⟨k, nat.lt_of_succ_lt h₁⟩ (b.cons (M.list_of_row ⟨k+1, h₁⟩))

def matrix.to_list_of_lists (M : matrix (fin m) (fin n) α) : list (list α) :=
begin
    cases m,
    from list.nil,
    from matrix.to_list_of_lists_aux M ⟨m, nat.lt_succ_self m⟩ list.nil,
end

variable [has_repr α]
instance matrix.has_repr : has_repr (matrix (fin m) (fin n) α) :=
begin
    constructor,
    intros M,
    from repr (matrix.to_list_of_lists M)
end