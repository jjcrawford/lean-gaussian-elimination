import data.finsupp

universes u v
variable (α : Type u)
variable [ring α]
variable [decidable_eq α]

@[simp] lemma ite.map (P : Prop) [decidable P] {β γ : Type*} (a b : β) (f : β → γ) :
  f (ite P a b) = ite P (f a) (f b) :=
begin
  split_ifs; refl
end

@[simp] lemma ite.mul_right (P : Prop) [decidable P] (a b c : α) :
  (ite P a b) * c = ite P (a * c) (b * c) := ite.map P a b (λ x, x * c)

-- theorem ite_single {α : Type*} [fintype α] [decidable_eq α] (a₀ : α) {β : Type*} [add_comm_monoid β] (f : α → β) : 

def finsupp_of_ite {α : Type*} [fintype α] [decidable_eq α] (a₀ : α) {β : Type*} [decidable_eq β] [add_comm_monoid β] (f : α → β) : finsupp α β :=
begin
  by_cases h₁ : f a₀ ≠ 0,
  { constructor,
    show α → β,
    from (λ a, ite (a₀ = a) (f a) 0),
    show finset α,
    from finset.singleton a₀,
    intros,
    simp,
    split_ifs,
    rw ←h,
    simp[h₁],
    simp[h],
    from λ h₂, h (eq.symm h₂),
  },
  exact 0
end

-- finsupp of double ite
def finsupp_of_double_ite {α : Type*} [fintype α] [decidable_eq α] (a₀ a₁ : α) {β : Type*} [add_comm_monoid β] (f g : α → β) (h₁ : f a₀ ≠ 0) (h₂ : g a₁ ≠ 0) : finsupp α β :=
begin
  constructor,
  show α → β,
  from (λ a, ite (a₀ = a) (f a) (ite (a₁ = a) (g a) 0)),
  show finset α,
  from finset.singleton a₀ ∪ finset.singleton a₁,
  intros,
  simp,
  split_ifs,
  rw ←h,
  simp[h₁],
  rw ←h_1,
  simp[h₂],
  simp,
  intros h_n,
  cases h_n,
  from h (eq.symm h_n),
  from h_1 (eq.symm h_n),
end

@[simp] lemma finsupp_of_double_ite_eq_double_ite {α : Type*} [fintype α] [decidable_eq α] (a₀ a₁ : α) {β : Type*} [add_comm_monoid β] (f g : α → β) (h₁ : f a₀ ≠ 0) (h₂ : g a₁ ≠ 0) : (λ a, ite (a₀ = a) (f a) (ite (a₁ = a) (g a) 0)) = (finsupp_of_double_ite a₀ a₁ f g h₁ h₂).to_fun :=
begin
  funext,
  by_cases h₁ : (a₀ = a),
  simp[h₁],
  unfold finsupp_of_double_ite,
  simp,
  unfold finsupp_of_double_ite,
end

@[simp] lemma coe_to_fun_to_fun {α : Type*} {β : Type*} [add_comm_monoid β] {fs : finsupp α β} : ⇑(fs) = fs.to_fun := rfl



lemma temp {α : Type*} [fintype α] [decidable_eq α] (a₀ a₁ : α) {β : Type*} [add_comm_monoid β] [decidable_eq β] (f g : α → β) (h₁ : f a₀ ≠ 0) (h₂ : g a₁ ≠ 0) (h_neq : a₀ ≠ a₁) (a : α) (h_p : a = a₀) : (a ∈ ((finsupp.single a₀ (f a₀)).support).val ∧
      ¬(finsupp.single a₀ (f a₀)).to_fun a + (finsupp.single a₁ (g a₁)).to_fun a = 0 ∨
    a ∈ ((finsupp.single a₁ (g a₁)).support).val ∧
      ¬(finsupp.single a₀ (f a₀)).to_fun a + (finsupp.single a₁ (g a₁)).to_fun a = 0) :=
begin
  simp[h_p],
  constructor,
  constructor,

  simp[finsupp.single, h₁],

  intros h_q,
  --(by simp[finsupp.single,h₂, h_neq])
  have H₁ : (finsupp.single a₁ (g a₁)).to_fun a₀ = 0,
  from iff.elim_left (@finsupp.not_mem_support_iff α β _ (finsupp.single a₁ (g a₁)) a₀) (by simp[finsupp.single,h₂, h_neq]),
  -- rw ←h_p at H₁,
  simp[H₁] at h_q,

  have H₂ : (finsupp.single a₀ (f a₀)).to_fun a₀ ≠ 0,
  from iff.elim_left (@finsupp.mem_support_iff α β _ (finsupp.single a₀ (f a₀)) a₀) (by simp[finsupp.single, h₁]),
  from H₂ h_q,
end


@[simp] lemma finsupp_of_double_ite_zip_singles {α : Type*} [fintype α] [decidable_eq α] (a₀ a₁ : α) {β : Type*} [add_comm_monoid β] [decidable_eq β] (f g : α → β) (h₁ : f a₀ ≠ 0) (h₂ : g a₁ ≠ 0) (h_neq : a₀ ≠ a₁) : (finsupp_of_double_ite a₀ a₁ f g h₁ h₂) = (finsupp.single a₀ (f a₀)) + (finsupp.single a₁ (g a₁)) :=
begin

  -- congr,
  unfold finsupp_of_double_ite,
  -- unfold finsupp.zip_with,
  congr,
  show (λ a, _) = (λ a, _),
  funext,
  by_cases h_t : (a₀ = a);
  simp[h_t],
  rw ←h_t,
  have H₁ : (finsupp.single a₁ (g a₁)).to_fun a₀ = 0,
  from iff.elim_left (@finsupp.not_mem_support_iff α β _ (finsupp.single a₁ (g a₁)) a₀) (by
  simp[finsupp.single,h₂, h_neq]),
  rw H₁,
  simp,
  simp[finsupp.single],
  simp,

  by_cases h_t₀ : (a₁ = a),
  simp[h_t₀],
  rw ←h_t₀,
  have H₁ : (finsupp.single a₀ (f a₀)).to_fun a₁ = 0,
  from iff.elim_left (@finsupp.not_mem_support_iff α β _ (finsupp.single a₀ (f a₀)) a₁) (by simp[finsupp.single,h₁, λ x, h_neq (eq.symm x)]),
  rw H₁,
  simp,
  simp[finsupp.single],
  simp,

  simp[h_t₀],
  have H₁ : (finsupp.single a₁ (g a₁)).to_fun a = 0,
  from iff.elim_left (@finsupp.not_mem_support_iff α β _ (finsupp.single a₁ (g a₁)) a) (by simp[finsupp.single, h₂, (λ x, h_t₀ (eq.symm x))]),
  have H₂ : (finsupp.single a₀ (f a₀)).to_fun a = 0,
  from iff.elim_left (@finsupp.not_mem_support_iff α β _ (finsupp.single a₀ (f a₀)) a) (by simp[finsupp.single, h₁, (λ x, h_t (eq.symm x))]),
  rw H₁,
  rw H₂,
  simp,

  -- simp[finset.singleton],
  ext,
  constructor,
  intros h_p,
  simp at h_p,
  cases h_p with h_p h_p,
{
  simp,
  apply temp; assumption,
},
{simp,
apply or.swap,
rw add_comm,
apply temp,
assumption,
assumption,
from λ x, h_neq (eq.symm x),
assumption,
},

intros h_p,
simp at h_p,
cases h_p with h_p h_p,
have H₁, from and.elim_left h_p,

simp,
constructor,
-- by_contra,
-- have H₄ :
have H₃ : ((finsupp.single a₀ (f a₀)).support) = finset.singleton a₀,
simp[finsupp.single, h₁],
rw H₃ at H₁,
-- ext,
simp[finsupp.single, finsupp.support, finset.val] at H₁,
-- constructor,
from H₁,

simp,
apply or.swap,
constructor,
have H₃ : ((finsupp.single a₁ (g a₁)).support) = finset.singleton a₁,
simp[finsupp.single, h₂],
-- simp[H₃] at h_p,
rw H₃ at h_p,
simp[finsupp.single, finsupp.support, finset.val] at h_p,
from and.elim_left h_p,
end


@[simp] lemma finsupp_of_ite_single {α : Type*} [fintype α] [decidable_eq α] (a₀ : α) {β : Type*} [add_comm_monoid β] [decidable_eq β] (f : α → β) : (finsupp_of_ite a₀ f) = finsupp.single a₀ (f a₀) := 
begin
  simp[finsupp.single],
  simp[finsupp_of_ite],
  simp[finset.singleton],
  by_cases h₁ : f a₀ ≠ 0,
  { simp[h₁],
    funext,
    -- congr,
    by_cases h₂ : (a₀ = a);
    simp[h₂], },
  simp at h₁,
  simp [h₁],
  refl,
end

@[simp] lemma finsupp_of_ite_eq_ite {α : Type*} [fintype α] [decidable_eq α] (a₀ : α) {β : Type*} [decidable_eq β] [add_comm_monoid β] (f : α → β) : (λ a, ite (a₀ = a) (f a) 0) = (finsupp_of_ite a₀ f).to_fun :=
begin
  funext,
  by_cases h₂ : (a₀ = a),
  simp[h₂],
  dsimp [finsupp.single],
  simp,
  unfold finsupp_of_ite,
  simp,
  simp[h₂],
  by_cases h₁ : f a₀ ≠ 0,
  simp[h₁],
  simp[h₂],
  simp[h₁],
  refl,
end

section 
open finset
-- open finsupp
lemma finsupp_sum_support_subset {α : Type*} [fintype α] [decidable_eq α] {β : Type*} [add_comm_monoid β] (fs : finsupp α β) : Π (S : finset α), fs.support ⊆ S → S.sum (fs.to_fun) = fs.sum (λ x y, y) := begin
  intros S hS,
  by_cases hT : (S ⊆ fs.support),
  congr,
  apply finset.subset.antisymm; assumption,
  unfold finsupp.sum,
  simp,    
  -- have h₇ : ⇑fs = (fs).to_fun,
  -- refl,
  have h₄, from eq.symm (@finset.sum_sdiff α β fs.support S fs.to_fun _ _ hS),
  apply eq.trans,
  from h₄,
  have h₅ : sum (S \ fs.support) (fs.to_fun) = 0,
  apply @finset.sum_eq_zero α β _ _ fs.to_fun (S \ fs.support),
  intros x,
  have h₆, from iff.elim_left ((@finsupp.not_mem_support_iff α β _ fs) x),
  -- simp at h₆,
  intros h₈,
  apply h₆,
  intros h₉,
  simp at h₈,
  simp at h₉,
  apply h₈.elim_right,
  from h₉,
  -- rw h₇,
  rw h₅,
  simp,
end
end

lemma finset.sum_ite_zero {α : Type*} [fintype α] [decidable_eq α] (a₀ : α) {β : Type*} [add_comm_monoid β] [decidable_eq β] (f : α → β):
  finset.sum finset.univ (λ a, ite (a₀ = a) (f a) 0) = f a₀ := begin

    -- TODO update: cases have been moved earlier.
    -- Outline of proof:  ⊢ finset.sum finset.univ (λ (a : α), ite (a₀ = a) (f a) 0) = f a₀
    /-
        Two cases, h : (f a₀ = 0):

        Case 1: If (f a₀ = 0) :
          The goal is:
          ⊢ finset.sum finset.univ (λ (a : α), ite (a₀ = a) (f a) 0) = 0
          We may show that (λ (a : α), ite (a₀ = a) (f a) 0) = (λ (a : α), 0) by cases.
          ⊢ finset.sum finset.univ (λ (a : α), 0) = 0
          which is resolved by the fact that summation over constant zero is zero.

        Case 2: If (f a₀ ≠ 0) :
          Then (λ (a : α), ite (a₀ = a) (f a) 0) is a finitely-supported (single) function : α →₀ β
          We then have
          ⊢ finset.sum finset.univ ((finsupp.single a₀ (f a₀)).to_fun) = f a₀
          Then summing over the entire finset with a single-supported function is the same
          as summing the result of the function mapped over the support of that function, so
          ⊢ finsupp.sum (finsupp.single a₀ (f a₀)) (λ (x : α) (y : β), y) = f a₀
          Then we may apply the fact that summing over a (single) supported function just picks the value at the point of interest, so
          ⊢ (λ (x : α) (y : β), y) a₀ (f a₀) = f a₀
          which is resolved by refl
    -/

    -- by_cases h : (f a₀ ≠ 0),
    -- Case 1: --------------------------------
    rw finsupp_of_ite_eq_ite,
    rw finsupp_of_ite_single,
    apply eq.trans (@finsupp_sum_support_subset α _ _ β _ (finsupp.single a₀ (f a₀)) finset.univ (by apply finset.subset_univ)), 
    -- from H₃,
    -- show f a₀ ≠ 0, by assumption,
    
    apply eq.trans (@finsupp.sum_single_index α β β _ _ _ _ a₀ (f a₀) (λ x y, y) (by refl)),
    -- from @finsupp.sum_single_index α β β _ _ _ _ a₀ (f a₀) (λ x y, y) (by refl),
    simp,
    
    -- Case 2: --------------------------------
    -- simp at h,
    -- simp[h],
    -- have H₅ : (λ (a : α), ite (a₀ = a) (f a) 0) = (λ (a : α), 0),
    -- funext,
    -- by_cases h₁ : (a₀ = a); simp[h₁],
    -- subst h₁, assumption,
    -- rw H₅,
    -- from @finset.sum_const_zero α β finset.univ _,
  end

-- set_option pp.proofs true

-- lemma finset.sum_ite : finset.sum X (λ a, ite (a₀ = a) (f a) (g a)) = ite (a₀ ∈ X) (f a₀) 0 + finset.sum (sorry) g

lemma finset.sum_ite_zero₂ {α : Type*} [fintype α] [decidable_eq α] (a₀ a₁ : α) {β : Type*} [add_comm_monoid β] [decidable_eq β] (f g : α → β) (h_ne : a₀ ≠ a₁):
  finset.sum finset.univ (λ a, ite (a₀ = a) (f a) (ite (a₁ = a) (g a) 0)) = f a₀ + g a₁ := begin
  by_cases h₁ : (g a₁ = 0),
    -- Case 1:
    have H₁ : (λ (a : α), ite (a₀ = a) (f a) (ite (a₁ = a) (g a) 0)) = (λ (a : α), ite (a₀ = a) (f a) 0),
    funext,
    by_cases h_t : (a₀ = a); simp[h_t],
    by_cases h_t₀ : (a₁ = a), {subst h_t₀, simp[h_t, h₁]}, simp[h_t₀],
    rw H₁,
    rw finset.sum_ite_zero,
    simp[h₁],


    -- Case 2:
    by_cases h₂ : (f a₀ = 0),
    have H₁ : (λ (a : α), ite (a₀ = a) (f a) (ite (a₁ = a) (g a) 0)) = (λ (a : α), ite (a₁ = a) (g a) 0),
    funext,
    by_cases h_t : (a₀ = a); simp[h_t],
    by_cases h_t₀ : (a₁ = a),
    subst h_t₀,
    exfalso, from h_ne h_t,
    simp[h_t₀],
    subst h_t,
    from h₂,
    rw H₁,
    -- rw h₂,
    rw finset.sum_ite_zero,
    simp[h₂],

    -- Case 3:
    rw finsupp_of_double_ite_eq_double_ite,
    rw finsupp_of_double_ite_zip_singles,
    repeat{show _ ≠ _, by assumption},
    
    apply eq.trans (@finsupp_sum_support_subset α _ _ β _ (finsupp.single a₀ (f a₀) + finsupp.single a₁ (g a₁)) finset.univ (by apply finset.subset_univ)),

    unfold finsupp.sum,

    have H₄ : disjoint ((finsupp.single a₀ (f a₀)).support) ((finsupp.single a₁ (g a₁)).support),
    dsimp[finsupp.single],
    -- simp[finsupp.single],
    
    -- simp[finsupp.single],
    simp[h₁, h₂],
    from λ x, h_ne (eq.symm x),

    have H₂, from @finsupp.support_add_eq α β _ _ _ (finsupp.single a₀ (f a₀)) (finsupp.single a₁ (g a₁)) H₄,

    have H₃ : finset.sum ((finsupp.single a₀ (f a₀) + finsupp.single a₁ (g a₁)).support)
      (λ (a : α), (finsupp.single a₀ (f a₀) + finsupp.single a₁ (g a₁)).to_fun a) = finset.sum (((finsupp.single a₀ (f a₀)).support) ∪ ((finsupp.single a₁ (g a₁)).support))
      (λ (a : α), (finsupp.single a₀ (f a₀) + finsupp.single a₁ (g a₁)).to_fun a),
    simp,
    congr,
    from H₂,
    simp,
    rw H₃,
    clear H₃ H₂,
    have H₅, from @finset.sum_union α β (finsupp.single a₀ (f a₀)).support (finsupp.single a₁ (g a₁)).support (λ (a : α), (finsupp.single a₀ (f a₀) + finsupp.single a₁ (g a₁)).to_fun a) _ _ ((iff.elim_left finset.disjoint_iff_inter_eq_empty)  H₄),
    apply eq.trans,
    from H₅,
    clear H₅,

    -- have H₁ : finset.sum ((finsupp.single a₀ (f a₀)).support)
    --     (λ (a : α), (finsupp.single a₀ (f a₀) + finsupp.single a₁ (g a₁)).to_fun a) = f a₀,
    
    have H₄, from @finsupp.add_apply α β _ _ _ (finsupp.single a₀ (f a₀)) (finsupp.single a₁ (g a₁)),
    rw ←coe_to_fun_to_fun,
    have H₅ :
      (λ (x : α), (finsupp.single a₀ (f a₀) + finsupp.single a₁ (g a₁)).to_fun x) =
      (λ (x : α), (finsupp.single a₀ (f a₀)).to_fun x + (finsupp.single a₁ (g a₁)).to_fun x),
    funext,
    have H₄_temp, from @H₄ x,
    simp at H₄_temp,
    from H₄_temp,
    simp,
    rw H₅,
    clear H₄,

    have H₁ : finset.sum ((finsupp.single a₀ (f a₀)).support)
        (λ (x : α), (finsupp.single a₀ (f a₀)).to_fun x + (finsupp.single a₁ (g a₁)).to_fun x) = f a₀,
    -- simp,

    dsimp[finsupp.single],
    simp[h₁, h₂, λ x, h_ne (eq.symm x)],
    simp[H₁],

    clear H₁,
    have H₁ : finset.sum ((finsupp.single a₁ (g a₁)).support)
        (λ (x : α), (finsupp.single a₀ (f a₀)).to_fun x + (finsupp.single a₁ (g a₁)).to_fun x) = g a₁,
    dsimp[finsupp.single],
    simp[h₁, h₂, h_ne],

    simp[H₁],
end
