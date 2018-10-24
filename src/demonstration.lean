import ring_theory.matrix
import .gaussian_elimination
import .computable_matrix -- I just invoke computable_matrix so I can borrow repr for now
import analysis.real -- So we can use ℚ

universes u
variables {m n : ℕ}
variable {α : Type u}
variable [division_ring α]
variable [decidable_eq α]

def matrix_of_computable_matrix : Π (M : computable_matrix m n α), matrix (fin m) (fin n) α :=
λ M i j, M.read i j

def computable_matrix_of_matrix : Π (M : matrix (fin m) (fin n) α), computable_matrix m n α :=
λ M, ⟨λ i, ⟨λ j, M i j⟩⟩

instance matrix.has_repr [has_repr α] : has_repr (matrix (fin m) (fin n) α) := ⟨λ M,repr (computable_matrix_of_matrix M)⟩


def test_matrix_1 : matrix (fin 2) (fin 3) ℚ := -- Just like our old friend fast_matrix!
matrix_of_computable_matrix (
    ![![ 1 , 1,  5 ], 
      ![ 2 , 1,  2 ]])

def test_matrix_2 : matrix (fin 3) (fin 4) ℚ := 
matrix_of_computable_matrix (
    ![![ 1 , 1,  5,  4], 
      ![ 0 , 1,  2,  2 ],
      ![ 0,  2,  1,  2]])

#eval test_matrix_1
#eval gaussian_elimination test_matrix_1

#eval test_matrix_2
#eval gaussian_elimination test_matrix_2