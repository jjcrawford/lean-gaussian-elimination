import ring_theory.matrix
import .gaussian_elimination
import .matrix_repr -- Let us print some things
import analysis.real -- So we can use ℚ

universes u
variables {m n : ℕ}
variable {α : Type u}
variable [division_ring α]
variable [decidable_eq α]


def test1 : matrix (fin 2) (fin 3) ℚ := -- Just like our old friend fast_matrix!
matrix.bang  ![![ 1 , 1,  5 ], 
               ![ 0 , 1,  2 ]]

def test2 : matrix (fin 3) (fin 4) ℚ := -- Just like our old friend fast_matrix!
matrix.bang  ![![ 1 , 1,  5,  4 ], 
               ![ 0 , 1,  2,  5 ],
               ![ 2 , 3,  2,  5 ]]


-- and now, the finale:
example : row_equivalent test1 (gaussian_elimination test1) := gaussian_elimination.row_equivalent test1
#eval test1
#eval gaussian_elimination test1
#check (gaussian_elimination.row_equivalent test1).matrix_implements
--#eval (gaussian_elimination.row_equivalent test1).to_matrix -- Why is this broken? :'(

example : row_equivalent test2 (gaussian_elimination test2) := gaussian_elimination.row_equivalent test2
#eval test2
#eval gaussian_elimination test2