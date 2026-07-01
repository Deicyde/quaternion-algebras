import QuaternionAlgebras.Matrix
open QuaternionAlgebras
open scoped Quaternion

variable {F : Type*} [Field F] (a b : F) {K : Type*} [Field K] [Algebra F K] (s : K)

-- Compute matI s * matJ (algebraMap F K b) as a matrix
example : matI s * matJ (algebraMap F K b) = !![0, s * algebraMap F K b; -s, 0] := by
  calc
    matI s * matJ (algebraMap F K b)
        = !![s, 0; 0, -s] * !![0, algebraMap F K b; 1, 0] := rfl
    _ = !![s*0 + 0*1, s*algebraMap F K b + 0*0; 0*0 + (-s)*1, 0*algebraMap F K b + (-s)*0] := by
      rw [Matrix.mul_fin_two]
    _ = !![0, s*algebraMap F K b; -s, 0] := by ring_nf

-- Now test entry extraction using Matrix.ext approach
example (t x y z : F) : 
  ((algebraMap F K t) • (1 : Matrix (Fin 2) (Fin 2) K) 
   + (algebraMap F K x) • matI s
   + (algebraMap F K y) • matJ (algebraMap F K b)
   + (algebraMap F K z) • (matI s * matJ (algebraMap F K b))) 0 0
   = algebraMap F K t + (algebraMap F K x) * s := by
  simp [matI, matJ, Matrix.mul_fin_two, Algebra.algebraMap_eq_smul_one, Algebra.smul_def, 
    Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, mul_comm, mul_left_comm, mul_assoc]

-- Alternative: use ring_nf after basic simplification  
example (t x y z : F) : 
  ((algebraMap F K t) • (1 : Matrix (Fin 2) (Fin 2) K) 
   + (algebraMap F K x) • matI s
   + (algebraMap F K y) • matJ (algebraMap F K b)
   + (algebraMap F K z) • (matI s * matJ (algebraMap F K b))) 0 0
   = algebraMap F K t + (algebraMap F K x) * s := by
  calc
    ((algebraMap F K t) • (1 : Matrix (Fin 2) (Fin 2) K) 
      + (algebraMap F K x) • matI s
      + (algebraMap F K y) • matJ (algebraMap F K b)
      + (algebraMap F K z) • (matI s * matJ (algebraMap F K b))) 0 0
        = ((algebraMap F K t) • (1 : Matrix (Fin 2) (Fin 2) K) 
          + (algebraMap F K x) • matI s
          + (algebraMap F K y) • matJ (algebraMap F K b)
          + (algebraMap F K z) • !![0, s*algebraMap F K b; -s, 0]) 0 0 := by
      rw [show matI s * matJ (algebraMap F K b) = !![0, s*algebraMap F K b; -s, 0] from ?_]
    _ = algebraMap F K t + (algebraMap F K x) * s := by
      simp [matI, matJ, Matrix.mul_fin_two, Algebra.smul_def, Matrix.add_apply, Matrix.one_apply]
  -- find the lemma from above
  sorry

-- actually, let's try a completely different approach - use dsimp and case analysis
example (t x y z : F) : 
  ((algebraMap F K t) • (1 : Matrix (Fin 2) (Fin 2) K) 
   + (algebraMap F K x) • matI s
   + (algebraMap F K y) • matJ (algebraMap F K b)
   + (algebraMap F K z) • (matI s * matJ (algebraMap F K b))) 0 0
   = algebraMap F K t + (algebraMap F K x) * s := by
  simp [matI, matJ, Matrix.mul_fin_two, Algebra.algebraMap_eq_smul_one, Matrix.add_apply, 
    Matrix.one_apply, Matrix.smul_apply, Matrix.mul_apply]
  ring_nf

-- Let me try one more time with the correct approach
example (t x y z : F) : 
  ((algebraMap F K t) • (1 : Matrix (Fin 2) (Fin 2) K) 
   + (algebraMap F K x) • matI s
   + (algebraMap F K y) • matJ (algebraMap F K b)
   + (algebraMap F K z) • (matI s * matJ (algebraMap F K b))) 0 0
   = algebraMap F K t + (algebraMap F K x) * s := by
  simp [matI, matJ, Matrix.mul_fin_two, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.mul_apply]
  ring_nf
