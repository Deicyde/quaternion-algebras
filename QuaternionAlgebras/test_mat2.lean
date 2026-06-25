import QuaternionAlgebras.Matrix
open QuaternionAlgebras
open scoped Quaternion

variable {F : Type*} [Field F] (a b : F) {K : Type*} [Field K] [Algebra F K] (s : K)

example (t x y z : F) : (algebraMap F K t : Matrix (Fin 2) (Fin 2) K) + (algebraMap F K x) • matI s + (algebraMap F K y) • matJ (algebraMap F K b) + (algebraMap F K z) • (matI s * matJ (algebraMap F K b)) = 0 := by
  -- compute entries
  sorry

-- Let me test the entry computation more directly
example (t x y z : F) : 
  ((algebraMap F K t : Matrix (Fin 2) (Fin 2) K) + (algebraMap F K x) • (matI s : Matrix (Fin 2) (Fin 2) K) 
   + (algebraMap F K y) • (matJ (algebraMap F K b) : Matrix (Fin 2) (Fin 2) K)
   + (algebraMap F K z) • (matI s * matJ (algebraMap F K b) : Matrix (Fin 2) (Fin 2) K)) 0 0
   = algebraMap F K t + (algebraMap F K x) * s := by
  simp [matI, matJ, Matrix.mul_fin_two, Matrix.smul_apply, Matrix.add_apply, Matrix.zero_apply, Matrix.one_apply, Matrix.one_fin_two]

