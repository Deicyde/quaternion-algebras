import QuaternionAlgebras.Matrix
open QuaternionAlgebras
open scoped Quaternion

variable {F : Type*} [Field F] (a b : F) {K : Type*} [Field K] [Algebra F K] (s : K)

-- Entry (0,0) of t·1 + x·matI s + y·matJ b' + z·(matI s * matJ b') should be t + x*s
example (t x y z : F) : 
  ((algebraMap F K t • (1 : Matrix (Fin 2) (Fin 2) K)) 
   + (algebraMap F K x • matI s)
   + (algebraMap F K y • matJ (algebraMap F K b))
   + (algebraMap F K z • (matI s * matJ (algebraMap F K b) : Matrix (Fin 2) (Fin 2) K))) 0 0
   = algebraMap F K t + (algebraMap F K x) * s := by
  simp [matI, matJ, Matrix.mul_fin_two, Matrix.smul_apply, Matrix.add_apply, Algebra.smul_def]

-- Entry (0,1) should be b'*(y + z*s)
example (t x y z : F) : 
  ((algebraMap F K t • (1 : Matrix (Fin 2) (Fin 2) K)) 
   + (algebraMap F K x • matI s)
   + (algebraMap F K y • matJ (algebraMap F K b))
   + (algebraMap F K z • (matI s * matJ (algebraMap F K b) : Matrix (Fin 2) (Fin 2) K))) 0 1
   = algebraMap F K b * (algebraMap F K y + (algebraMap F K z) * s) := by
  simp [matI, matJ, Matrix.mul_fin_two, Matrix.smul_apply, Matrix.add_apply, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]

-- Entry (1,0) should be y - z*s
example (t x y z : F) : 
  ((algebraMap F K t • (1 : Matrix (Fin 2) (Fin 2) K)) 
   + (algebraMap F K x • matI s)
   + (algebraMap F K y • matJ (algebraMap F K b))
   + (algebraMap F K z • (matI s * matJ (algebraMap F K b) : Matrix (Fin 2) (Fin 2) K))) 1 0
   = algebraMap F K y - (algebraMap F K z) * s := by
  simp [matI, matJ, Matrix.mul_fin_two, Matrix.smul_apply, Matrix.add_apply, Algebra.smul_def]

-- Entry (1,1) should be t - x*s
example (t x y z : F) : 
  ((algebraMap F K t • (1 : Matrix (Fin 2) (Fin 2) K)) 
   + (algebraMap F K x • matI s)
   + (algebraMap F K y • matJ (algebraMap F K b))
   + (algebraMap F K z • (matI s * matJ (algebraMap F K b) : Matrix (Fin 2) (Fin 2) K))) 1 1
   = algebraMap F K t - (algebraMap F K x) * s := by
  simp [matI, matJ, Matrix.mul_fin_two, Matrix.smul_apply, Matrix.add_apply, Algebra.smul_def]
