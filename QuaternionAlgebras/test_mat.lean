import QuaternionAlgebras.Matrix
open QuaternionAlgebras
open scoped Quaternion

variable {F : Type*} [Field F] (a b : F) {K : Type*} [Field K] [Algebra F K] (s : K)

-- Compute matI s * matJ (algebraMap F K b)
example : matI s * matJ (algebraMap F K b) = !![0, s * algebraMap F K b; -s, 0] := by
  calc
    matI s * matJ (algebraMap F K b) = !![s, 0; 0, -s] * !![0, algebraMap F K b; 1, 0] := rfl
    _ = !![s*0 + 0*1, s*algebraMap F K b + 0*0; 0*0 + (-s)*1, 0*algebraMap F K b + (-s)*0] := by
      rw [Matrix.mul_fin_two]
    _ = !![0, s*algebraMap F K b; -s, 0] := by ring

#check Matrix.mul_fin_two
