import QuaternionAlgebras.Matrix
open QuaternionAlgebras
open scoped Quaternion

variable {F : Type*} [Field F] (a b : F)

lemma gk_eq_gi_mul_gj' : gk a b = gi a b * gj a b := by
  ext <;> simp [gi, gj, gk]

#check gk_eq_gi_mul_gj'
