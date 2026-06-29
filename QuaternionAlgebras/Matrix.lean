import QuaternionAlgebras.Beginnings

/-!
# Quaternion algebras: matrix representations

Over a splitting field `K = F(√a)` containing a root `s` of `x² - a`, the
quaternion algebra `(a,b/F)` embeds into `M₂(K)`.  When `a` is already a square
in `F` (e.g. `a = 1`) the embedding is an isomorphism onto `M₂(F)`.
-/

namespace QuaternionAlgebras

open scoped Quaternion

variable {F : Type*} [Field F] (a b : F)

/-- The matrix `I = !![s, 0; 0, -s]` over a ring `K`. -/
def matI {K : Type*} [Ring K] (s : K) : Matrix (Fin 2) (Fin 2) K :=
  !![s, 0; 0, -s]

/-- The matrix `J = !![0, b; 1, 0]` over a ring `K`. -/
def matJ {K : Type*} [Ring K] (b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![0, b; 1, 0]

/-- Matrix basis relations: with `s² = a`, the matrices `I, J` satisfy
`I² = a • 1`, `J² = b • 1` and `J I = -(I J)`. -/
lemma matrix_basis_relations {K : Type*} [CommRing K] (s a b : K) (hs : s * s = a) :
    matI s * matI s = a • (1 : Matrix (Fin 2) (Fin 2) K) ∧
      matJ b * matJ b = b • (1 : Matrix (Fin 2) (Fin 2) K) ∧
      matJ b * matI s = -(matI s * matJ b) := by
  have hI : matI s * matI s = a • (1 : Matrix (Fin 2) (Fin 2) K) := by
    calc
      matI s * matI s = !![s, 0; 0, -s] * !![s, 0; 0, -s] := rfl
      _ = !![s*s + 0*0, s*0 + 0*(-s); 0*s + (-s)*0, 0*0 + (-s)*(-s)] := by
        rw [Matrix.mul_fin_two]
      _ = !![s*s, 0; 0, s*s] := by
        simp
      _ = !![a, 0; 0, a] := by rw [hs]
      _ = a • !![1, 0; 0, 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp
      _ = a • (1 : Matrix (Fin 2) (Fin 2) K) := by rw [Matrix.one_fin_two]
  have hJ : matJ b * matJ b = b • (1 : Matrix (Fin 2) (Fin 2) K) := by
    calc
      matJ b * matJ b = !![0, b; 1, 0] * !![0, b; 1, 0] := rfl
      _ = !![0*0 + b*1, 0*b + b*0; 1*0 + 0*1, 1*b + 0*0] := by
        rw [Matrix.mul_fin_two]
      _ = !![b, 0; 0, b] := by
        simp
      _ = b • !![1, 0; 0, 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp
      _ = b • (1 : Matrix (Fin 2) (Fin 2) K) := by rw [Matrix.one_fin_two]
  have hJI : matJ b * matI s = -(matI s * matJ b) := by
    calc
      matJ b * matI s = !![0, b; 1, 0] * !![s, 0; 0, -s] := rfl
      _ = !![0*s + b*0, 0*0 + b*(-s); 1*s + 0*0, 1*0 + 0*(-s)] := by
        rw [Matrix.mul_fin_two]
      _ = !![0, -(b * s); s, 0] := by
        simp
      _ = -(!![0, s*b; -s, 0]) := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [mul_comm b s]
      _ = -(!![s, 0; 0, -s] * !![0, b; 1, 0]) := by
        rw [Matrix.mul_fin_two]
        simp
      _ = -(matI s * matJ b) := rfl
  exact ⟨hI, hJ, hJI⟩

/-- The matrix embedding (Voight 2.3.1), stated constructively: over a field
extension `K/F` containing a square root `s` of `a`, the explicit `F`-algebra
homomorphism `(a,b/F) → M₂(K)` sending `i ↦ I`, `j ↦ J`, `k ↦ IJ`, built as the
lift of the quaternion basis `(I, J, IJ)`. -/
noncomputable def matrixHom {K : Type*} [Field K] [Algebra F K] (s : K)
    (hs : s * s = algebraMap F K a) :
    ℍ[F, a, 0, b] →ₐ[F] Matrix (Fin 2) (Fin 2) K :=
  QuaternionAlgebra.Basis.liftHom
    { i := matI s
      j := matJ (algebraMap F K b)
      k := matI s * matJ (algebraMap F K b)
      i_mul_i := by
        obtain ⟨hI, _, _⟩ := matrix_basis_relations s (algebraMap F K a) (algebraMap F K b) hs
        calc
          matI s * matI s = (algebraMap F K a) • (1 : Matrix (Fin 2) (Fin 2) K) := hI
          _ = a • (1 : Matrix (Fin 2) (Fin 2) K) := by simp
          _ = a • (1 : Matrix (Fin 2) (Fin 2) K) + (0 : F) • matI s := by simp
      j_mul_j := by
        obtain ⟨_, hJ, _⟩ := matrix_basis_relations s (algebraMap F K a) (algebraMap F K b) hs
        calc
          matJ (algebraMap F K b) * matJ (algebraMap F K b)
              = (algebraMap F K b) • (1 : Matrix (Fin 2) (Fin 2) K) := hJ
          _ = b • (1 : Matrix (Fin 2) (Fin 2) K) := by simp
      i_mul_j := rfl
      j_mul_i := by
        obtain ⟨_, _, hJI⟩ := matrix_basis_relations s (algebraMap F K a) (algebraMap F K b) hs
        calc
          matJ (algebraMap F K b) * matI s = -(matI s * matJ (algebraMap F K b)) := hJI
          _ = (0 : F) • matJ (algebraMap F K b) - (matI s * matJ (algebraMap F K b)) := by simp }

@[simp] lemma matrixHom_gi {K : Type*} [Field K] [Algebra F K] (s : K)
    (hs : s * s = algebraMap F K a) : matrixHom a b s hs (gi a b) = matI s := by
  simp [matrixHom, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift, gi]

@[simp] lemma matrixHom_gj {K : Type*} [Field K] [Algebra F K] (s : K)
    (hs : s * s = algebraMap F K a) :
    matrixHom a b s hs (gj a b) = matJ (algebraMap F K b) := by
  simp [matrixHom, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift, gj]

@[simp] lemma matrixHom_gk {K : Type*} [Field K] [Algebra F K] (s : K)
    (hs : s * s = algebraMap F K a) :
    matrixHom a b s hs (gk a b) = matI s * matJ (algebraMap F K b) := by
  simp [matrixHom, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift, gk]

/-- Matrix embedding (Voight 2.3.1): for `a, b ≠ 0` and `char F ≠ 2`, the matrix
homomorphism `matrixHom` is injective, hence an isomorphism onto its image. -/
lemma matrixHom_injective {K : Type*} [Field K] [Algebra F K]
    (ha : a ≠ 0) (hb : b ≠ 0) (htwo : (2 : F) ≠ 0) (s : K)
    (hs : s * s = algebraMap F K a) :
    Function.Injective (matrixHom a b s hs) := by
  have ρinj : Function.Injective (algebraMap F K) := (algebraMap F K).injective
  have hsne : s ≠ 0 := by
    intro h
    exact ha (ρinj (by rw [map_zero, ← hs, h, mul_zero]))
  have hbne : algebraMap F K b ≠ 0 := by simpa using ρinj.ne hb
  have h2K : (2 : K) ≠ 0 := by
    intro h
    apply htwo
    apply ρinj
    rw [map_ofNat, map_zero]; exact h
  refine (injective_iff_map_eq_zero _).2 fun α hα => ?_
  have hdecomp : α = α.re • (1 : ℍ[F, a, 0, b]) + α.imI • gi a b
      + α.imJ • gj a b + α.imK • gk a b := by
    apply QuaternionAlgebra.ext <;> simp [gi, gj, gk]
  rw [hdecomp] at hα
  simp only [map_add, map_smul, map_one, matrixHom_gi, matrixHom_gj, matrixHom_gk] at hα
  have h00 := congrFun (congrFun hα 0) 0
  have h01 := congrFun (congrFun hα 0) 1
  have h10 := congrFun (congrFun hα 1) 0
  have h11 := congrFun (congrFun hα 1) 1
  simp only [matI, matJ, Matrix.one_fin_two, Matrix.add_apply, Matrix.smul_apply,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.zero_apply, smul_zero,
    mul_zero, mul_one, zero_mul, add_zero, zero_add] at h00 h01 h10 h11
  simp only [Algebra.smul_def, mul_one, mul_neg] at h00 h01 h10 h11
  -- h00 : ρre + ρimI*s = 0 ; h11 : ρre - ρimI*s = 0
  -- h10 : ρimJ - ρimK*s = 0 ; h01 : ρimJ*ρb + ρimK*(s*ρb) = 0
  have hre : algebraMap F K α.re = 0 := by
    have e : (2 : K) * algebraMap F K α.re = 0 := by linear_combination h00 + h11
    exact (mul_eq_zero.mp e).resolve_left h2K
  have himI : algebraMap F K α.imI = 0 := by
    have e : (2 : K) * (algebraMap F K α.imI * s) = 0 := by linear_combination h00 - h11
    have e' : algebraMap F K α.imI * s = 0 := (mul_eq_zero.mp e).resolve_left h2K
    exact (mul_eq_zero.mp e').resolve_right hsne
  have hsum : algebraMap F K α.imJ + algebraMap F K α.imK * s = 0 := by
    have e : algebraMap F K b * (algebraMap F K α.imJ + algebraMap F K α.imK * s) = 0 := by
      linear_combination h01
    exact (mul_eq_zero.mp e).resolve_left hbne
  have himJ : algebraMap F K α.imJ = 0 := by
    have e : (2 : K) * algebraMap F K α.imJ = 0 := by linear_combination hsum + h10
    exact (mul_eq_zero.mp e).resolve_left h2K
  have himK : algebraMap F K α.imK = 0 := by
    have e : (2 : K) * (algebraMap F K α.imK * s) = 0 := by linear_combination hsum - h10
    have e' : algebraMap F K α.imK * s = 0 := (mul_eq_zero.mp e).resolve_left h2K
    exact (mul_eq_zero.mp e').resolve_right hsne
  have e1 : α.re = 0 := ρinj (by rw [map_zero]; exact hre)
  have e2 : α.imI = 0 := ρinj (by rw [map_zero]; exact himI)
  have e3 : α.imJ = 0 := ρinj (by rw [map_zero]; exact himJ)
  have e4 : α.imK = 0 := ρinj (by rw [map_zero]; exact himK)
  apply QuaternionAlgebra.ext <;> simp [e1, e2, e3, e4]

/-- The split quaternion algebra `(1,b/F)` is isomorphic to `M₂(F)`.  In
particular `(1,1/F) ≅ M₂(F)`. -/
theorem split_matrix (b : F) :
    Nonempty (ℍ[F, 1, 0, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by sorry

end QuaternionAlgebras
