import QuaternionAlgebras.Chapter2.Beginnings

/-!
# Quaternion algebras: matrix representations

Over a splitting field `K = F(√a)` containing a root `s` of `x² - a`, the
quaternion algebra `(a,b/F)` embeds into `M₂(K)`.  When `a` is already a square
in `F` (e.g. `a = 1`) the embedding is an isomorphism onto `M₂(F)`.
-/

namespace QuaternionAlgebras

open scoped Quaternion
open Polynomial

variable {F : Type*} [Field F] (a b : F)

/-- A square root of `a` exists in the splitting field of `X² - a`. -/
theorem exists_sqrt (a : F) :
    ∃ s : (X ^ 2 - C a).SplittingField,
      s * s = algebraMap F (X ^ 2 - C a).SplittingField a := by
  have hsplit : ((X ^ 2 - C a).map
      (algebraMap F (X ^ 2 - C a).SplittingField)).Splits :=
    IsSplittingField.splits (X ^ 2 - C a).SplittingField (X ^ 2 - C a)
  have hdeg : ((X ^ 2 - C a).map
      (algebraMap F (X ^ 2 - C a).SplittingField)).degree ≠ 0 := by
    rw [degree_map_eq_of_injective (algebraMap F _).injective,
      degree_X_pow_sub_C (by norm_num) a]; norm_num
  obtain ⟨s, hs⟩ := hsplit.exists_eval_eq_zero hdeg
  refine ⟨s, ?_⟩
  have h0 : s ^ 2 - algebraMap F (X ^ 2 - C a).SplittingField a = 0 := by
    simpa [eval_map, eval₂_sub, eval₂_X_pow, eval₂_C] using hs
  linear_combination sub_eq_zero.mp h0

/-- A chosen square root of `a` in the splitting field of `X² - a`. -/
noncomputable def sqrtA : (X ^ 2 - C a).SplittingField := (exists_sqrt a).choose

lemma sqrtA_mul_self :
    sqrtA a * sqrtA a = algebraMap F (X ^ 2 - C a).SplittingField a :=
  (exists_sqrt a).choose_spec

/-- The matrix `I = !![s, 0; 0, -s]` over a ring `K`. -/
def matI {K : Type*} [Ring K] (s : K) : Matrix (Fin 2) (Fin 2) K := !![s, 0; 0, -s]

/-- The matrix `J = !![0, b; 1, 0]` over a ring `K`. -/
def matJ {K : Type*} [Ring K] (b : K) : Matrix (Fin 2) (Fin 2) K := !![0, b; 1, 0]

/-- Matrix basis relations: with `s² = a`, the matrices `I, J` satisfy
`I² = a • 1`, `J² = b • 1` and `J I = -(I J)`. -/
lemma matrix_basis_relations {K : Type*} [CommRing K] (s a b : K) (hs : s * s = a) :
    matI s * matI s = a • (1 : Matrix (Fin 2) (Fin 2) K) ∧
      matJ b * matJ b = b • (1 : Matrix (Fin 2) (Fin 2) K) ∧
      matJ b * matI s = -(matI s * matJ b) := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [matI, matJ, Matrix.one_fin_two, hs, mul_comm s b]

/-- The matrix embedding (Voight 2.3.1): the `F`-algebra map `(a,b/F) → M₂(K)`,
`i ↦ I`, `j ↦ J`, `k ↦ IJ`, as the lift of the basis `(I, J, IJ)`. -/
noncomputable def matrixHom :
    ℍ[F, a, 0, b] →ₐ[F] Matrix (Fin 2) (Fin 2) (X ^ 2 - C a).SplittingField :=
  QuaternionAlgebra.Basis.liftHom
    { i := matI (sqrtA a)
      j := matJ (algebraMap F _ b)
      k := matI (sqrtA a) * matJ (algebraMap F _ b)
      i_mul_i := by
        obtain ⟨hI, _, _⟩ := matrix_basis_relations (sqrtA a)
          (algebraMap F _ a) (algebraMap F _ b) (sqrtA_mul_self a)
        rw [hI]; simp [algebraMap_smul]
      j_mul_j := by
        obtain ⟨_, hJ, _⟩ := matrix_basis_relations (sqrtA a)
          (algebraMap F _ a) (algebraMap F _ b) (sqrtA_mul_self a)
        rw [hJ]; simp [algebraMap_smul]
      i_mul_j := rfl
      j_mul_i := by
        obtain ⟨_, _, hJI⟩ := matrix_basis_relations (sqrtA a)
          (algebraMap F _ a) (algebraMap F _ b) (sqrtA_mul_self a)
        rw [hJI]; simp }

@[simp] lemma matrixHom_gi : matrixHom a b (gi a b) = matI (sqrtA a) := by
  simp [matrixHom, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift, gi]

@[simp] lemma matrixHom_gj :
    matrixHom a b (gj a b) = matJ (algebraMap F (X ^ 2 - C a).SplittingField b) := by
  simp [matrixHom, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift, gj]

/-- Key injectivity: over a field extension `K/F` with a square root `s` of `a`
(`a, b ≠ 0`, `char F ≠ 2`), an `F`-algebra map `(a,b/F) → M₂(K)` sending the
generators to `I`, `J` is injective. -/
lemma matI_matJ_injective {K : Type*} [Field K] [Algebra F K]
    (ha : a ≠ 0) (hb : b ≠ 0) (htwo : (2 : F) ≠ 0) (s : K)
    (hs : s * s = algebraMap F K a)
    (φ : ℍ[F, a, 0, b] →ₐ[F] Matrix (Fin 2) (Fin 2) K)
    (h1 : φ (gi a b) = matI s) (h2 : φ (gj a b) = matJ (algebraMap F K b)) :
    Function.Injective φ := by
  have ρinj : Function.Injective (algebraMap F K) := (algebraMap F K).injective
  have hsne : s ≠ 0 := fun h => ha (ρinj (by rw [map_zero, ← hs, h, mul_zero]))
  have hbne : algebraMap F K b ≠ 0 := by simpa using ρinj.ne hb
  have h2K : (2 : K) ≠ 0 := fun h => htwo (ρinj (by rw [map_ofNat, map_zero]; exact h))
  refine (injective_iff_map_eq_zero φ).2 fun α hα => ?_
  have hk : φ (gk a b) = matI s * matJ (algebraMap F K b) := by
    rw [gk_eq_gi_mul_gj, map_mul, h1, h2]
  have hdecomp : α = α.re • (1 : ℍ[F, a, 0, b]) + α.imI • gi a b
      + α.imJ • gj a b + α.imK • gk a b := by
    apply QuaternionAlgebra.ext <;> simp [gi, gj, gk]
  rw [hdecomp] at hα
  simp only [map_add, map_smul, map_one, h1, h2, hk] at hα
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
  have hre : algebraMap F K α.re = 0 := by
    have e : (2 : K) * algebraMap F K α.re = 0 := by linear_combination h00 + h11
    exact (mul_eq_zero.mp e).resolve_left h2K
  have himI : algebraMap F K α.imI = 0 := by
    have e : (2 : K) * (algebraMap F K α.imI * s) = 0 := by linear_combination h00 - h11
    exact (mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left h2K)).resolve_right hsne
  have hsum : algebraMap F K α.imJ + algebraMap F K α.imK * s = 0 :=
    (mul_eq_zero.mp (by linear_combination h01 :
      algebraMap F K b * (algebraMap F K α.imJ + algebraMap F K α.imK * s) = 0)).resolve_left hbne
  have himJ : algebraMap F K α.imJ = 0 := by
    have e : (2 : K) * algebraMap F K α.imJ = 0 := by linear_combination hsum + h10
    exact (mul_eq_zero.mp e).resolve_left h2K
  have himK : algebraMap F K α.imK = 0 := by
    have e : (2 : K) * (algebraMap F K α.imK * s) = 0 := by linear_combination hsum - h10
    exact (mul_eq_zero.mp ((mul_eq_zero.mp e).resolve_left h2K)).resolve_right hsne
  have mz : (0 : K) = algebraMap F K 0 := (map_zero _).symm
  apply QuaternionAlgebra.ext <;>
    simp [ρinj (hre.trans mz), ρinj (himI.trans mz),
      ρinj (himJ.trans mz), ρinj (himK.trans mz)]

/-- Matrix embedding (Voight 2.3.1): for `a, b ≠ 0` and `char F ≠ 2`, the matrix
homomorphism `matrixHom` into `M₂(F(√a))` is injective, hence an isomorphism onto
its image. -/
lemma matrixHom_injective (ha : a ≠ 0) (hb : b ≠ 0) (htwo : (2 : F) ≠ 0) :
    Function.Injective (matrixHom a b) :=
  matI_matJ_injective a b ha hb htwo (sqrtA a) (sqrtA_mul_self a) (matrixHom a b)
    (matrixHom_gi a b) (matrixHom_gj a b)

/-- The split quaternion algebra `(1,b/F)` is isomorphic to `M₂(F)`, given
explicitly by `i ↦ !![1,0;0,-1]`, `j ↦ !![0,b;1,0]`.  In particular
`(1,1/F) ≅ M₂(F)`. -/
noncomputable def split_matrix (b : F) (hb : b ≠ 0) (htwo : (2 : F) ≠ 0) :
    ℍ[F, 1, 0, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F := by
  obtain ⟨hI, hJ, hJI⟩ := matrix_basis_relations (1 : F) (1 : F) b (by ring)
  let qb : QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) F) 1 0 b :=
    { i := matI 1
      j := matJ b
      k := matI 1 * matJ b
      i_mul_i := by rw [hI]; simp
      j_mul_j := hJ
      i_mul_j := rfl
      j_mul_i := by rw [hJI]; simp }
  have h1 : qb.liftHom (gi 1 b) = matI 1 := by
    simp [qb, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift, gi]
  have h2 : qb.liftHom (gj 1 b) = matJ (algebraMap F F b) := by
    simp [qb, QuaternionAlgebra.Basis.liftHom_apply, QuaternionAlgebra.Basis.lift, gj]
  have hinj : Function.Injective qb.liftHom :=
    matI_matJ_injective (1 : F) b one_ne_zero hb htwo (1 : F) (by simp) qb.liftHom h1 h2
  have hfin : Module.finrank F ℍ[F, 1, 0, b]
      = Module.finrank F (Matrix (Fin 2) (Fin 2) F) := by
    rw [dim_four, Module.finrank_matrix]; simp
  exact AlgEquiv.ofBijective qb.liftHom ⟨hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := qb.liftHom.toLinearMap) hfin).mp hinj⟩

/-! ### The left regular representation over `K = F[i]`

Following Voight 2.3.8–2.3.9, we view `B = (a,b/F)` as a (right) module over the
commutative `F`-algebra `K = F[i] ≅ F[X]/(X²-a)` and realize the left regular
representation inside `End_K B`. -/

/-- `i² = a` in `(a,b/F)`. -/
lemma gi_mul_gi : gi a b * gi a b = algebraMap F ℍ[F, a, 0, b] a := by
  rw [Algebra.algebraMap_eq_smul_one]; ext <;> simp [gi]

/-- `K = F[i]`, modeled as `F[X]/(X²-a)`. -/
abbrev RootField := AdjoinRoot (X ^ 2 - C a)

/-- Evaluation `F[X] → B` at `i` (its image is the commutative subring `F[i]`). -/
noncomputable def evalGi : Polynomial F →+* ℍ[F, a, 0, b] :=
  Polynomial.eval₂RingHom' (algebraMap F _) (gi a b)
    (fun c => Algebra.commute_algebraMap_left c (gi a b))

lemma evalGi_root : evalGi a b (X ^ 2 - C a) = 0 := by
  simp only [evalGi, Polynomial.eval₂RingHom'_apply, eval₂_sub, eval₂_X_pow, eval₂_C]
  rw [pow_two, gi_mul_gi, sub_self]

/-- The embedding `ι : K = F[i] → B`. -/
noncomputable def rootι : RootField a →+* ℍ[F, a, 0, b] :=
  Ideal.Quotient.lift _ (evalGi a b) <| by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, evalGi_root, mul_zero]

/-- `B = (a,b/F)` is a (right) `K`-module, `k • β := β · ι(k)`.  This is a module
because `K` is commutative, so its image `ι(K) = F[i]` is a commutative subring. -/
noncomputable instance : Module (RootField a) ℍ[F, a, 0, b] where
  smul k β := β * rootι a b k
  one_smul β := by show β * rootι a b 1 = β; rw [map_one, mul_one]
  mul_smul k₁ k₂ β := by
    show β * rootι a b (k₁ * k₂) = β * rootι a b k₂ * rootι a b k₁
    rw [mul_comm k₁ k₂, map_mul, mul_assoc]
  smul_zero k := by show (0 : ℍ[F, a, 0, b]) * rootι a b k = 0; rw [zero_mul]
  smul_add k β₁ β₂ := by
    show (β₁ + β₂) * rootι a b k = β₁ * rootι a b k + β₂ * rootι a b k; rw [add_mul]
  add_smul k₁ k₂ β := by
    show β * rootι a b (k₁ + k₂) = β * rootι a b k₁ + β * rootι a b k₂; rw [map_add, mul_add]
  zero_smul β := by show β * rootι a b 0 = 0; rw [map_zero, mul_zero]

lemma rootField_smul_def (k : RootField a) (β : ℍ[F, a, 0, b]) :
    k • β = β * rootι a b k := rfl

/-- The left regular representation over `K = F[i]` (Voight (2.3.9)): the ring
homomorphism `λ : B → End_K B`, `α ↦ (β ↦ α β)`, each `λ_α` being `K`-linear
because left and right multiplication commute. -/
noncomputable def leftRegRepK :
    ℍ[F, a, 0, b] →+* Module.End (RootField a) ℍ[F, a, 0, b] where
  toFun α :=
    { toFun := fun β => α * β
      map_add' := fun β₁ β₂ => mul_add α β₁ β₂
      map_smul' := fun k β => by
        simp only [RingHom.id_apply, rootField_smul_def, ← mul_assoc] }
  map_one' := LinearMap.ext fun β => by show (1 : ℍ[F, a, 0, b]) * β = β; rw [one_mul]
  map_mul' α α' := LinearMap.ext fun β => by
    show (α * α') * β = α * (α' * β); rw [mul_assoc]
  map_zero' := LinearMap.ext fun β => by show (0 : ℍ[F, a, 0, b]) * β = 0; rw [zero_mul]
  map_add' α α' := LinearMap.ext fun β => by
    show (α + α') * β = α * β + α' * β; rw [add_mul]

@[simp] lemma leftRegRepK_apply (α β : ℍ[F, a, 0, b]) :
    leftRegRepK a b α β = α * β := rfl

/-- The left regular representation over `K` is faithful (injective). -/
lemma leftRegRepK_faithful : Function.Injective (leftRegRepK a b) := by
  refine (injective_iff_map_eq_zero _).2 fun α h => ?_
  have hα : leftRegRepK a b α 1 = 0 := by rw [h]; rfl
  simpa using hα

/-! ### The Hamiltonians inside `M₂(ℂ)` -/

/-- The embedding (Voight (2.4.1)) of the real Hamiltonians `ℍ = (-1,-1/ℝ)` into
`M₂(ℂ)`, `i ↦ !![I,0;0,-I]`, `j ↦ !![0,-1;1,0]`; explicitly
`t + xi + yj + zk ↦ !![t+xI, -y-zI; y-zI, t-xI]`.  This is the matrix embedding
with `a = b = -1` and `√(-1) = I ∈ ℂ`. -/
noncomputable def hamiltonToComplex :
    ℍ[ℝ, -1, 0, -1] →ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  QuaternionAlgebra.Basis.liftHom
    { i := matI Complex.I
      j := matJ (-1 : ℂ)
      k := matI Complex.I * matJ (-1 : ℂ)
      i_mul_i := by
        rw [(matrix_basis_relations Complex.I (-1 : ℂ) (-1 : ℂ) Complex.I_mul_I).1,
          zero_smul, add_zero, ← algebraMap_smul ℂ (-1 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℂ)]; simp
      j_mul_j := by
        rw [(matrix_basis_relations Complex.I (-1 : ℂ) (-1 : ℂ) Complex.I_mul_I).2.1,
          ← algebraMap_smul ℂ (-1 : ℝ) (1 : Matrix (Fin 2) (Fin 2) ℂ)]; simp
      i_mul_j := rfl
      j_mul_i := by
        rw [(matrix_basis_relations Complex.I (-1 : ℂ) (-1 : ℂ) Complex.I_mul_I).2.2,
          zero_smul, zero_sub] }

/-- Explicit matrix form of the Hamiltonian embedding:
`t + xi + yj + zk ↦ !![t+xI, -y-zI; y-zI, t-xI]`. -/
lemma hamiltonToComplex_apply (α : ℍ[ℝ, -1, 0, -1]) :
    hamiltonToComplex α =
      !![(α.re : ℂ) + (α.imI : ℂ) * Complex.I, -(α.imJ : ℂ) - (α.imK : ℂ) * Complex.I;
         (α.imJ : ℂ) - (α.imK : ℂ) * Complex.I, (α.re : ℂ) - (α.imI : ℂ) * Complex.I] := by
  simp only [hamiltonToComplex, QuaternionAlgebra.Basis.liftHom_apply,
    QuaternionAlgebra.Basis.lift, matI, matJ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Algebra.algebraMap_eq_smul_one, Complex.real_smul,
      Matrix.one_fin_two] <;>
    ring

/-- Voight (2.4.7), trace: the trace of the matrix embedding is twice the real part. -/
lemma hamiltonToComplex_trace (α : ℍ[ℝ, -1, 0, -1]) :
    (hamiltonToComplex α).trace = (2 * α.re : ℝ) := by
  rw [hamiltonToComplex_apply, Matrix.trace_fin_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
    Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
  push_cast; ring

/-- Voight (2.4.7), determinant: the determinant of the matrix embedding is the
reduced norm `normSq`. -/
lemma hamiltonToComplex_det (α : ℍ[ℝ, -1, 0, -1]) :
    (hamiltonToComplex α).det = (Quaternion.normSq α : ℝ) := by
  rw [hamiltonToComplex_apply, Matrix.det_fin_two_of, Quaternion.normSq_def']
  push_cast
  linear_combination (-(α.imI : ℂ) ^ 2 - (α.imK : ℂ) ^ 2) * Complex.I_sq

/-- The Hamiltonian embedding into `M₂(ℂ)` is injective. -/
lemma hamiltonToComplex_injective : Function.Injective hamiltonToComplex :=
  matI_matJ_injective (-1) (-1) (by norm_num) (by norm_num) (by norm_num)
    Complex.I (by rw [Complex.I_mul_I]; simp) hamiltonToComplex
    (by simp [hamiltonToComplex, QuaternionAlgebra.Basis.liftHom_apply,
      QuaternionAlgebra.Basis.lift, gi])
    (by simp [hamiltonToComplex, QuaternionAlgebra.Basis.liftHom_apply,
      QuaternionAlgebra.Basis.lift, gj])

end QuaternionAlgebras
