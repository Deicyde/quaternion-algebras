import Mathlib

/-!
# Rotations: the double cover `ℍ¹ → SO(3)`

For `α` in the unit Hamiltonians `ℍ¹ = {α : normSq α = 1}`, conjugation
`v ↦ α v α⁻¹` is an `ℝ`-linear isometry of the pure quaternions `ℍ⁰ ≅ ℝ³` of
determinant one, hence an element of `SO(3) = Matrix.specialOrthogonalGroup
(Fin 3) ℝ`.  The resulting map `ℍ¹ → SO(3)` is a surjective group homomorphism
with kernel `{±1}`.

The Physlib lemmas `GroupTheory.SO3.exists_stationary_vec` and
`EuclideanGroup.linearIsometryEquivToOrthogonal` referenced in the blueprint are
not available in Mathlib, so the corresponding statements
(`isometry_to_so`, `so3_axis_angle`) are phrased directly in Mathlib terms.
-/

namespace QuaternionAlgebras

open scoped Quaternion Matrix RealInnerProductSpace

/-- The real scalar action commutes with conjugation, making `Quaternion ℝ` a
star module over `ℝ`. -/
instance : StarModule ℝ (Quaternion ℝ) := ⟨fun r x => by ext <;> simp⟩

/-- A quaternion is *skew-adjoint* when `star q = -q`. Mathlib ships
`IsSelfAdjoint` but leaves `IsSkewAdjoint` as a TODO, so we introduce it here, in
the `Quaternion` namespace so that dot notation `q.IsSkewAdjoint` is available. -/
def _root_.Quaternion.IsSkewAdjoint (q : Quaternion ℝ) : Prop := star q = -q

/-- For real quaternions, skew-adjointness is exactly the vanishing of the real
part. -/
@[simp] lemma isSkewAdjoint_iff_re (q : Quaternion ℝ) :
    q.IsSkewAdjoint ↔ q.re = 0 := Quaternion.star_eq_neg

/-- Multiplicativity of the norm: `normSq (α β) = normSq α * normSq β`. -/
lemma normSq_mul (α β : Quaternion ℝ) :
    Quaternion.normSq (α * β) = Quaternion.normSq α * Quaternion.normSq β :=
  map_mul Quaternion.normSq α β

/-- Membership in the pure quaternions `skewAdjoint.submodule ℝ (Quaternion ℝ)`
is exactly the vanishing of the real part. -/
@[simp] lemma mem_skewAdjoint_submodule_iff (q : Quaternion ℝ) :
    q ∈ skewAdjoint.submodule ℝ (Quaternion ℝ) ↔ q.re = 0 := by
  rw [← Quaternion.star_eq_neg]
  exact skewAdjoint.mem_iff

/-- Square of a pure quaternion: `v` is pure iff `v² = -normSq v`.  In particular
for pure `v` one has `v² = -normSq v ≤ 0`. -/
lemma pure_square (v : Quaternion ℝ) :
    v.IsSkewAdjoint ↔
      v ^ 2 = -((Quaternion.normSq v : ℝ) : Quaternion ℝ) := by
  rw [isSkewAdjoint_iff_re]
  simpa using (Quaternion.sq_eq_neg_normSq (a := v)).symm

/-- Real part of a product of pure quaternions: minus their inner product (the
standard Euclidean dot product on `ℍ`). Only `w` needs to be pure. -/
lemma pure_product_re (v w : Quaternion ℝ)
    (_hv : v.IsSkewAdjoint)
    (hw : w.IsSkewAdjoint) :
    (v * w).re = -⟪v, w⟫ := by
  have hwstar : star w = -w := Quaternion.star_eq_neg.mpr ((isSkewAdjoint_iff_re w).mp hw)
  rw [Quaternion.inner_def, hwstar, mul_neg]
  simp

/-- The imaginary part of a quaternion as a vector in `ℝ³`. -/
def imVec (v : Quaternion ℝ) : Fin 3 → ℝ := ![v.imI, v.imJ, v.imK]

/-- The pure quaternion whose imaginary part is a given vector of `ℝ³`. -/
def ofImVec (u : Fin 3 → ℝ) : Quaternion ℝ := ⟨0, u 0, u 1, u 2⟩

/-- The cross product `v × w` of two quaternions, packaged as a pure quaternion,
reusing Mathlib's `crossProduct` on their imaginary parts. -/
def crossQuat (v w : Quaternion ℝ) : Quaternion ℝ :=
  ofImVec (imVec v ⨯₃ imVec w)

/-- Imaginary part of a product of pure quaternions is their cross product. -/
lemma pure_product_im (v w : Quaternion ℝ)
    (hv : v.IsSkewAdjoint)
    (hw : w.IsSkewAdjoint) :
    imVec (v * w) = imVec v ⨯₃ imVec w := by
  rw [isSkewAdjoint_iff_re] at hv hw
  funext i
  fin_cases i <;>
    simp [imVec, cross_apply, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, hv, hw]
  all_goals ring

/-- Product of pure quaternions: `vw = -(v·w) + (v×w)`, with the dot product as
the real part and the cross product as the (pure) imaginary part. -/
lemma pure_product (v w : Quaternion ℝ)
    (hv : v.IsSkewAdjoint)
    (hw : w.IsSkewAdjoint) :
    v * w = -((⟪v, w⟫ : ℝ) : Quaternion ℝ) + crossQuat v w := by
  have hre := pure_product_re v w hv hw
  have him := pure_product_im v w hv hw
  have h0 := congrFun him 0
  have h1 := congrFun him 1
  have h2 := congrFun him 2
  simp only [imVec, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
  ext <;>
    simp [crossQuat, ofImVec, imVec, hre, h0, h1, h2]

/-- Orthogonality criterion (a): the product of two pure quaternions is again
pure (skew-adjoint) iff they are orthogonal. -/
lemma pure_mul_isSkewAdjoint_iff (v w : Quaternion ℝ)
    (hv : v.IsSkewAdjoint) (hw : w.IsSkewAdjoint) :
    (v * w).IsSkewAdjoint ↔ ⟪v, w⟫ = 0 := by
  rw [isSkewAdjoint_iff_re, pure_product_re v w hv hw, neg_eq_zero]

/-- Orthogonality criterion (b): two pure quaternions anticommute
(`wv = -vw`) iff they are orthogonal. -/
lemma pure_anticomm_iff (v w : Quaternion ℝ)
    (hv : v.IsSkewAdjoint) (hw : w.IsSkewAdjoint) :
    w * v = -(v * w) ↔ ⟪v, w⟫ = 0 := by
  have hvre : v.re = 0 := (isSkewAdjoint_iff_re v).mp hv
  have hwre : w.re = 0 := (isSkewAdjoint_iff_re w).mp hw
  have hdot : (⟪v, w⟫ : ℝ) = v.imI * w.imI + v.imJ * w.imJ + v.imK * w.imK := by
    have h := pure_product_re v w hv hw
    rw [Quaternion.re_mul, hvre, hwre, zero_mul] at h
    linarith
  -- The imaginary (cross) parts always cancel, so the equation reduces to the
  -- real-part (dot-product) condition.
  rw [hdot, eq_neg_iff_add_eq_zero, Quaternion.ext_iff]
  simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    hvre, hwre]
  constructor
  · rintro ⟨h, -, -, -⟩; linear_combination (-1 / 2 : ℝ) * h
  · intro h; exact ⟨by linear_combination -2 * h, by ring, by ring, by ring⟩

/-- Euclidean structure on the pure quaternions: the coordinate map
`v₁ i + v₂ j + v₃ k ↦ (v₁, v₂, v₃)` is a linear isometric equivalence
`ℍ⁰ ≃ₗᵢ EuclideanSpace ℝ (Fin 3)` (for which `i, j, k` is an orthonormal
basis). -/
noncomputable def pureCoord :
    skewAdjoint.submodule ℝ (Quaternion ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun v := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![v.1.imI, v.1.imJ, v.1.imK]
  map_add' := by sorry
  map_smul' := by sorry
  invFun w :=
    ⟨⟨0, WithLp.equiv 2 (Fin 3 → ℝ) w 0, WithLp.equiv 2 (Fin 3 → ℝ) w 1,
      WithLp.equiv 2 (Fin 3 → ℝ) w 2⟩, by sorry⟩
  left_inv := by sorry
  right_inv := by sorry

/-- The coordinate map `ℍ⁰ → EuclideanSpace ℝ (Fin 3)` is a linear isometry. -/
noncomputable def pureEuclid :
    skewAdjoint.submodule ℝ (Quaternion ℝ) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toLinearEquiv := pureCoord
  norm_map' := by sorry

/-- A norm-preserving `ℝ`-linear map of `ℝ³` with determinant one has its matrix
in `SO(3)`. -/
lemma isometry_to_so (A : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ v : EuclideanSpace ℝ (Fin 3), ‖Matrix.toEuclideanLin A v‖ = ‖v‖)
    (hdet : A.det = 1) : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by sorry

/-- Conjugation as an `ℝ`-linear endomorphism `v ↦ α v α⁻¹` of `ℍ`. -/
noncomputable def conjEndo (α : Quaternion ℝ) : Quaternion ℝ →ₗ[ℝ] Quaternion ℝ :=
  (LinearMap.mulRight ℝ α⁻¹).comp (LinearMap.mulLeft ℝ α)

/-- Conjugation preserves purity: for `α ≠ 0` and pure `v`, `α v α⁻¹` is pure. -/
lemma conj_preserves_pure (α : Quaternion ℝ) (hα : α ≠ 0) (v : Quaternion ℝ)
    (hv : v.IsSkewAdjoint) : (conjEndo α v).re = 0 := by
  rw [isSkewAdjoint_iff_re] at hv
  -- The real part of a quaternion product is symmetric: re (x * y) = re (y * x).
  have hcyc : ∀ x y : Quaternion ℝ, (x * y).re = (y * x).re := by
    intro x y; simp only [Quaternion.re_mul]; ring
  have hgoal : conjEndo α v = α * v * α⁻¹ := by
    simp [conjEndo, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, mul_assoc]
  rw [hgoal]
  -- re (α v α⁻¹) = re (α⁻¹ (α v)) = re ((α⁻¹ α) v) = re v = 0.
  calc (α * v * α⁻¹).re
      = (α⁻¹ * (α * v)).re := hcyc (α * v) α⁻¹
    _ = (α⁻¹ * α * v).re := by rw [mul_assoc]
    _ = v.re := by rw [inv_mul_cancel₀ hα, one_mul]
    _ = 0 := hv

/-- Conjugation preserves the norm: for `α` with `normSq α = 1` and any `v`,
`normSq (α v α⁻¹) = normSq v`. -/
lemma conj_preserves_norm (α : Quaternion ℝ) (hα : Quaternion.normSq α = 1)
    (v : Quaternion ℝ) : Quaternion.normSq (conjEndo α v) = Quaternion.normSq v := by
  have hconj : conjEndo α v = α * v * α⁻¹ := by
    simp [conjEndo, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, mul_assoc]
  rw [hconj]
  calc
    Quaternion.normSq (α * v * α⁻¹) = Quaternion.normSq (α * v) * Quaternion.normSq (α⁻¹) := by
      rw [normSq_mul]
    _ = (Quaternion.normSq α * Quaternion.normSq v) * Quaternion.normSq (α⁻¹) := by
      rw [normSq_mul]
    _ = (Quaternion.normSq α * Quaternion.normSq v) * (Quaternion.normSq α)⁻¹ := by
      rw [Quaternion.normSq_inv]
    _ = (1 * Quaternion.normSq v) * (1 : ℝ)⁻¹ := by rw [hα]
    _ = Quaternion.normSq v := by norm_num

/-- Conjugation is `ℝ`-linear on the pure quaternions: for `α ≠ 0`, the map
`ρ_α : v ↦ α v α⁻¹` restricts to an `ℝ`-linear endomorphism of `ℍ⁰`. -/
noncomputable def rotLin (α : Quaternion ℝ) (hα : α ≠ 0) :
    skewAdjoint.submodule ℝ (Quaternion ℝ) →ₗ[ℝ] skewAdjoint.submodule ℝ (Quaternion ℝ) :=
  (conjEndo α).restrict (fun v hv => by
    rw [mem_skewAdjoint_submodule_iff] at hv ⊢
    exact conj_preserves_pure α hα v ((isSkewAdjoint_iff_re v).mpr hv))

/-- The *adjoint representation* (Voight (2.4.13)): a unit quaternion `α ∈ ℍ¹`
acts on the pure quaternions `ℍ⁰` by conjugation, `v ↦ α v α⁻¹`, yielding the
`ℝ`-linear endomorphism `ρ_α = adjoint α` of `ℍ⁰`.  The assignment
`α ↦ adjoint α` is the representation; that it lands in `SO(3)` and is a group
homomorphism is `rotation_mem_so` and `double_cover`. -/
noncomputable def adjoint (α : Quaternion ℝ) (hα : α ≠ 0) :
    skewAdjoint.submodule ℝ (Quaternion ℝ) →ₗ[ℝ] skewAdjoint.submodule ℝ (Quaternion ℝ) :=
  rotLin α hα

/-- The standard pure-quaternion frame `i, j, k`. -/
def frame : Fin 3 → Quaternion ℝ :=
  ![⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- The `3 × 3` matrix of `ρ_α : v ↦ α v α⁻¹` in the orthonormal basis
`i, j, k` of `ℍ⁰`. -/
noncomputable def rotMatrix (α : Quaternion ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    ![(conjEndo α (frame j)).imI, (conjEndo α (frame j)).imJ,
      (conjEndo α (frame j)).imK] i

/-- `ρ_α` is orthogonal: for `normSq α = 1` it preserves the norm on `ℍ⁰`. -/
lemma rotation_orthogonal (α : Quaternion ℝ) (hα : Quaternion.normSq α = 1)
    (v : Quaternion ℝ) (_hv : v.IsSkewAdjoint) :
    Quaternion.normSq (conjEndo α v) = Quaternion.normSq v :=
  conj_preserves_norm α hα v

/-- The determinant of the matrix of `ρ_α` equals `(normSq α)³`; in particular it
is `1` for `α ∈ ℍ¹`. -/
lemma rotation_det (α : Quaternion ℝ) :
    (rotMatrix α).det = (Quaternion.normSq α) ^ 3 := by sorry

/-- Conjugation acts by rotations: for `α ∈ ℍ¹`, the matrix of `ρ_α` lies in
`SO(3)`. -/
theorem rotation_mem_so (α : Quaternion ℝ) (hα : Quaternion.normSq α = 1) :
    rotMatrix α ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by sorry

/-- Kernel of the rotation map: if `α ∈ ℍ¹` fixes every pure quaternion under
conjugation, then `α = ±1`. -/
lemma rotation_kernel (α : Quaternion ℝ) (hα : Quaternion.normSq α = 1)
    (h : ∀ v : Quaternion ℝ, v.IsSkewAdjoint → conjEndo α v = v) :
    α = 1 ∨ α = -1 := by sorry

/-- Axis and angle of an `SO(3)` element: every `A ∈ SO(3)` has a unit axis `u`
with `A u = u`, and an angle `2θ` recorded by its trace `tr A = 1 + 2 cos 2θ`. -/
lemma so3_axis_angle (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ (u : EuclideanSpace ℝ (Fin 3)) (θ : ℝ),
      ‖u‖ = 1 ∧ Matrix.toEuclideanLin A u = u ∧
        Matrix.trace A = 1 + 2 * Real.cos (2 * θ) := by sorry

/-- Conjugation fixes its axis: for a unit pure quaternion `u` and `θ ∈ ℝ`, with
`α = cos θ + (sin θ) u ∈ ℍ¹`, one has `ρ_α(u) = u`. -/
lemma rotation_fixes_axis (u : Quaternion ℝ)
    (hu : u.IsSkewAdjoint)
    (hu1 : Quaternion.normSq u = 1) (θ : ℝ) :
    conjEndo (((Real.cos θ : ℝ) : Quaternion ℝ) + (Real.sin θ) • u) u = u := by sorry

/-- Conjugation rotates the orthogonal plane by `2θ`: with `u, α` as above and a
unit pure `w` orthogonal to `u`,
`ρ_α(w) = (cos 2θ) w + (sin 2θ) (u × w)` (where `u × w = u w` for orthogonal
pure `u, w`). -/
lemma rotation_on_perp (u w : Quaternion ℝ)
    (hu : u.IsSkewAdjoint)
    (hw : w.IsSkewAdjoint)
    (hu1 : Quaternion.normSq u = 1) (hw1 : Quaternion.normSq w = 1)
    (horth : u.imI * w.imI + u.imJ * w.imJ + u.imK * w.imK = 0) (θ : ℝ) :
    conjEndo (((Real.cos θ : ℝ) : Quaternion ℝ) + (Real.sin θ) • u) w =
      (Real.cos (2 * θ)) • w + (Real.sin (2 * θ)) • (u * w) := by sorry

/-- The rotation map is surjective: every `A ∈ SO(3)` is `ρ_α` for some
`α ∈ ℍ¹`. -/
lemma rotation_surjective (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ α : Quaternion ℝ, Quaternion.normSq α = 1 ∧ rotMatrix α = A := by sorry

/-- The double cover `ℍ¹ → SO(3)`: the map `α ↦ ρ_α` is a surjective group
homomorphism from the unit quaternions to `SO(3)` with kernel `{±1}`. -/
theorem double_cover :
    ∃ f : unitary (Quaternion ℝ) →* Matrix.specialOrthogonalGroup (Fin 3) ℝ,
      (∀ x, (f x : Matrix (Fin 3) (Fin 3) ℝ) = rotMatrix x) ∧
        Function.Surjective f ∧
        (∀ x, f x = 1 ↔ (x : Quaternion ℝ) = 1 ∨ (x : Quaternion ℝ) = -1) := by
  sorry

end QuaternionAlgebras
