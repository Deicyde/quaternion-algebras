import QuaternionAlgebras.Conjugation

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

open scoped Quaternion

/-- Euclidean structure on the pure quaternions: the coordinate map
`v₁ i + v₂ j + v₃ k ↦ (v₁, v₂, v₃)` is a linear isometric equivalence
`ℍ⁰ ≃ₗᵢ EuclideanSpace ℝ (Fin 3)` (for which `i, j, k` is an orthonormal
basis). -/
noncomputable def pureCoord : Hpure ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3) where
  toFun v := (WithLp.equiv 2 (Fin 3 → ℝ)).symm ![v.1.imI, v.1.imJ, v.1.imK]
  map_add' := by sorry
  map_smul' := by sorry
  invFun w :=
    ⟨⟨0, WithLp.equiv 2 (Fin 3 → ℝ) w 0, WithLp.equiv 2 (Fin 3 → ℝ) w 1,
      WithLp.equiv 2 (Fin 3 → ℝ) w 2⟩, by sorry⟩
  left_inv := by sorry
  right_inv := by sorry

/-- The coordinate map `ℍ⁰ → EuclideanSpace ℝ (Fin 3)` is a linear isometry. -/
noncomputable def pureEuclid : Hpure ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) where
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
    (hv : v.re = 0) : (conjEndo α v).re = 0 := by
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
  sorry

/-- Conjugation is `ℝ`-linear on the pure quaternions: for `α ≠ 0`, the map
`ρ_α : v ↦ α v α⁻¹` restricts to an `ℝ`-linear endomorphism of `ℍ⁰`. -/
noncomputable def rotLin (α : Quaternion ℝ) (hα : α ≠ 0) : Hpure →ₗ[ℝ] Hpure :=
  (conjEndo α).restrict (fun v hv => conj_preserves_pure α hα v hv)

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
    (v : Quaternion ℝ) (hv : v.re = 0) :
    Quaternion.normSq (conjEndo α v) = Quaternion.normSq v := by sorry

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
    (h : ∀ v : Quaternion ℝ, v.re = 0 → conjEndo α v = v) :
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
lemma rotation_fixes_axis (u : Quaternion ℝ) (hu : u.re = 0)
    (hu1 : Quaternion.normSq u = 1) (θ : ℝ) :
    conjEndo (((Real.cos θ : ℝ) : Quaternion ℝ) + (Real.sin θ) • u) u = u := by sorry

/-- Conjugation rotates the orthogonal plane by `2θ`: with `u, α` as above and a
unit pure `w` orthogonal to `u`,
`ρ_α(w) = (cos 2θ) w + (sin 2θ) (u × w)` (where `u × w = u w` for orthogonal
pure `u, w`). -/
lemma rotation_on_perp (u w : Quaternion ℝ) (hu : u.re = 0) (hw : w.re = 0)
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
