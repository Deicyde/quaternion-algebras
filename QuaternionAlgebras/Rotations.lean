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
  unfold conjEndo
  simp [LinearMap.mulRight_apply, LinearMap.mulLeft_apply, mul_assoc]
  -- goal: (α * v * α⁻¹).re = 0
  -- use star_eq_neg: star a = -a ↔ a.re = 0
  have hstar : star (α * v * α⁻¹) = -(α * v * α⁻¹) := by
    calc
      star (α * v * α⁻¹) = star (α⁻¹) * star v * star α := by
        simp [star_mul, mul_assoc]
      _ = star (α⁻¹) * (-v) * star α := by
        -- from v.re = 0, we have star v = -v:
        -- prove directly using componentwise calculation
        have hv_star : star v = -v := by
          ext <;> simp [hv, star, add_comm, add_left_neg, mul_comm, add_assoc]
        rw [hv_star]
      _ = -(star (α⁻¹) * v * star α) := by ring
      _ = -(α * v * α⁻¹) := by
        -- key identity: star (α⁻¹) * v * star α = α * v * α⁻¹
        have hstar_α_eq : star α = (Quaternion.normSq α : Quaternion ℝ) * α⁻¹ := by
          calc
            star α = ((α⁻¹ * α : Quaternion ℝ) : Quaternion ℝ) * star α := by field_simp [hα]
            _ = α⁻¹ * (α * star α) := by ring
            _ = α⁻¹ * (Quaternion.normSq α : Quaternion ℝ) := by rw [Quaternion.self_mul_star]
            _ = (Quaternion.normSq α : Quaternion ℝ) * α⁻¹ := by ring
        have hstar_α_inv_eq : star (α⁻¹) = (α : Quaternion ℝ) * ((Quaternion.normSq α)⁻¹ : ℝ) := by
          calc
            star (α⁻¹) = ((α * α⁻¹ : Quaternion ℝ) : Quaternion ℝ) * star (α⁻¹) := by field_simp [hα]
            _ = α * (α⁻¹ * star (α⁻¹)) := by ring
            _ = α * (Quaternion.normSq (α⁻¹) : Quaternion ℝ) := by rw [Quaternion.self_mul_star]
            _ = α * (((Quaternion.normSq α)⁻¹ : ℝ) : Quaternion ℝ) := by
              simp [Quaternion.normSq_inv]
            _ = (α : Quaternion ℝ) * ((Quaternion.normSq α)⁻¹ : ℝ) := rfl
        calc
          star (α⁻¹) * v * star α
              = ((α : Quaternion ℝ) * ((Quaternion.normSq α)⁻¹ : ℝ)) * v *
                  ((Quaternion.normSq α : Quaternion ℝ) * α⁻¹) := by
                rw [hstar_α_inv_eq, hstar_α_eq]
          _ = (α : Quaternion ℝ) * (((Quaternion.normSq α)⁻¹ : ℝ) : Quaternion ℝ) * v *
                ((Quaternion.normSq α : Quaternion ℝ) * α⁻¹) := rfl
          _ = α * (((Quaternion.normSq α)⁻¹ : ℝ) : Quaternion ℝ) * v *
                (Quaternion.normSq α : Quaternion ℝ) * α⁻¹ := by ring
          _ = α * v * (((Quaternion.normSq α)⁻¹ : ℝ) : Quaternion ℝ) *
                (Quaternion.normSq α : Quaternion ℝ) * α⁻¹ := by
            -- scalars commute: ((normSq α)⁻¹ : ℝ) * v = v * ((normSq α)⁻¹ : ℝ)
            simp [Algebra.commutes]
          _ = α * v * ((((Quaternion.normSq α)⁻¹ : ℝ) : Quaternion ℝ) *
                (Quaternion.normSq α : Quaternion ℝ)) * α⁻¹ := by ring
          _ = α * v * (1 : Quaternion ℝ) * α⁻¹ := by
            have hnorm : (Quaternion.normSq α : Quaternion ℝ) ≠ 0 := by
              simpa using (Quaternion.normSq_ne_zero.mpr hα)
            simp [hnorm]
          _ = α * v * α⁻¹ := by simp
  -- now from star (α * v * α⁻¹) = -(α * v * α⁻¹), deduce (α * v * α⁻¹).re = 0
  have h_re : (α * v * α⁻¹).re = 0 := by
    have helper : ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)] := α * v * α⁻¹
    sorry
  exact h_re

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
