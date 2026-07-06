import Mathlib

/-!
# Rotations: the double cover `ℍ¹ → SO(3)`

For `α` in the unit Hamiltonians `ℍ¹ = {α : normSq α = 1}`, conjugation
`v ↦ α v α⁻¹` is an `ℝ`-linear isometry of the pure quaternions `ℍ⁰ ≅ ℝ³` of
determinant one, hence an element of `SO(3) = Matrix.specialOrthogonalGroup
(Fin 3) ℝ`.  The resulting map `rotationHom : ℍ¹ →* SO(3)` is a surjective group
homomorphism with kernel `{±1}` — the double cover (Voight, Corollary 2.4.21).

Surjectivity follows Voight's Exercise 2.15: every `A ∈ SO(3)` fixes a unit
axis `u` (eigenvalue 1); reading the rotation angle `θ` off the image of a unit
vector `w ⟂ u` fixes the orientation, and `α = cos(θ/2) + sin(θ/2)·u` realizes
`A` by conjugation.
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
  rw [Quaternion.inner_def, Quaternion.star_eq_neg.mpr ((isSkewAdjoint_iff_re w).mp hw), mul_neg]
  simp

/-- The imaginary part of a quaternion as a vector in `ℝ³`. -/
def imVec (v : Quaternion ℝ) : Fin 3 → ℝ := ![v.imI, v.imJ, v.imK]

/-- The pure quaternion whose imaginary part is a given vector of `ℝ³`. -/
def ofImVec (u : Fin 3 → ℝ) : Quaternion ℝ := ⟨0, u 0, u 1, u 2⟩

/-- The *pure part* `xi + yj + zk` of a quaternion `α = t + xi + yj + zk`, i.e. the
projection onto `ℍ⁰` obtained by discarding the real part. -/
def purePart (α : Quaternion ℝ) : Quaternion ℝ := ofImVec (imVec α)

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
  ext <;> simp [crossQuat, ofImVec, imVec, hre, h0, h1, h2]

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
    have h := pure_product_re v w hv hw; rw [Quaternion.re_mul, hvre, hwre, zero_mul] at h; linarith
  -- The imaginary (cross) parts cancel, reducing to the real-part (dot) condition.
  rw [hdot, eq_neg_iff_add_eq_zero, Quaternion.ext_iff]
  simp [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    hvre, hwre]
  constructor
  · rintro ⟨h, -, -, -⟩; linear_combination (-1 / 2 : ℝ) * h
  · intro h; exact ⟨by linear_combination -2 * h, by ring, by ring, by ring⟩

/-- The *axis* `I(α)` (Voight (2.4.16)): the normalized pure part `(xi+yj+zk)/‖xi+yj+zk‖`. -/
noncomputable def axis (α : Quaternion ℝ) : Quaternion ℝ :=
  ‖purePart α‖⁻¹ • purePart α

/-- Conjugation as an `ℝ`-linear endomorphism `v ↦ α v α⁻¹` of `ℍ`. -/
noncomputable def conjEndo (α : Quaternion ℝ) : Quaternion ℝ →ₗ[ℝ] Quaternion ℝ :=
  (LinearMap.mulRight ℝ α⁻¹).comp (LinearMap.mulLeft ℝ α)

/-- Conjugation preserves purity: for `α ≠ 0` and pure `v`, `α v α⁻¹` is pure. -/
lemma conj_preserves_pure (α : Quaternion ℝ) (hα : α ≠ 0) (v : Quaternion ℝ)
    (hv : v.IsSkewAdjoint) : (conjEndo α v).re = 0 := by
  rw [isSkewAdjoint_iff_re] at hv
  have hgoal : conjEndo α v = α * v * α⁻¹ := by
    simp [conjEndo, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, mul_assoc]
  -- re (α v α⁻¹) = re (α⁻¹ α v) = re v = 0.
  rw [hgoal, show (α * v * α⁻¹).re = (α⁻¹ * (α * v)).re by simp only [Quaternion.re_mul]; ring,
    ← mul_assoc, inv_mul_cancel₀ hα, one_mul, hv]

/-- Conjugation is `ℝ`-linear on the pure quaternions: for `α ≠ 0`, the map
`ρ_α : v ↦ α v α⁻¹` restricts to an `ℝ`-linear endomorphism of `ℍ⁰`. -/
noncomputable def rotLin (α : Quaternion ℝ) (hα : α ≠ 0) :
    skewAdjoint.submodule ℝ (Quaternion ℝ) →ₗ[ℝ] skewAdjoint.submodule ℝ (Quaternion ℝ) :=
  (conjEndo α).restrict (fun v hv => by
    rw [mem_skewAdjoint_submodule_iff] at hv ⊢
    exact conj_preserves_pure α hα v ((isSkewAdjoint_iff_re v).mpr hv))

/-- `ℍ¹` membership is exactly the norm-one condition `normSq α = 1`. -/
lemma mem_unitary_iff_normSq (α : Quaternion ℝ) :
    α ∈ unitary (Quaternion ℝ) ↔ Quaternion.normSq α = 1 := by
  rw [Unitary.mem_iff]
  constructor
  · rintro ⟨h, -⟩
    rw [Quaternion.star_mul_self] at h
    simpa using congrArg (·.re) h
  · intro h
    exact ⟨by simp [Quaternion.star_mul_self, h], by simp [Quaternion.self_mul_star, h]⟩

/-- A unit quaternion is nonzero. -/
lemma coe_unitary_ne_zero (u : unitary (Quaternion ℝ)) : (u : Quaternion ℝ) ≠ 0 := by
  intro h
  have h1 : Quaternion.normSq (u : Quaternion ℝ) = 1 := (mem_unitary_iff_normSq _).mp u.2
  rw [h, map_zero] at h1; exact zero_ne_one h1

/-- Explicit form of conjugation: `conjEndo α v = α v α⁻¹`. -/
lemma conjEndo_apply (α v : Quaternion ℝ) : conjEndo α v = α * v * α⁻¹ := by
  simp [conjEndo, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, mul_assoc]

/-- Conjugation by `1` is the identity. -/
lemma conjEndo_one (v : Quaternion ℝ) : conjEndo 1 v = v := by
  simp [conjEndo_apply]

/-- Conjugation is multiplicative: `ρ_{αβ} = ρ_α ∘ ρ_β`. -/
lemma conjEndo_mul (α β v : Quaternion ℝ) :
    conjEndo (α * β) v = conjEndo α (conjEndo β v) := by
  simp only [conjEndo_apply, mul_inv_rev]
  noncomm_ring

/-- For a unit quaternion `α⁻¹ = star α`, so conjugation is `v ↦ α v \barα`. -/
lemma conjEndo_star (α v : Quaternion ℝ) (hα : Quaternion.normSq α = 1) :
    conjEndo α v = α * v * star α := by
  rw [conjEndo_apply, inv_eq_of_mul_eq_one_right
    (by rw [Quaternion.self_mul_star, hα, Quaternion.coe_one])]

/-- The underlying quaternion of `rotLin α hα x` is `conjEndo α x`. -/
lemma rotLin_coe (α : Quaternion ℝ) (hα : α ≠ 0)
    (x : skewAdjoint.submodule ℝ (Quaternion ℝ)) :
    (↑(rotLin α hα x) : Quaternion ℝ) = conjEndo α ↑x := by
  simp only [rotLin, LinearMap.coe_restrict_apply]

/-- Conjugation by a unit quaternion `α`, packaged as an `ℝ`-linear *automorphism*
of `ℍ⁰` (its inverse is conjugation by `α⁻¹`). -/
noncomputable def rotEquiv (u : unitary (Quaternion ℝ)) :
    skewAdjoint.submodule ℝ (Quaternion ℝ) ≃ₗ[ℝ] skewAdjoint.submodule ℝ (Quaternion ℝ) :=
  LinearEquiv.ofLinear
    (rotLin ↑u (coe_unitary_ne_zero u))
    (rotLin (↑u)⁻¹ (inv_ne_zero (coe_unitary_ne_zero u)))
    (by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [LinearMap.id_apply, LinearMap.comp_apply, rotLin_coe, rotLin_coe, ← conjEndo_mul,
        mul_inv_cancel₀ (coe_unitary_ne_zero u), conjEndo_one])
    (by
      refine LinearMap.ext fun v => Subtype.ext ?_
      rw [LinearMap.id_apply, LinearMap.comp_apply, rotLin_coe, rotLin_coe, ← conjEndo_mul,
        inv_mul_cancel₀ (coe_unitary_ne_zero u), conjEndo_one])

/-- The underlying quaternion of `rotEquiv u v` is `α v α⁻¹` with `α = ↑u`. -/
lemma rotEquiv_coe_apply (u : unitary (Quaternion ℝ))
    (v : skewAdjoint.submodule ℝ (Quaternion ℝ)) :
    (↑(rotEquiv u v) : Quaternion ℝ) = (↑u : Quaternion ℝ) * ↑v * (↑u)⁻¹ := by
  simp only [rotEquiv, LinearEquiv.ofLinear_apply, rotLin_coe, conjEndo_apply]

/-- The *adjoint representation* (Voight (2.4.13)): the group homomorphism
`ℍ¹ → Aut(ℍ⁰)` sending a unit quaternion `α` to conjugation
`ρ_α : v ↦ α v α⁻¹`, an `ℝ`-linear automorphism of the pure quaternions `ℍ⁰`. -/
noncomputable def adjoint :
    unitary (Quaternion ℝ) →*
      (skewAdjoint.submodule ℝ (Quaternion ℝ) ≃ₗ[ℝ] skewAdjoint.submodule ℝ (Quaternion ℝ)) where
  toFun := rotEquiv
  map_one' := by
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    show (↑(rotEquiv 1 v) : Quaternion ℝ) = ↑v
    rw [rotEquiv_coe_apply, OneMemClass.coe_one, inv_one, mul_one, one_mul]
  map_mul' u w := by
    refine LinearEquiv.ext fun v => Subtype.ext ?_
    show (↑(rotEquiv (u * w) v) : Quaternion ℝ) = ↑(rotEquiv u (rotEquiv w v))
    simp only [rotEquiv_coe_apply, Submonoid.coe_mul, mul_inv_rev]
    noncomm_ring

/-- Coordinate isomorphism `ℍ⁰ ≃ₗ ℝ³` sending a pure quaternion to its imaginary
part `(v₁, v₂, v₃)`. -/
def pureFin : skewAdjoint.submodule ℝ (Quaternion ℝ) ≃ₗ[ℝ] (Fin 3 → ℝ) where
  toFun v := imVec ↑v
  map_add' v w := by funext i; fin_cases i <;> simp [imVec]
  map_smul' r v := by funext i; fin_cases i <;> simp [imVec]
  invFun u := ⟨ofImVec u, by rw [mem_skewAdjoint_submodule_iff]; simp [ofImVec]⟩
  left_inv v := by
    apply Subtype.ext
    have hv : (v : Quaternion ℝ).re = 0 := (mem_skewAdjoint_submodule_iff _).mp v.2
    ext <;> simp [imVec, ofImVec, hv]
  right_inv u := by funext i; fin_cases i <;> simp [imVec, ofImVec]

/-- The coordinate basis `i, j, k` of `ℍ⁰`, as `Basis.ofEquivFun pureFin`. -/
noncomputable def pureBasis : Module.Basis (Fin 3) ℝ (skewAdjoint.submodule ℝ (Quaternion ℝ)) :=
  Module.Basis.ofEquivFun pureFin

/-- The standard pure-quaternion frame `i, j, k`. -/
def frame : Fin 3 → Quaternion ℝ :=
  ![⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]

/-- The `j`-th coordinate basis vector of `ℍ⁰` is the `j`-th frame quaternion. -/
lemma pureBasis_coe (j : Fin 3) : (pureBasis j : Quaternion ℝ) = frame j := by
  have key : pureFin (pureBasis j) = imVec (frame j) := by
    funext i
    simp only [pureBasis]
    rw [← Module.Basis.ofEquivFun_repr_apply, Module.Basis.repr_self]
    fin_cases j <;> fin_cases i <;> simp [imVec, frame]
  have h2 : pureBasis j = pureFin.symm (imVec (frame j)) := by
    rw [← key, LinearEquiv.symm_apply_apply]
  rw [h2]
  show ofImVec (imVec (frame j)) = frame j
  fin_cases j <;> simp [ofImVec, imVec, frame]

/-- The `3 × 3` matrix of `ρ_α : v ↦ α v α⁻¹` in the orthonormal basis
`i, j, k` of `ℍ⁰`. -/
noncomputable def rotMatrix (α : Quaternion ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j =>
    ![(conjEndo α (frame j)).imI, (conjEndo α (frame j)).imJ,
      (conjEndo α (frame j)).imK] i

/-- Explicit matrix of `ρ_α` for a unit quaternion `α = t + xi + yj + zk`
(Voight (2.4.20), general form): the standard quaternion rotation matrix. -/
lemma rotMatrix_eq (α : Quaternion ℝ) (hα : Quaternion.normSq α = 1) :
    rotMatrix α = !![
      α.re ^ 2 + α.imI ^ 2 - α.imJ ^ 2 - α.imK ^ 2,
        2 * (α.imI * α.imJ - α.re * α.imK), 2 * (α.imI * α.imK + α.re * α.imJ);
      2 * (α.imI * α.imJ + α.re * α.imK),
        α.re ^ 2 - α.imI ^ 2 + α.imJ ^ 2 - α.imK ^ 2, 2 * (α.imJ * α.imK - α.re * α.imI);
      2 * (α.imI * α.imK - α.re * α.imJ),
        2 * (α.imJ * α.imK + α.re * α.imI), α.re ^ 2 - α.imI ^ 2 - α.imJ ^ 2 + α.imK ^ 2] := by
  have hc : ∀ v, conjEndo α v = α * v * star α := fun v => conjEndo_star α v hα
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotMatrix, frame, hc, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star,
      Quaternion.imK_star] <;>
    ring

/-- Computational core of Voight 2.4.18: the explicit rotation matrix of a unit
quaternion lies in `SO(3)`. -/
lemma rotMatrix_mem_so (α : Quaternion ℝ) (hα : Quaternion.normSq α = 1) :
    rotMatrix α ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  have hn : α.re ^ 2 + α.imI ^ 2 + α.imJ ^ 2 + α.imK ^ 2 = 1 := by
    rw [← Quaternion.normSq_def']; exact hα
  rw [Matrix.mem_specialOrthogonalGroup_iff, rotMatrix_eq α hα]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_three] <;>
      (first
        | linear_combination (α.re ^ 2 + α.imI ^ 2 + α.imJ ^ 2 + α.imK ^ 2 + 1) * hn
        | ring)
  · rw [Matrix.det_fin_three]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val',
      Matrix.cons_val_fin_one, Matrix.head_fin_const]
    linear_combination ((α.re ^ 2 + α.imI ^ 2 + α.imJ ^ 2 + α.imK ^ 2) ^ 2 +
      (α.re ^ 2 + α.imI ^ 2 + α.imJ ^ 2 + α.imK ^ 2) + 1) * hn

/-- The natural isomorphism `(ℍ⁰ →ₗ ℍ⁰) ≃ M₃(ℝ)` (the matrix in the `i, j, k`
basis) carries the adjoint action `adjoint u` of a unit `u` to the rotation matrix
of `↑u`. -/
lemma adjoint_toMatrix (u : unitary (Quaternion ℝ)) :
    LinearMap.toMatrix pureBasis pureBasis (adjoint u).toLinearMap = rotMatrix ↑u := by
  have hrepr : ∀ (x : skewAdjoint.submodule ℝ (Quaternion ℝ)) (i : Fin 3),
      (pureBasis.repr x) i = imVec (↑x) i := by
    intro x i; simp only [pureBasis, Module.Basis.ofEquivFun_repr_apply]; rfl
  ext i j
  rw [LinearMap.toMatrix_apply, hrepr]
  have hx : (↑((adjoint u).toLinearMap (pureBasis j)) : Quaternion ℝ)
      = conjEndo ↑u (frame j) := by
    show (↑(rotEquiv u (pureBasis j)) : Quaternion ℝ) = conjEndo ↑u (frame j)
    rw [rotEquiv_coe_apply, pureBasis_coe, conjEndo_apply]
  rw [hx]
  simp [rotMatrix, imVec]

/-- Conjugation acts by rotations (Voight 2.4.18): for a unit quaternion
`u ∈ ℍ¹ = unitary ℍ`, the matrix of the adjoint action `adjoint u` in the
orthonormal frame `i, j, k` lies in `SO(3)`. -/
theorem rotation_mem_so (u : unitary (Quaternion ℝ)) :
    LinearMap.toMatrix pureBasis pureBasis (adjoint u).toLinearMap ∈
      Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [adjoint_toMatrix]
  exact rotMatrix_mem_so ↑u ((mem_unitary_iff_normSq _).mp u.2)

/-- The rotation angle of a unit quaternion: `θ = arccos(Re α)` (Voight (2.4.16)). -/
noncomputable def rotAngle (α : Quaternion ℝ) : ℝ := Real.arccos α.re

/-- The adjoint action of `u ∈ ℍ¹` rotates `ℍ⁰ ≅ ℝ³` by `2θ` (Voight 2.4.18): its
`SO(3)` matrix has trace `1 + 2 cos 2θ`. -/
theorem rotation_trace (u : unitary (Quaternion ℝ)) :
    LinearMap.trace ℝ _ (adjoint u).toLinearMap =
      1 + 2 * Real.cos (2 * rotAngle ↑u) := by
  rw [LinearMap.trace_eq_matrix_trace ℝ pureBasis]
  have hα : Quaternion.normSq (↑u : Quaternion ℝ) = 1 := (mem_unitary_iff_normSq _).mp u.2
  have hn : (↑u : Quaternion ℝ).re ^ 2 + (↑u : Quaternion ℝ).imI ^ 2
      + (↑u : Quaternion ℝ).imJ ^ 2 + (↑u : Quaternion ℝ).imK ^ 2 = 1 := by
    rw [← Quaternion.normSq_def']; exact hα
  have hle1 : -1 ≤ (↑u : Quaternion ℝ).re := by
    nlinarith [sq_nonneg (↑u : Quaternion ℝ).imI, sq_nonneg (↑u : Quaternion ℝ).imJ,
      sq_nonneg (↑u : Quaternion ℝ).imK, sq_nonneg ((↑u : Quaternion ℝ).re + 1)]
  have hle2 : (↑u : Quaternion ℝ).re ≤ 1 := by
    nlinarith [sq_nonneg (↑u : Quaternion ℝ).imI, sq_nonneg (↑u : Quaternion ℝ).imJ,
      sq_nonneg (↑u : Quaternion ℝ).imK, sq_nonneg ((↑u : Quaternion ℝ).re - 1)]
  rw [adjoint_toMatrix, rotMatrix_eq ↑u hα, Matrix.trace_fin_three, rotAngle,
    Real.cos_two_mul, Real.cos_arccos hle1 hle2]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const]
  linear_combination -hn

/-- Kernel of the rotation map: if `α ∈ ℍ¹` fixes every pure quaternion under
conjugation, then `α = ±1`. -/
lemma rotation_kernel (α : Quaternion ℝ) (hα : Quaternion.normSq α = 1)
    (h : ∀ v : Quaternion ℝ, v.IsSkewAdjoint → conjEndo α v = v) :
    α = 1 ∨ α = -1 := by
  have hα0 : α ≠ 0 := by
    intro h0; rw [h0, map_zero] at hα; exact zero_ne_one hα
  -- Turn each fixed-point equation `α v α⁻¹ = v` into a commutation `α v = v α`.
  have hcomm : ∀ v : Quaternion ℝ, v.IsSkewAdjoint → α * v = v * α := by
    intro v hv
    have := congrArg (· * α) (show α * v * α⁻¹ = v by rw [← conjEndo_apply]; exact h v hv)
    simpa only [mul_assoc, inv_mul_cancel₀ hα0, mul_one] using this
  have ci := hcomm _ ((isSkewAdjoint_iff_re (⟨0, 1, 0, 0⟩ : Quaternion ℝ)).mpr rfl)
  have cj := hcomm _ ((isSkewAdjoint_iff_re (⟨0, 0, 1, 0⟩ : Quaternion ℝ)).mpr rfl)
  have ck := hcomm _ ((isSkewAdjoint_iff_re (⟨0, 0, 0, 1⟩ : Quaternion ℝ)).mpr rfl)
  -- Extract coordinate identities from the commutations.
  rw [Quaternion.ext_iff] at ci cj ck
  simp only [Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul,
    mul_zero, mul_one, zero_mul, add_zero, zero_add, sub_zero, zero_sub] at ci cj ck
  obtain ⟨-, ci2, ci3, ci4⟩ := ci
  obtain ⟨-, cj2, cj3, cj4⟩ := cj
  obtain ⟨-, ck2, ck3, ck4⟩ := ck
  -- These force all imaginary parts of α to vanish.
  have hI : α.imI = 0 := by linarith
  have hJ : α.imJ = 0 := by linarith
  have hK : α.imK = 0 := by linarith
  -- With imaginary parts zero, normSq α = α.re² = 1, so α.re = ±1.
  have hfac : (α.re - 1) * (α.re + 1) = 0 := by
    rw [Quaternion.normSq_def'] at hα; nlinarith [hα, hI, hJ, hK]
  rcases mul_eq_zero.mp hfac with h1 | h1
  · refine Or.inl ?_
    have hr : α.re = 1 := by linarith
    ext <;> simp [hr, hI, hJ, hK]
  · refine Or.inr ?_
    have hr : α.re = -1 := by linarith
    ext <;> simp [hr, hI, hJ, hK]

/-- Every `A ∈ SO(3)` fixes a unit axis: there is a unit vector `u` with `A u = u`
(eigenvalue `1`). Proof: `det(A - 1) = 0` since `n = 3` is odd, giving a nonzero
kernel vector, which we normalize. -/
lemma so3_has_fixed_unit_axis (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ u : EuclideanSpace ℝ (Fin 3), ‖u‖ = 1 ∧ Matrix.toEuclideanLin A u = u := by
  -- Unpack membership: orthogonality and det = 1.
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hA
  obtain ⟨hOmem, hdet⟩ := hA
  rw [Matrix.mem_orthogonalGroup_iff] at hOmem
  -- DET-PARITY: (A - 1).det = 0, since d = (1-A).det = -d in odd dimension.
  have hdz : (A - 1).det = 0 := by
    have hd1 : (A - 1).det = (1 - A).det := by
      rw [show A - 1 = A * (1 - Aᵀ) by rw [Matrix.mul_sub, Matrix.mul_one, hOmem],
        Matrix.det_mul, hdet, one_mul, ← Matrix.det_transpose (1 - A),
        Matrix.transpose_sub, Matrix.transpose_one]
    have hd3 : (1 - A).det = -(A - 1).det := by
      rw [(neg_sub A 1).symm, Matrix.det_neg, Fintype.card_fin]; norm_num
    linarith [hd1.trans hd3]
  -- Eigenvector for eigenvalue 1.
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdz
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMv
  set v₂ : EuclideanSpace ℝ (Fin 3) := (WithLp.equiv 2 (Fin 3 → ℝ)).symm v with hv2def
  have hfixed : Matrix.toEuclideanLin A v₂ = v₂ :=
    show WithLp.toLp 2 (A *ᵥ v) = WithLp.toLp 2 v by rw [hMv]
  have hnorm_ne : ‖v₂‖ ≠ 0 := norm_ne_zero_iff.mpr (by rw [hv2def, WithLp.equiv_symm_apply]; simpa using hv)
  refine ⟨(‖v₂‖⁻¹ : ℝ) • v₂, ?_, by rw [map_smul, hfixed]⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖v₂‖⁻¹)]; field_simp

/-- For a unit pure quaternion `u`, the quaternion `cos φ + sin φ • u` has norm one. -/
lemma normSq_cos_add_sin_smul (u : Quaternion ℝ) (hu : u.IsSkewAdjoint)
    (hu1 : Quaternion.normSq u = 1) (φ : ℝ) :
    Quaternion.normSq (((Real.cos φ : ℝ) : Quaternion ℝ) + Real.sin φ • u) = 1 := by
  have hure : u.re = 0 := (isSkewAdjoint_iff_re u).mp hu
  have hunorm' : u.re ^ 2 + u.imI ^ 2 + u.imJ ^ 2 + u.imK ^ 2 = 1 := by
    rw [← Quaternion.normSq_def']; exact hu1
  have hpyth : Real.cos φ ^ 2 + Real.sin φ ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq _
  rw [Quaternion.normSq_def']
  simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add, Quaternion.imK_add,
    Quaternion.re_coe, Quaternion.imI_coe, Quaternion.imJ_coe, Quaternion.imK_coe,
    Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul, Quaternion.imK_smul,
    smul_eq_mul, hure]
  nlinarith [hunorm', hpyth, hure]

/-- Conjugation fixes its axis: for a unit pure quaternion `u` and `θ ∈ ℝ`, with
`α = cos θ + (sin θ) u ∈ ℍ¹`, one has `ρ_α(u) = u`. -/
lemma rotation_fixes_axis (u : Quaternion ℝ)
    (hu : u.IsSkewAdjoint)
    (hu1 : Quaternion.normSq u = 1) (θ : ℝ) :
    conjEndo (((Real.cos θ : ℝ) : Quaternion ℝ) + (Real.sin θ) • u) u = u := by
  set α : Quaternion ℝ := ((Real.cos θ : ℝ) : Quaternion ℝ) + (Real.sin θ) • u with hαdef
  -- α has norm one, hence is nonzero.
  have hαnorm : Quaternion.normSq α = 1 := normSq_cos_add_sin_smul u hu hu1 θ
  have hα0 : α ≠ 0 := by intro h0; rw [h0, map_zero] at hαnorm; exact zero_ne_one hαnorm
  have hcomm : α * u = u * α := by
    rw [hαdef, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, Quaternion.coe_commutes]
  rw [conjEndo_apply, hcomm, mul_assoc, mul_inv_cancel₀ hα0, mul_one]

/-- Conjugation rotates the orthogonal plane by `2θ`: with `u, α` as above and a
unit pure `w` orthogonal to `u`,
`ρ_α(w) = (cos 2θ) w + (sin 2θ) (u × w)` (where `u × w = u w` for orthogonal
pure `u, w`). -/
lemma rotation_on_perp (u w : Quaternion ℝ)
    (hu : u.IsSkewAdjoint)
    (hw : w.IsSkewAdjoint)
    (hu1 : Quaternion.normSq u = 1) (_hw1 : Quaternion.normSq w = 1)
    (horth : u.imI * w.imI + u.imJ * w.imJ + u.imK * w.imK = 0) (θ : ℝ) :
    conjEndo (((Real.cos θ : ℝ) : Quaternion ℝ) + (Real.sin θ) • u) w =
      (Real.cos (2 * θ)) • w + (Real.sin (2 * θ)) • (u * w) := by
  set c : ℝ := Real.cos θ with hc
  set s : ℝ := Real.sin θ with hs
  set α : Quaternion ℝ := ((c : ℝ) : Quaternion ℝ) + s • u with hαdef
  have hure : u.re = 0 := (isSkewAdjoint_iff_re u).mp hu
  have hαnorm : Quaternion.normSq α = 1 := by
    rw [hαdef, hc, hs]; exact normSq_cos_add_sin_smul u hu hu1 θ
  have hstar : star α = ((c : ℝ) : Quaternion ℝ) - s • u := by
    rw [hαdef, star_add, star_smul, Quaternion.star_eq_neg.mpr hure, Quaternion.star_coe,
      star_trivial, smul_neg, sub_eq_add_neg]
  -- u * u = -1.
  have husq : u * u = -1 := by
    have := (pure_square u).mp hu; rw [pow_two] at this; rw [this, hu1, Quaternion.coe_one]
  -- w * u = -(u * w) from orthogonality, and u * w * u = w.
  have hwu : w * u = -(u * w) := (pure_anticomm_iff u w hu hw).mpr (by
    rw [Quaternion.inner_def, Quaternion.star_eq_neg.mpr ((isSkewAdjoint_iff_re w).mp hw), mul_neg]
    simp only [Quaternion.re_neg, Quaternion.re_mul, hure, (isSkewAdjoint_iff_re w).mp hw]
    linarith [horth])
  have huwu : u * w * u = w := by
    rw [mul_assoc, hwu, mul_neg, ← mul_assoc, husq, neg_one_mul, neg_neg]
  -- Rewrite scalar smuls as coercions with central scalars C, S.
  set C : Quaternion ℝ := ((c : ℝ) : Quaternion ℝ) with hCdef
  set S : Quaternion ℝ := ((s : ℝ) : Quaternion ℝ) with hSdef
  have hCcomm : ∀ x : Quaternion ℝ, C * x = x * C := fun x => Quaternion.coe_commutes c x
  have hScomm : ∀ x : Quaternion ℝ, S * x = x * S := fun x => Quaternion.coe_commutes s x
  have hsu : s • u = S * u := by rw [hSdef, Quaternion.coe_mul_eq_smul]
  -- Expand the conjugation: conjEndo α w = α * w * star α.
  rw [conjEndo_star α w hαnorm, hstar, hαdef, hsu]
  -- RHS: rewrite cos(2θ), sin(2θ) and the smuls.
  rw [Real.cos_two_mul' θ, Real.sin_two_mul θ, ← hc, ← hs]
  have hrw_w : ((c ^ 2 - s ^ 2 : ℝ)) • w = (C * C - S * S) * w := by
    rw [hCdef, hSdef, ← Quaternion.coe_mul, ← Quaternion.coe_mul, ← Quaternion.coe_sub,
      Quaternion.coe_mul_eq_smul]
    congr 1; ring
  have hrw_uw : ((2 * s * c : ℝ)) • (u * w) = (C * S + S * C) * (u * w) := by
    rw [hCdef, hSdef, ← Quaternion.coe_mul, ← Quaternion.coe_mul, ← Quaternion.coe_add,
      Quaternion.coe_mul_eq_smul]
    congr 2; ring
  rw [hrw_w, hrw_uw]
  -- Now purely: (C + S*u) * w * (C - S*u) = (C*C - S*S)*w + (C*S + S*C)*(u*w).
  have hdistrib : (C + S * u) * w * (C - S * u)
      = C*w*C - C*w*(S*u) + S*u*w*C - S*u*w*(S*u) := by noncomm_ring
  rw [hdistrib]
  -- Reduce each monomial using centrality of C, S and the relations husq, hwu, huwu.
  rw [show C*w*C = C*C*w by rw [show C*w*C = C*(w*C) by noncomm_ring, ← hCcomm w]; noncomm_ring]
  rw [show C*w*(S*u) = C*S*(w*u) by
    rw [show C*w*(S*u) = C*(w*S)*u by noncomm_ring, ← hScomm w]; noncomm_ring]
  rw [show S*u*w*C = S*C*(u*w) by
    rw [show S*u*w*C = S*((u*w)*C) by noncomm_ring, ← hCcomm (u*w)]; noncomm_ring]
  rw [show S*u*w*(S*u) = S*S*(u*w*u) by
    rw [show S*u*w*(S*u) = S*((u*w)*S)*u by noncomm_ring, ← hScomm (u*w)]; noncomm_ring]
  rw [hwu, huwu]
  noncomm_ring

/-! ### Surjectivity of the double cover (Voight, Exercise 2.15)

Every `A ∈ SO(3)` fixes a unit axis `u`; picking a unit `w ⟂ u` and reading the angle `θ` off
the image `A w = a·w + b·(u×w)` (with `a² + b² = 1`) fixes the orientation, and
`α = cos(θ/2) + sin(θ/2)·u` realizes `A` by conjugation.  Matching `rotMatrix α = A` reduces to
agreement on the frame `{u, w, u×w}`. -/

lemma exists_theta_of_sq_add_sq_eq_one (a b : ℝ) (hab : a^2 + b^2 = 1) :
    ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = b := by
  set z : ℂ := (a : ℂ) + (b : ℂ) * Complex.I with hz
  have hz1 : ‖z‖ = 1 := by rw [hz, Complex.norm_add_mul_I, hab, Real.sqrt_one]
  have hz0 : z ≠ 0 := by rw [← norm_ne_zero_iff, hz1]; norm_num
  exact ⟨Complex.arg z, by rw [Complex.cos_arg hz0, hz1, div_one, hz]; simp,
    by rw [Complex.sin_arg, hz1, div_one, hz]; simp⟩

lemma so3_mulVec_cross (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    A *ᵥ (x ⨯₃ y) = (A *ᵥ x) ⨯₃ (A *ᵥ y) := by
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hA
  obtain ⟨hO, hdet⟩ := hA
  rw [Matrix.mem_orthogonalGroup_iff] at hO
  have hr00 := congrFun (congrFun hO 0) 0
  have hr01 := congrFun (congrFun hO 0) 1
  have hr02 := congrFun (congrFun hO 0) 2
  have hr11 := congrFun (congrFun hO 1) 1
  have hr12 := congrFun (congrFun hO 1) 2
  have hr22 := congrFun (congrFun hO 2) 2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply,
    Fin.sum_univ_three, Fin.reduceEq, if_true, if_false] at hr00 hr01 hr02 hr11 hr12 hr22
  rw [Matrix.det_fin_three] at hdet
  funext k
  fin_cases k <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, cross_apply,
      Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  · linear_combination ((A 1 0)*(A 2 1)*(x 0)*(y 1) - (A 1 0)*(A 2 1)*(x 1)*(y 0) + (A 1 0)*(A 2 2)*(x 0)*(y 2) - (A 1 0)*(A 2 2)*(x 2)*(y 0) - (A 1 1)*(A 2 0)*(x 0)*(y 1) + (A 1 1)*(A 2 0)*(x 1)*(y 0) + (A 1 1)*(A 2 2)*(x 1)*(y 2) - (A 1 1)*(A 2 2)*(x 2)*(y 1) - (A 1 2)*(A 2 0)*(x 0)*(y 2) + (A 1 2)*(A 2 0)*(x 2)*(y 0) - (A 1 2)*(A 2 1)*(x 1)*(y 2) + (A 1 2)*(A 2 1)*(x 2)*(y 1)) * hr00 + (-(A 0 0)*(A 2 1)*(x 0)*(y 1) + (A 0 0)*(A 2 1)*(x 1)*(y 0) - (A 0 0)*(A 2 2)*(x 0)*(y 2) + (A 0 0)*(A 2 2)*(x 2)*(y 0) + (A 0 1)*(A 2 0)*(x 0)*(y 1) - (A 0 1)*(A 2 0)*(x 1)*(y 0) - (A 0 1)*(A 2 2)*(x 1)*(y 2) + (A 0 1)*(A 2 2)*(x 2)*(y 1) + (A 0 2)*(A 2 0)*(x 0)*(y 2) - (A 0 2)*(A 2 0)*(x 2)*(y 0) + (A 0 2)*(A 2 1)*(x 1)*(y 2) - (A 0 2)*(A 2 1)*(x 2)*(y 1)) * hr01 + ((A 0 0)*(A 1 1)*(x 0)*(y 1) - (A 0 0)*(A 1 1)*(x 1)*(y 0) + (A 0 0)*(A 1 2)*(x 0)*(y 2) - (A 0 0)*(A 1 2)*(x 2)*(y 0) - (A 0 1)*(A 1 0)*(x 0)*(y 1) + (A 0 1)*(A 1 0)*(x 1)*(y 0) + (A 0 1)*(A 1 2)*(x 1)*(y 2) - (A 0 1)*(A 1 2)*(x 2)*(y 1) - (A 0 2)*(A 1 0)*(x 0)*(y 2) + (A 0 2)*(A 1 0)*(x 2)*(y 0) - (A 0 2)*(A 1 1)*(x 1)*(y 2) + (A 0 2)*(A 1 1)*(x 2)*(y 1)) * hr02 + (-(A 0 0)*(x 1)*(y 2) + (A 0 0)*(x 2)*(y 1) + (A 0 1)*(x 0)*(y 2) - (A 0 1)*(x 2)*(y 0) - (A 0 2)*(x 0)*(y 1) + (A 0 2)*(x 1)*(y 0)) * hdet
  · linear_combination ((A 1 0)*(A 2 1)*(x 0)*(y 1) - (A 1 0)*(A 2 1)*(x 1)*(y 0) + (A 1 0)*(A 2 2)*(x 0)*(y 2) - (A 1 0)*(A 2 2)*(x 2)*(y 0) - (A 1 1)*(A 2 0)*(x 0)*(y 1) + (A 1 1)*(A 2 0)*(x 1)*(y 0) + (A 1 1)*(A 2 2)*(x 1)*(y 2) - (A 1 1)*(A 2 2)*(x 2)*(y 1) - (A 1 2)*(A 2 0)*(x 0)*(y 2) + (A 1 2)*(A 2 0)*(x 2)*(y 0) - (A 1 2)*(A 2 1)*(x 1)*(y 2) + (A 1 2)*(A 2 1)*(x 2)*(y 1)) * hr01 + (-(A 0 0)*(A 2 1)*(x 0)*(y 1) + (A 0 0)*(A 2 1)*(x 1)*(y 0) - (A 0 0)*(A 2 2)*(x 0)*(y 2) + (A 0 0)*(A 2 2)*(x 2)*(y 0) + (A 0 1)*(A 2 0)*(x 0)*(y 1) - (A 0 1)*(A 2 0)*(x 1)*(y 0) - (A 0 1)*(A 2 2)*(x 1)*(y 2) + (A 0 1)*(A 2 2)*(x 2)*(y 1) + (A 0 2)*(A 2 0)*(x 0)*(y 2) - (A 0 2)*(A 2 0)*(x 2)*(y 0) + (A 0 2)*(A 2 1)*(x 1)*(y 2) - (A 0 2)*(A 2 1)*(x 2)*(y 1)) * hr11 + ((A 0 0)*(A 1 1)*(x 0)*(y 1) - (A 0 0)*(A 1 1)*(x 1)*(y 0) + (A 0 0)*(A 1 2)*(x 0)*(y 2) - (A 0 0)*(A 1 2)*(x 2)*(y 0) - (A 0 1)*(A 1 0)*(x 0)*(y 1) + (A 0 1)*(A 1 0)*(x 1)*(y 0) + (A 0 1)*(A 1 2)*(x 1)*(y 2) - (A 0 1)*(A 1 2)*(x 2)*(y 1) - (A 0 2)*(A 1 0)*(x 0)*(y 2) + (A 0 2)*(A 1 0)*(x 2)*(y 0) - (A 0 2)*(A 1 1)*(x 1)*(y 2) + (A 0 2)*(A 1 1)*(x 2)*(y 1)) * hr12 + (-(A 1 0)*(x 1)*(y 2) + (A 1 0)*(x 2)*(y 1) + (A 1 1)*(x 0)*(y 2) - (A 1 1)*(x 2)*(y 0) - (A 1 2)*(x 0)*(y 1) + (A 1 2)*(x 1)*(y 0)) * hdet
  · linear_combination ((A 1 0)*(A 2 1)*(x 0)*(y 1) - (A 1 0)*(A 2 1)*(x 1)*(y 0) + (A 1 0)*(A 2 2)*(x 0)*(y 2) - (A 1 0)*(A 2 2)*(x 2)*(y 0) - (A 1 1)*(A 2 0)*(x 0)*(y 1) + (A 1 1)*(A 2 0)*(x 1)*(y 0) + (A 1 1)*(A 2 2)*(x 1)*(y 2) - (A 1 1)*(A 2 2)*(x 2)*(y 1) - (A 1 2)*(A 2 0)*(x 0)*(y 2) + (A 1 2)*(A 2 0)*(x 2)*(y 0) - (A 1 2)*(A 2 1)*(x 1)*(y 2) + (A 1 2)*(A 2 1)*(x 2)*(y 1)) * hr02 + (-(A 0 0)*(A 2 1)*(x 0)*(y 1) + (A 0 0)*(A 2 1)*(x 1)*(y 0) - (A 0 0)*(A 2 2)*(x 0)*(y 2) + (A 0 0)*(A 2 2)*(x 2)*(y 0) + (A 0 1)*(A 2 0)*(x 0)*(y 1) - (A 0 1)*(A 2 0)*(x 1)*(y 0) - (A 0 1)*(A 2 2)*(x 1)*(y 2) + (A 0 1)*(A 2 2)*(x 2)*(y 1) + (A 0 2)*(A 2 0)*(x 0)*(y 2) - (A 0 2)*(A 2 0)*(x 2)*(y 0) + (A 0 2)*(A 2 1)*(x 1)*(y 2) - (A 0 2)*(A 2 1)*(x 2)*(y 1)) * hr12 + ((A 0 0)*(A 1 1)*(x 0)*(y 1) - (A 0 0)*(A 1 1)*(x 1)*(y 0) + (A 0 0)*(A 1 2)*(x 0)*(y 2) - (A 0 0)*(A 1 2)*(x 2)*(y 0) - (A 0 1)*(A 1 0)*(x 0)*(y 1) + (A 0 1)*(A 1 0)*(x 1)*(y 0) + (A 0 1)*(A 1 2)*(x 1)*(y 2) - (A 0 1)*(A 1 2)*(x 2)*(y 1) - (A 0 2)*(A 1 0)*(x 0)*(y 2) + (A 0 2)*(A 1 0)*(x 2)*(y 0) - (A 0 2)*(A 1 1)*(x 1)*(y 2) + (A 0 2)*(A 1 1)*(x 2)*(y 1)) * hr22 + (-(A 2 0)*(x 1)*(y 2) + (A 2 0)*(x 2)*(y 1) + (A 2 1)*(x 0)*(y 2) - (A 2 1)*(x 2)*(y 0) - (A 2 2)*(x 0)*(y 1) + (A 2 2)*(x 1)*(y 0)) * hdet

lemma exists_unit_orthogonal (uc : Fin 3 → ℝ) (_h : uc 0^2 + uc 1^2 + uc 2^2 = 1) :
    ∃ wc : Fin 3 → ℝ, (wc 0^2 + wc 1^2 + wc 2^2 = 1) ∧
      (uc 0 * wc 0 + uc 1 * wc 1 + uc 2 * wc 2 = 0) := by
  by_cases hz : uc 0 = 0 ∧ uc 1 = 0
  · exact ⟨![1, 0, 0], by simp, by simp [hz.1, hz.2]⟩
  · have hpos : 0 < uc 0 ^ 2 + uc 1 ^ 2 := by
      rcases not_and_or.mp hz with h0 | h1
      · have : 0 < uc 0 ^ 2 := by positivity
        nlinarith [sq_nonneg (uc 1)]
      · have : 0 < uc 1 ^ 2 := by positivity
        nlinarith [sq_nonneg (uc 0)]
    set r := Real.sqrt (uc 0 ^ 2 + uc 1 ^ 2) with hr
    have hrne : r ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
    have hr2 : r ^ 2 = uc 0 ^ 2 + uc 1 ^ 2 := by rw [hr, Real.sq_sqrt hpos.le]
    refine ⟨![uc 1 / r, -uc 0 / r, 0], ?_, ?_⟩ <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] <;> field_simp
    · nlinarith [hr2]
    · ring

/-- Coordinatewise additivity of `imVec`. -/
lemma imVec_add (p q : Quaternion ℝ) (i : Fin 3) :
    imVec (p + q) i = imVec p i + imVec q i := by
  fin_cases i <;> simp [imVec]

/-- Coordinatewise homogeneity of `imVec`. -/
lemma imVec_smul (c : ℝ) (p : Quaternion ℝ) (i : Fin 3) :
    imVec (c • p) i = c * imVec p i := by
  fin_cases i <;> simp [imVec]

lemma rotMatrix_mulVec (α : Quaternion ℝ) (v : Fin 3 → ℝ) :
    rotMatrix α *ᵥ v = imVec (conjEndo α (ofImVec v)) := by
  have hentry : ∀ i j, rotMatrix α i j = imVec (conjEndo α (frame j)) i := fun _ _ => rfl
  have hexpand : ofImVec v = v 0 • frame 0 + v 1 • frame 1 + v 2 • frame 2 := by
    ext <;> simp [ofImVec, frame]
  funext i
  have hlhs : (rotMatrix α *ᵥ v) i
      = rotMatrix α i 0 * v 0 + rotMatrix α i 1 * v 1 + rotMatrix α i 2 * v 2 := by
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hrhs : imVec (conjEndo α (ofImVec v)) i
      = v 0 * imVec (conjEndo α (frame 0)) i + v 1 * imVec (conjEndo α (frame 1)) i
        + v 2 * imVec (conjEndo α (frame 2)) i := by
    rw [hexpand, map_add, map_add, map_smul, map_smul, map_smul,
      imVec_add, imVec_add, imVec_smul, imVec_smul, imVec_smul]
  rw [hlhs, hrhs, hentry, hentry, hentry]
  ring

/-- An orthogonal matrix preserves the dot product: `(A x) ⬝ (A y) = x ⬝ y`. -/
lemma so3_dot_preserving (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) (x y : Fin 3 → ℝ) :
    (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = x ⬝ᵥ y := by
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hA
  obtain ⟨hO, _⟩ := hA
  rw [Matrix.mem_orthogonalGroup_iff'] at hO
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hO,
    Matrix.one_mulVec]

/-- Orthonormal expansion in the frame `{uc, wc, uc ⨯₃ wc}`: any `z ∈ ℝ³` equals
its coordinate expansion, because the three vectors form an orthonormal basis. -/
lemma ortho_expand (uc wc z : Fin 3 → ℝ)
    (hu : uc 0 ^ 2 + uc 1 ^ 2 + uc 2 ^ 2 = 1)
    (hw : wc 0 ^ 2 + wc 1 ^ 2 + wc 2 ^ 2 = 1)
    (ho : uc 0 * wc 0 + uc 1 * wc 1 + uc 2 * wc 2 = 0) :
    z = (z ⬝ᵥ uc) • uc + (z ⬝ᵥ wc) • wc + (z ⬝ᵥ (uc ⨯₃ wc)) • (uc ⨯₃ wc) := by
  funext i
  fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, dotProduct, Fin.sum_univ_three,
      cross_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
  · linear_combination (wc 0 * wc 1 * z 1 + wc 0 * wc 2 * z 2 - wc 1 ^ 2 * z 0 -
        wc 2 ^ 2 * z 0) * hu + (uc 0 ^ 2 * z 0 + uc 0 * uc 1 * z 1 + uc 0 * uc 2 * z 2 -
        z 0) * hw + (-(uc 0) * wc 0 * z 0 - uc 0 * wc 1 * z 1 - uc 0 * wc 2 * z 2 -
        uc 1 * wc 0 * z 1 + uc 1 * wc 1 * z 0 - uc 2 * wc 0 * z 2 + uc 2 * wc 2 * z 0) * ho
  · linear_combination (-(wc 0 ^ 2) * z 1 + wc 0 * wc 1 * z 0 + wc 1 * wc 2 * z 2 -
        wc 2 ^ 2 * z 1) * hu + (uc 0 * uc 1 * z 0 + uc 1 ^ 2 * z 1 + uc 1 * uc 2 * z 2 -
        z 1) * hw + (uc 0 * wc 0 * z 1 - uc 0 * wc 1 * z 0 - uc 1 * wc 0 * z 0 -
        uc 1 * wc 1 * z 1 - uc 1 * wc 2 * z 2 - uc 2 * wc 1 * z 2 + uc 2 * wc 2 * z 1) * ho
  · linear_combination (wc 0 * wc 2 * z 0 + wc 1 * wc 2 * z 1 + wc 2 ^ 2 * z 2 -
        z 2) * hu + (-(uc 0 ^ 2) * z 2 + uc 0 * uc 2 * z 0 - uc 1 ^ 2 * z 2 +
        uc 1 * uc 2 * z 1) * hw + (uc 0 * wc 0 * z 2 - uc 0 * wc 2 * z 0 +
        uc 1 * wc 1 * z 2 - uc 1 * wc 2 * z 1 - uc 2 * wc 0 * z 0 - uc 2 * wc 1 * z 1 -
        uc 2 * wc 2 * z 2) * ho

/-- `imVec (ofImVec uc) = uc`. -/
lemma imVec_ofImVec (uc : Fin 3 → ℝ) : imVec (ofImVec uc) = uc := by
  funext i; fin_cases i <;> simp [imVec, ofImVec]

/-- `ofImVec` is skew-adjoint. -/
lemma ofImVec_isSkewAdjoint (uc : Fin 3 → ℝ) : (ofImVec uc).IsSkewAdjoint := by
  rw [isSkewAdjoint_iff_re]; simp [ofImVec]

/-- `normSq (ofImVec uc)` from the coordinate norm. -/
lemma normSq_ofImVec (uc : Fin 3 → ℝ) (h : uc 0 ^ 2 + uc 1 ^ 2 + uc 2 ^ 2 = 1) :
    Quaternion.normSq (ofImVec uc) = 1 := by
  rw [Quaternion.normSq_def']; simp only [ofImVec]; nlinarith [h]

/-- `ofImVec` is additive. -/
lemma ofImVec_add (v w : Fin 3 → ℝ) : ofImVec (v + w) = ofImVec v + ofImVec w := by
  ext <;> simp [ofImVec]

/-- `ofImVec` is homogeneous. -/
lemma ofImVec_smul (c : ℝ) (v : Fin 3 → ℝ) : ofImVec (c • v) = c • ofImVec v := by
  ext <;> simp [ofImVec]

/-- Conjugation `conjEndo α` is multiplicative in its argument (for `α ≠ 0`):
`α(uv)α⁻¹ = (αuα⁻¹)(αvα⁻¹)`. -/
lemma conjEndo_arg_mul (α u v : Quaternion ℝ) (hα0 : α ≠ 0) :
    conjEndo α (u * v) = conjEndo α u * conjEndo α v := by
  rw [conjEndo_apply, conjEndo_apply, conjEndo_apply]
  have hcancel : α⁻¹ * α = 1 := inv_mul_cancel₀ hα0
  calc α * (u * v) * α⁻¹
      = α * u * (α⁻¹ * α) * v * α⁻¹ := by rw [hcancel]; noncomm_ring
    _ = α * u * α⁻¹ * (α * v * α⁻¹) := by noncomm_ring

theorem rotation_surjective (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : A ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ α : Quaternion ℝ, Quaternion.normSq α = 1 ∧ rotMatrix α = A := by
  -- STEP A: axis.
  obtain ⟨ue, hue1, hufix⟩ := so3_has_fixed_unit_axis A hA
  set uc : Fin 3 → ℝ := WithLp.equiv 2 (Fin 3 → ℝ) ue with hucdef
  have hAu : A *ᵥ uc = uc := by
    rw [hucdef]
    have h2 : (WithLp.equiv 2 (Fin 3 → ℝ)) (Matrix.toEuclideanLin A ue)
        = A *ᵥ (WithLp.equiv 2 (Fin 3 → ℝ)) ue := rfl
    rw [← h2, hufix]
  have hunorm : uc 0 ^ 2 + uc 1 ^ 2 + uc 2 ^ 2 = 1 := by
    have hsq : (uc 0 ^ 2 + uc 1 ^ 2 + uc 2 ^ 2) = (‖ue‖) ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
      simp only [hucdef, Real.norm_eq_abs, sq_abs]; rfl
    rw [hsq, hue1]; norm_num
  set uq : Quaternion ℝ := ofImVec uc with huqdef
  have huskew : uq.IsSkewAdjoint := ofImVec_isSkewAdjoint uc
  have hu1 : Quaternion.normSq uq = 1 := normSq_ofImVec uc hunorm
  have himuq : imVec uq = uc := imVec_ofImVec uc
  -- STEP B: perpendicular unit vector.
  obtain ⟨wc, hwnorm, hworth⟩ := exists_unit_orthogonal uc hunorm
  set wq : Quaternion ℝ := ofImVec wc with hwqdef
  have hwskew : wq.IsSkewAdjoint := ofImVec_isSkewAdjoint wc
  have hw1 : Quaternion.normSq wq = 1 := normSq_ofImVec wc hwnorm
  have himwq : imVec wq = wc := imVec_ofImVec wc
  have horth : uq.imI * wq.imI + uq.imJ * wq.imJ + uq.imK * wq.imK = 0 := by
    simp only [huqdef, hwqdef, ofImVec]; linarith [hworth]
  -- STEP C: the angle and the image of wc under A.
  have huu : uc ⬝ᵥ uc = 1 := by simp only [dotProduct, Fin.sum_univ_three]; nlinarith [hunorm]
  have hww : wc ⬝ᵥ wc = 1 := by simp only [dotProduct, Fin.sum_univ_three]; nlinarith [hwnorm]
  have huw : uc ⬝ᵥ wc = 0 := by simp only [dotProduct, Fin.sum_univ_three]; linarith [hworth]
  set a : ℝ := (A *ᵥ wc) ⬝ᵥ wc with hadef
  set b : ℝ := (A *ᵥ wc) ⬝ᵥ (uc ⨯₃ wc) with hbdef
  have hAwcnorm : (A *ᵥ wc) ⬝ᵥ (A *ᵥ wc) = 1 := by rw [so3_dot_preserving A hA]; exact hww
  have hAwcuc : (A *ᵥ wc) ⬝ᵥ uc = 0 := by
    rw [← hAu, so3_dot_preserving A hA, dotProduct_comm]; exact huw
  have hdecomp : A *ᵥ wc = a • wc + b • (uc ⨯₃ wc) := by
    have hexp := ortho_expand uc wc (A *ᵥ wc) hunorm hwnorm hworth
    rwa [hAwcuc, zero_smul, zero_add, ← hadef, ← hbdef] at hexp
  have hab : a ^ 2 + b ^ 2 = 1 := by
    have hcwn : (uc ⨯₃ wc) ⬝ᵥ (uc ⨯₃ wc) = 1 := by rw [cross_dot_cross, huu, hww, huw]; ring
    have hwcw : wc ⬝ᵥ (uc ⨯₃ wc) = 0 := dot_cross_self uc wc
    have hnorm2 : (A *ᵥ wc) ⬝ᵥ (A *ᵥ wc)
        = a ^ 2 * (wc ⬝ᵥ wc) + b ^ 2 * ((uc ⨯₃ wc) ⬝ᵥ (uc ⨯₃ wc))
          + 2 * a * b * (wc ⬝ᵥ (uc ⨯₃ wc)) := by
      rw [hdecomp]
      simp only [dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hAwcnorm, hww, hcwn, hwcw] at hnorm2; linarith [hnorm2]
  obtain ⟨θ, hcosθ, hsinθ⟩ := exists_theta_of_sq_add_sq_eq_one a b hab
  -- STEP D: the quaternion α.
  set α : Quaternion ℝ := ((Real.cos (θ / 2) : ℝ) : Quaternion ℝ) + Real.sin (θ / 2) • uq
    with hαdef
  have hαnorm : Quaternion.normSq α = 1 := normSq_cos_add_sin_smul uq huskew hu1 (θ / 2)
  have hα0 : α ≠ 0 := by
    intro h0; rw [h0, map_zero] at hαnorm; exact zero_ne_one hαnorm
  refine ⟨α, hαnorm, ?_⟩
  -- STEP E: rotMatrix α = A.
  -- The pre-imVec conjugation image of wq (used in both perp cases).
  have Cwc : conjEndo α wq = a • wq + b • (uq * wq) := by
    have := rotation_on_perp uq wq huskew hwskew hu1 hw1 horth (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring, hcosθ, hsinθ] at this
    rw [hαdef]; exact this
  -- The three basis images of `v ↦ imVec (conjEndo α (ofImVec v))`.
  have Kuc : imVec (conjEndo α (ofImVec uc)) = A *ᵥ uc := by
    rw [← huqdef, hαdef, rotation_fixes_axis uq huskew hu1 (θ / 2), himuq, hAu]
  have hdot : (⟪uq, wq⟫ : ℝ) = 0 := by
    rw [Quaternion.inner_def]
    have hwstar : star wq = -wq := Quaternion.star_eq_neg.mpr ((isSkewAdjoint_iff_re wq).mp hwskew)
    rw [hwstar, mul_neg]
    simp only [Quaternion.re_neg, Quaternion.re_mul]
    have hure : uq.re = 0 := (isSkewAdjoint_iff_re uq).mp huskew
    have hwre : wq.re = 0 := (isSkewAdjoint_iff_re wq).mp hwskew
    rw [hure, hwre]; linarith [horth]
  have hprodcross : uq * wq = crossQuat uq wq := by
    rw [pure_product uq wq huskew hwskew, hdot]; simp
  have hwqim : imVec (uq * wq) = uc ⨯₃ wc := by
    rw [pure_product_im uq wq huskew hwskew, himuq, himwq]
  -- imVec of the common combination `a•wq + b•(uq*wq)`.
  have himAB : imVec (a • wq + b • (uq * wq)) = a • wc + b • (uc ⨯₃ wc) := by
    funext i
    rw [imVec_add _ _ i, imVec_smul _ _ i, imVec_smul _ _ i]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [congrFun himwq i, congrFun hwqim i]
  have Kwc : imVec (conjEndo α (ofImVec wc)) = A *ᵥ wc := by
    rw [← hwqdef, Cwc, himAB, hdecomp]
  have Kcw : imVec (conjEndo α (ofImVec (uc ⨯₃ wc))) = A *ᵥ (uc ⨯₃ wc) := by
    rw [show ofImVec (uc ⨯₃ wc) = uq * wq by rw [hprodcross, crossQuat, himuq, himwq],
      conjEndo_arg_mul α uq wq hα0,
      show conjEndo α uq = uq by rw [hαdef]; exact rotation_fixes_axis uq huskew hu1 (θ / 2), Cwc]
    have hpskew : (a • wq + b • (uq * wq)).IsSkewAdjoint := by
      rw [isSkewAdjoint_iff_re]
      have h2 : (uq * wq).re = 0 := by rw [pure_product_re uq wq huskew hwskew, hdot, neg_zero]
      simp [Quaternion.re_add, Quaternion.re_smul, (isSkewAdjoint_iff_re wq).mp hwskew, h2]
    rw [pure_product_im uq _ huskew hpskew, himuq, himAB, so3_mulVec_cross A hA uc wc, hAu, hdecomp]
  -- Reduce `rotMatrix α = A` to agreement on all `v`, then use linearity + basis.
  rw [Matrix.ext_iff_mulVec]
  intro v
  rw [rotMatrix_mulVec]
  have hArest : A *ᵥ v = (v ⬝ᵥ uc) • (A *ᵥ uc) + (v ⬝ᵥ wc) • (A *ᵥ wc)
      + (v ⬝ᵥ (uc ⨯₃ wc)) • (A *ᵥ (uc ⨯₃ wc)) := by
    conv_lhs => rw [ortho_expand uc wc v hunorm hwnorm hworth]
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul]
  rw [hArest]
  conv_lhs => rw [ortho_expand uc wc v hunorm hwnorm hworth]
  rw [ofImVec_add, ofImVec_add, ofImVec_smul, ofImVec_smul, ofImVec_smul, map_add, map_add,
    map_smul, map_smul, map_smul]
  funext i
  simp only [imVec_add, imVec_smul, Kuc, Kwc, Kcw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- The matrix-valued monoid homomorphism `u ↦ toMatrix (adjoint u)` underlying the
rotation action, before corestricting to `SO(3)`. -/
noncomputable def rotationHom' : unitary (Quaternion ℝ) →* Matrix (Fin 3) (Fin 3) ℝ :=
  { toFun := fun u => LinearMap.toMatrix pureBasis pureBasis (adjoint u).toLinearMap
    map_one' := by rw [map_one, LinearEquiv.coe_toLinearMap_one, LinearMap.toMatrix_id]
    map_mul' := fun u w => by
      rw [map_mul, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul] }

@[simp] lemma rotationHom'_apply (u : unitary (Quaternion ℝ)) :
    rotationHom' u = rotMatrix ↑u := adjoint_toMatrix u

lemma rotationHom'_mem_so (u : unitary (Quaternion ℝ)) :
    rotationHom' u ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [rotationHom'_apply]; exact rotMatrix_mem_so ↑u ((mem_unitary_iff_normSq _).mp u.2)

/-- The **rotation homomorphism** `ρ : ℍ¹ = unitary ℍ →* SO(3)`, `u ↦ ρ_u`, whose
underlying matrix in the orthonormal frame `i, j, k` is `rotMatrix ↑u`. This is the
group homomorphism realizing the double cover. -/
noncomputable def rotationHom :
    unitary (Quaternion ℝ) →* Matrix.specialOrthogonalGroup (Fin 3) ℝ :=
  rotationHom'.codRestrict _ rotationHom'_mem_so

/-- **Surjectivity of the double cover**: every `A ∈ SO(3)` is `ρ_α` for some unit
quaternion `α`. -/
theorem rotationHom_surjective : Function.Surjective rotationHom := by
  rintro ⟨A, hA⟩
  obtain ⟨α, hαnorm, hαA⟩ := rotation_surjective A hA
  refine ⟨⟨α, (mem_unitary_iff_normSq _).mpr hαnorm⟩, ?_⟩
  apply Subtype.ext
  show rotationHom' _ = A
  rw [rotationHom'_apply]; exact hαA

/-- **Kernel of the double cover**: `ρ_x = 1` exactly when `x = ±1`. -/
theorem rotationHom_apply_eq_one_iff (x : unitary (Quaternion ℝ)) :
    rotationHom x = 1 ↔ (x : Quaternion ℝ) = 1 ∨ (x : Quaternion ℝ) = -1 := by
  rw [Subtype.ext_iff]
  show rotationHom' x = ↑(1 : Matrix.specialOrthogonalGroup (Fin 3) ℝ) ↔ _
  rw [Submonoid.coe_one, rotationHom'_apply]
  constructor
  · intro hmat
    -- `rotMatrix ↑x = 1` forces `(adjoint x).toLinearMap = id`, so conjugation fixes `ℍ⁰`.
    have hlin : (adjoint x).toLinearMap = LinearMap.id :=
      (LinearMap.toMatrix pureBasis pureBasis).injective (by
        rw [adjoint_toMatrix, LinearMap.toMatrix_id, hmat])
    refine rotation_kernel ↑x ((mem_unitary_iff_normSq _).mp x.2) fun v hv => ?_
    set y : skewAdjoint.submodule ℝ (Quaternion ℝ) :=
      ⟨v, (mem_skewAdjoint_submodule_iff v).mpr ((isSkewAdjoint_iff_re v).mp hv)⟩
    have hid := congrArg (fun (L : _ →ₗ[ℝ] _) => (L y : skewAdjoint.submodule ℝ (Quaternion ℝ))) hlin
    simp only [LinearMap.id_apply] at hid
    have hval : (↑((adjoint x).toLinearMap y) : Quaternion ℝ) = conjEndo ↑x v := by
      show (↑(rotEquiv x y) : Quaternion ℝ) = conjEndo ↑x v
      rw [rotEquiv_coe_apply, conjEndo_apply]
    rw [← hval]; exact congrArg Subtype.val hid
  · rintro (hx | hx) <;> rw [hx]
    · rw [rotMatrix_eq 1 (by rw [map_one])]; ext i j; fin_cases i <;> fin_cases j <;> simp
    · rw [rotMatrix_eq (-1) (by rw [Quaternion.normSq_neg, map_one])]
      ext i j; fin_cases i <;> fin_cases j <;> simp

/-- The kernel of the rotation homomorphism is `{±1}`. -/
theorem mem_rotationHom_ker (x : unitary (Quaternion ℝ)) :
    x ∈ rotationHom.ker ↔ (x : Quaternion ℝ) = 1 ∨ (x : Quaternion ℝ) = -1 := by
  rw [MonoidHom.mem_ker]; exact rotationHom_apply_eq_one_iff x

/-- Bridge: for `x : unitary (Quaternion ℝ)`, `↑x = 1 ↔ x = 1`. -/
theorem coe_eq_one_iff (x : unitary (Quaternion ℝ)) :
    (x : Quaternion ℝ) = 1 ↔ x = 1 := by
  rw [Subtype.ext_iff]; rfl

/-- Bridge: for `x : unitary (Quaternion ℝ)`, `↑x = -1 ↔ x = -1`. -/
theorem coe_eq_neg_one_iff (x : unitary (Quaternion ℝ)) :
    (x : Quaternion ℝ) = -1 ↔ x = -1 := by
  rw [Subtype.ext_iff, Unitary.coe_neg]; rfl

/-- The kernel of the rotation homomorphism is `{-1, 1}` (Voight, Corollary 2.4.21):
together with `rotationHom_surjective`, this is the double cover `ℍ¹ → SO(3)`. -/
theorem rotationHom_ker :
    (rotationHom.ker : Set (unitary (Quaternion ℝ))) = {-1, 1} := by
  ext x
  rw [SetLike.mem_coe, mem_rotationHom_ker, coe_eq_one_iff, coe_eq_neg_one_iff,
    Set.mem_insert_iff, Set.mem_singleton_iff, or_comm]

end QuaternionAlgebras
