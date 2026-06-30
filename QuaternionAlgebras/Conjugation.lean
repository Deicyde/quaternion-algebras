import Mathlib

/-!
# Conjugation, norm, and pure quaternions

We work with the real Hamiltonians `ℍ = Quaternion ℝ = ℍ[ℝ, -1, 0, -1]`.  The
standard involution is `star`, the squared norm is `Quaternion.normSq`, and the
pure (imaginary) quaternions are the skew-adjoint elements
`skewAdjoint.submodule ℝ (Quaternion ℝ)` (those with `star α = -α`), while the
real quaternions are the self-adjoint elements `selfAdjoint.submodule ℝ
(Quaternion ℝ)`.
-/

namespace QuaternionAlgebras

open scoped Quaternion

/-- The real scalar action commutes with conjugation, making `Quaternion ℝ` a
star module over `ℝ`. -/
instance : StarModule ℝ (Quaternion ℝ) := ⟨fun r x => by ext <;> simp⟩

/-- Trace and norm via conjugation: `α + ᾱ = 2 t` and
`α ᾱ = ᾱ α = t² + x² + y² + z² = normSq α`. -/
lemma trace_norm (α : Quaternion ℝ) :
    α + star α = ((2 * α.re : ℝ) : Quaternion ℝ) ∧
      α * star α = ((Quaternion.normSq α : ℝ) : Quaternion ℝ) ∧
      star α * α = ((Quaternion.normSq α : ℝ) : Quaternion ℝ) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using Quaternion.self_add_star' α
  · simpa using Quaternion.self_mul_star α
  · simpa using Quaternion.star_mul_self α

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
    v.re = 0 ↔ v ^ 2 = -((Quaternion.normSq v : ℝ) : Quaternion ℝ) := by
  simpa using (Quaternion.sq_eq_neg_normSq (a := v)).symm

/-- Real part of a product of pure quaternions: minus the dot product. -/
lemma pure_product_re (v w : Quaternion ℝ) (hv : v.re = 0) (hw : w.re = 0) :
    (v * w).re = -(v.imI * w.imI + v.imJ * w.imJ + v.imK * w.imK) := by
  rw [Quaternion.re_mul, hv, hw]
  ring

/-- Imaginary part of a product of pure quaternions: the cross product. -/
lemma pure_product_im (v w : Quaternion ℝ) (hv : v.re = 0) (hw : w.re = 0) :
    (v * w).imI = v.imJ * w.imK - v.imK * w.imJ ∧
      (v * w).imJ = v.imK * w.imI - v.imI * w.imK ∧
      (v * w).imK = v.imI * w.imJ - v.imJ * w.imI := by
  have hI : (v * w).imI = v.imJ * w.imK - v.imK * w.imJ := by
    rw [Quaternion.imI_mul, hv, hw]
    ring
  have hJ : (v * w).imJ = v.imK * w.imI - v.imI * w.imK := by
    rw [Quaternion.imJ_mul, hv, hw]
    ring
  have hK : (v * w).imK = v.imI * w.imJ - v.imJ * w.imI := by
    rw [Quaternion.imK_mul, hv, hw]
    ring
  exact ⟨hI, hJ, hK⟩

/-- Product of pure quaternions: `vw = -(v·w) + (v×w)`, with the dot product as
the real part and the cross product as the (pure) imaginary part. -/
lemma pure_product (v w : Quaternion ℝ) (hv : v.re = 0) (hw : w.re = 0) :
    v * w =
      (⟨-(v.imI * w.imI + v.imJ * w.imJ + v.imK * w.imK),
        v.imJ * w.imK - v.imK * w.imJ, v.imK * w.imI - v.imI * w.imK,
        v.imI * w.imJ - v.imJ * w.imI⟩ : Quaternion ℝ) := by
  have hre := pure_product_re v w hv hw
  have ⟨hI, hJ, hK⟩ := pure_product_im v w hv hw
  ext <;> simp [hre, hI, hJ, hK]

/-- Orthogonality criteria for pure quaternions:
(a) `vw` is pure iff `v ⟂ w`; (b) `wv = -vw` iff `v ⟂ w`. -/
lemma pure_orthogonal (v w : Quaternion ℝ) (hv : v.re = 0) (hw : w.re = 0) :
    ((v * w).re = 0 ↔ v.imI * w.imI + v.imJ * w.imJ + v.imK * w.imK = 0) ∧
      (w * v = -(v * w) ↔
        v.imI * w.imI + v.imJ * w.imJ + v.imK * w.imK = 0) := by sorry

end QuaternionAlgebras
