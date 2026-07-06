import Mathlib
import QuaternionAlgebras.Chapter3.Classification

/-!
# Frobenius' theorem (Voight, Chapter 3)

We record the real-field consequences of the degree-two classification: a quadratic
extension of `ℝ` is `ℂ`, real division quaternion algebras are `ℍ`, and Frobenius'
theorem classifying algebraic division algebras over `ℝ`.
-/

namespace QuaternionAlgebras.Chapter3

open scoped Quaternion

/-- **Algebraic algebra.** `B` is algebraic over `F` if every element is algebraic. -/
def IsAlgebraicAlgebra (F B : Type*) [Field F] [Ring B] [Algebra F B] : Prop :=
  ∀ α : B, IsAlgebraic F α

/-- **A quadratic extension of `ℝ` is `ℂ`.** -/
theorem real_quadratic_ext_eq_C (L : Type*) [Field L] [Algebra ℝ L]
    (h : Module.finrank ℝ L = 2) : Nonempty (L ≃ₐ[ℝ] ℂ) := by
  sorry

/-- **Square-rescaling isomorphism of quaternion algebras.** For `a, b, u, v ∈ Fˣ`,
`ℍ[F,a,0,b] ≅ ℍ[F, a u², 0, b v²]`. -/
theorem quaternion_square_rescale {F : Type*} [Field F] (a b u v : F)
    (ha : a ≠ 0) (hb : b ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0) :
    Nonempty (ℍ[F, a, 0, b] ≃ₐ[F] ℍ[F, a * u ^ 2, 0, b * v ^ 2]) := by
  sorry

/-- **A quaternion algebra with a square coefficient is not division.** If
`char F ≠ 2` and `a = c²` with `c ∈ Fˣ`, then `ℍ[F,a,0,b]` has a nonzero non-unit. -/
theorem quaternion_isotropic_not_division {F : Type*} [Field F] (hchar : (2 : F) ≠ 0)
    (a b c : F) (hc : c ≠ 0) (hac : a = c ^ 2) :
    ∃ x : ℍ[F, a, 0, b], x ≠ 0 ∧ ¬ IsUnit x := by
  sorry

/-- **The real division quaternion algebra is `ℍ`.** A division quaternion algebra
over `ℝ` has `a, b < 0` and is isomorphic to `ℍ[ℝ,-1,0,-1] = ℍ`. -/
theorem real_division_quaternion_eq_H (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0)
    (hdiv : ∀ x : ℍ[ℝ, a, 0, b], x ≠ 0 → IsUnit x) :
    a < 0 ∧ b < 0 ∧ Nonempty (ℍ[ℝ, a, 0, b] ≃ₐ[ℝ] ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) := by
  sorry

/-- **Frobenius.** An algebraic division algebra over `ℝ` is `ℝ`, `ℂ`, or `ℍ`. -/
theorem frobenius (B : Type*) [DivisionRing B] [Algebra ℝ B]
    (halg : IsAlgebraicAlgebra ℝ B) :
    Function.Surjective (algebraMap ℝ B) ∨ Nonempty (B ≃ₐ[ℝ] ℂ) ∨
      Nonempty (B ≃ₐ[ℝ] ℍ[ℝ, (-1 : ℝ), 0, (-1 : ℝ)]) := by
  sorry

end QuaternionAlgebras.Chapter3
