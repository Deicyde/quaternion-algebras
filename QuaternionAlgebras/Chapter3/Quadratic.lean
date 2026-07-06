import Mathlib
import QuaternionAlgebras.Chapter3.Involutions

/-!
# Quadratic algebras and uniqueness of standard involutions (Voight, Chapter 3)

A **quadratic algebra** is an `F`-algebra `K` with `dim_F K = 2` (the abstract
`Module.finrank` condition, not the concrete `QuadraticAlgebra` type).  We prove the
basis decomposition, the quadratic relation, commutativity, the existence and
uniqueness of the standard (conjugation) involution, and deduce that a standard
involution on any algebra is unique.
-/

namespace QuaternionAlgebras.Chapter3

/-- **Quadratic algebra.** `K` is a quadratic `F`-algebra if `dim_F K = 2`. -/
def IsQuadraticAlgebra (F K : Type*) [Field F] [Ring K] [Algebra F K] : Prop :=
  Module.finrank F K = 2

variable {F K : Type*} [Field F] [Ring K] [Algebra F K]

/-- **Basis decomposition of a quadratic algebra.** For `α ∈ K \ F`, `{1, α}` is an
`F`-basis of `K`. -/
theorem quadratic_basis (h : IsQuadraticAlgebra F K) (α : K)
    (hα : α ∉ Set.range (algebraMap F K)) :
    ∃ b : Module.Basis (Fin 2) F K, b 0 = 1 ∧ b 1 = α := by
  sorry

/-- **Quadratic relation.** For `α ∈ K \ F` there are unique `t, n ∈ F` with
`α² = t α - n`. -/
theorem quadratic_min_rel (h : IsQuadraticAlgebra F K) (α : K)
    (hα : α ∉ Set.range (algebraMap F K)) :
    ∃! p : F × F, α ^ 2 = algebraMap F K p.1 * α - algebraMap F K p.2 := by
  sorry

/-- **A quadratic algebra is commutative.** -/
theorem quadratic_comm (h : IsQuadraticAlgebra F K) (x y : K) : x * y = y * x := by
  sorry

/-- **The conjugation map on a quadratic algebra is an involution.** Given `α ∈ K \ F`
with `α² = t α - n`, there is an involution `⁻` fixing `F` with `ᾱ = t - α`. -/
theorem quadratic_conjugation_involution (h : IsQuadraticAlgebra F K) (α : K)
    (hα : α ∉ Set.range (algebraMap F K)) (t n : F)
    (hrel : α ^ 2 = algebraMap F K t * α - algebraMap F K n) :
    ∃ inv : Involution F K, inv.toLinearMap α = algebraMap F K t - α := by
  sorry

/-- **The conjugation map on a quadratic algebra is standard.** Any involution with
`ᾱ = t - α` (in the quadratic situation) is standard. -/
theorem quadratic_conjugation_standard (h : IsQuadraticAlgebra F K) (α : K)
    (hα : α ∉ Set.range (algebraMap F K)) (t n : F)
    (hrel : α ^ 2 = algebraMap F K t * α - algebraMap F K n)
    (inv : Involution F K) (hfα : inv.toLinearMap α = algebraMap F K t - α) :
    inv.IsStandard := by
  sorry

/-- **Existence of a standard involution on a quadratic algebra.** -/
theorem quadratic_involution_exists (h : IsQuadraticAlgebra F K) (α : K)
    (hα : α ∉ Set.range (algebraMap F K)) (t n : F)
    (hrel : α ^ 2 = algebraMap F K t * α - algebraMap F K n) :
    ∃ inv : Involution F K, inv.IsStandard ∧ inv.toLinearMap α = algebraMap F K t - α := by
  sorry

/-- **Uniqueness of a standard involution on a quadratic algebra.** Any standard
involution sends `α` to `t - α`. -/
theorem quadratic_involution_unique (h : IsQuadraticAlgebra F K) (α : K)
    (hα : α ∉ Set.range (algebraMap F K)) (t n : F)
    (hrel : α ^ 2 = algebraMap F K t * α - algebraMap F K n)
    (inv : Involution F K) (hinv : inv.IsStandard) :
    inv.toLinearMap α = algebraMap F K t - α := by
  sorry

/-- **Unique standard involution on a quadratic algebra.** There is exactly one
standard involution on a quadratic algebra. -/
theorem quadratic_unique_involution (h : IsQuadraticAlgebra F K) :
    ∃! inv : Involution F K, inv.IsStandard := by
  sorry

variable {B : Type*} [Ring B] [Algebra F B]

/-- **A standard involution is determined outside the base field.** For `α ∈ B \ F`,
`ᾱ = trd(α) - α`, so its value is forced. -/
theorem involution_determined_outside_base (inv : Involution F B) (h : inv.IsStandard)
    (α : B) (hα : α ∉ Set.range (algebraMap F B)) :
    inv.toLinearMap α = algebraMap F B (inv.reducedTrace h α) - α := by
  sorry

/-- **A standard involution is unique.** If `B` has a standard involution, it is the
only one. -/
theorem involution_unique (inv₁ inv₂ : Involution F B)
    (h₁ : inv₁.IsStandard) (h₂ : inv₂.IsStandard) : inv₁ = inv₂ := by
  sorry

end QuaternionAlgebras.Chapter3
