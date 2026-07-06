import Mathlib
import QuaternionAlgebras.Chapter2.Beginnings

/-!
# Involutions, reduced trace and reduced norm (Voight, Chapter 3, §3.1–3.2)

We follow Voight, *Quaternion Algebras*, Chapter 3.  Throughout `F` is a
(commutative) field and `B` is an associative `F`-algebra with `1 ≠ 0`.

An **involution** on `B` is an `F`-linear anti-automorphism fixing `1` and squaring
to the identity.  The blueprint's intended model is a `StarRing`/`StarModule F B`;
because `StarModule F B` demands a `Star F` instance (which a bare field lacks), we
instead bundle the involution as a structure carrying the `F`-linear map `B →ₗ[F] B`
and its three axioms.  This is equivalent and fully faithful to the definition.  For
the quaternion algebra `ℍ[F,a,0,b]` this map is Mathlib's `star`.

The predicate "`α ∈ F`" is encoded as `α ∈ Set.range (algebraMap F B)`.
-/

namespace QuaternionAlgebras.Chapter3

open scoped Quaternion

/-- **Involution.** An involution on `B` is an `F`-linear map `⁻ : B → B` with
(i) `1̄ = 1`; (ii) `α̿ = α`; (iii) `α β‾ = β̄ ᾱ` (an anti-automorphism). -/
structure Involution (F B : Type*) [Field F] [Ring B] [Algebra F B] where
  /-- The underlying `F`-linear map `α ↦ ᾱ`. -/
  toLinearMap : B →ₗ[F] B
  /-- (i) `1̄ = 1`. -/
  map_one : toLinearMap 1 = 1
  /-- (ii) the map is involutive. -/
  involutive : Function.Involutive toLinearMap
  /-- (iii) the map is anti-multiplicative. -/
  map_mul_rev : ∀ α β : B, toLinearMap (α * β) = toLinearMap β * toLinearMap α

variable {F B : Type*} [Field F] [Ring B] [Algebra F B]

/-- **Standard involution.** An involution is *standard* if `α · ᾱ ∈ F` for all `α`. -/
def Involution.IsStandard (inv : Involution F B) : Prop :=
  ∀ α : B, α * inv.toLinearMap α ∈ Set.range (algebraMap F B)

/-- `B` **has a standard involution** if some involution on `B` is standard. -/
def HasStandardInvolution (F B : Type*) [Field F] [Ring B] [Algebra F B] : Prop :=
  ∃ inv : Involution F B, inv.IsStandard

/-- **Trace lands in the base field.** For a standard involution, `α + ᾱ ∈ F`. -/
theorem Involution.trace_in_base (inv : Involution F B) (h : inv.IsStandard) (α : B) :
    α + inv.toLinearMap α ∈ Set.range (algebraMap F B) := by
  sorry

/-- **Conjugate commutes with element.** For a standard involution, `α ᾱ = ᾱ α`. -/
theorem Involution.self_mul_star_comm (inv : Involution F B) (h : inv.IsStandard) (α : B) :
    α * inv.toLinearMap α = inv.toLinearMap α * α := by
  sorry

/-- **Reduced trace.** `trd α = α + ᾱ`, viewed as an element of `F` via the
(injective) structure map; it lands in `F` by `trace_in_base`. -/
noncomputable def Involution.reducedTrace (inv : Involution F B) (h : inv.IsStandard)
    (α : B) : F :=
  (inv.trace_in_base h α).choose

/-- Defining property of the reduced trace: `algebraMap F B (trd α) = α + ᾱ`. -/
theorem Involution.algebraMap_reducedTrace (inv : Involution F B) (h : inv.IsStandard)
    (α : B) : algebraMap F B (inv.reducedTrace h α) = α + inv.toLinearMap α :=
  (inv.trace_in_base h α).choose_spec

/-- **Reduced norm.** `nrd α = α ᾱ`, viewed as an element of `F`; it lands in `F` by
standardness. -/
noncomputable def Involution.reducedNorm (inv : Involution F B) (h : inv.IsStandard)
    (α : B) : F :=
  (h α).choose

/-- Defining property of the reduced norm: `algebraMap F B (nrd α) = α ᾱ`. -/
theorem Involution.algebraMap_reducedNorm (inv : Involution F B) (h : inv.IsStandard)
    (α : B) : algebraMap F B (inv.reducedNorm h α) = α * inv.toLinearMap α :=
  (h α).choose_spec

/-- **Reduced trace is `F`-linear.** -/
theorem Involution.reducedTrace_isLinear [Nontrivial B] (inv : Involution F B)
    (h : inv.IsStandard) :
    IsLinearMap F (inv.reducedTrace h) := by
  sorry

/-- **Reduced norm is multiplicative** (and unital). -/
theorem Involution.reducedNorm_mul [Nontrivial B] (inv : Involution F B) (h : inv.IsStandard) :
    (∀ α β : B, inv.reducedNorm h (α * β) = inv.reducedNorm h α * inv.reducedNorm h β) ∧
      inv.reducedNorm h 1 = 1 := by
  sorry

/-- **Nonzero norm gives a unit**, with explicit inverse `nrd(α)⁻¹ • ᾱ`. -/
theorem Involution.isUnit_of_reducedNorm_ne_zero (inv : Involution F B) (h : inv.IsStandard)
    {α : B} (hn : inv.reducedNorm h α ≠ 0) : IsUnit α := by
  sorry

/-- **A unit has nonzero norm.** -/
theorem Involution.reducedNorm_ne_zero_of_isUnit [Nontrivial B] (inv : Involution F B)
    (h : inv.IsStandard) {α : B} (hu : IsUnit α) : inv.reducedNorm h α ≠ 0 := by
  sorry

/-- **Units are exactly the elements of nonzero reduced norm.** -/
theorem Involution.isUnit_iff_reducedNorm_ne_zero [Nontrivial B] (inv : Involution F B)
    (h : inv.IsStandard) (α : B) : IsUnit α ↔ inv.reducedNorm h α ≠ 0 := by
  sorry

/-- **Reduced trace is symmetric on products.** -/
theorem Involution.reducedTrace_mul_comm (inv : Involution F B) (h : inv.IsStandard) (α β : B) :
    inv.reducedTrace h (β * α) = inv.reducedTrace h (α * β) := by
  sorry

/-- **Reduced characteristic polynomial / Cayley–Hamilton.** Every `α ∈ B` satisfies
`α² - trd(α)·α + nrd(α) = 0`. -/
theorem Involution.reduced_char_poly (inv : Involution F B) (h : inv.IsStandard) (α : B) :
    α ^ 2 - algebraMap F B (inv.reducedTrace h α) * α
      + algebraMap F B (inv.reducedNorm h α) = 0 := by
  sorry

/-! ### The quaternion algebra example -/

/-- **Norm form of a quaternion algebra.** For `α = t + xi + yj + zij` in
`ℍ[F,a,0,b]`, `α · star α = t² - a x² - b y² + ab z²`, a scalar. -/
theorem quaternion_normForm (a b : F) (α : ℍ[F, a, 0, b]) :
    α * star α =
      algebraMap F ℍ[F, a, 0, b]
        (α.re ^ 2 - a * α.imI ^ 2 - b * α.imJ ^ 2 + a * b * α.imK ^ 2) := by
  sorry

/-- **Conjugation is a standard involution on a quaternion algebra.** There is a
standard involution on `ℍ[F,a,0,b]` whose underlying map is Mathlib's `star`. -/
theorem quaternion_isStandardInvolution (a b : F) :
    ∃ inv : Involution F ℍ[F, a, 0, b],
      inv.IsStandard ∧ ∀ α, inv.toLinearMap α = star α := by
  sorry

/-! ### Bounded degree -/

/-- **Bounded degree.** `B` has degree at most `m` if every `α ∈ B` is a root of some
monic `f ∈ F[X]` of degree `≤ m`. -/
def HasDegreeLE (F B : Type*) [Field F] [Ring B] [Algebra F B] (m : ℕ) : Prop :=
  ∀ α : B, ∃ p : Polynomial F, p.Monic ∧ p.natDegree ≤ m ∧ Polynomial.aeval α p = 0

/-- **Finite-dimensional algebras have finite degree.** If `dim_F B = n < ∞` then
`B` has degree at most `n`. -/
theorem hasDegreeLE_of_finite [Module.Finite F B] :
    HasDegreeLE F B (Module.finrank F B) := by
  sorry

/-- **Degree one means the base field.** If `B` has degree `≤ 1` then `B = F`, i.e.
the structure map is surjective. -/
theorem surjective_algebraMap_of_hasDegreeLE_one (h : HasDegreeLE F B 1) :
    Function.Surjective (algebraMap F B) := by
  sorry

/-- **A standard involution forces degree at most two.** -/
theorem hasDegreeLE_two_of_standard (inv : Involution F B) (h : inv.IsStandard) :
    HasDegreeLE F B 2 := by
  sorry

end QuaternionAlgebras.Chapter3
