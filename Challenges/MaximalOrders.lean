import Mathlib
-- Self-contained challenge file: imports **only** Mathlib and defines every
-- prerequisite below.  Written against Mathlib master (commit d255f67ec8,
-- toolchain `leanprover/lean4:v4.32.0-rc1`), the checkout used by the
-- `quaternion-algebras` project.  The final statement ends in `sorry`.
--
-- Machine-elaborated clean with `lake env lean` against the above toolchain
-- (only the expected `declaration uses 'sorry'` warning at the theorem).

/-!
# Challenge: quaternion algebras over number fields have maximal orders

A formalization target from John Voight, *Quaternion Algebras* (GTM 288, 2021;
open-access edition at https://quatalg.org).

> **Proposition 15.5.2** (number-field case). *Let `K` be a number field with ring
> of integers `𝓞 K`, and let `B` be a quaternion algebra over `K`. Then there exists
> a maximal `𝓞 K`-order `O ⊆ B`, and every `𝓞 K`-order in `B` is contained in a
> maximal `𝓞 K`-order.*

(Voight's Proposition 15.5.2 is stated over an arbitrary Dedekind domain `R` with
fraction field `F`; here we specialize to `R = 𝓞 K`, `F = K`, which is exactly the
statement "quaternion algebras over number fields have maximal orders".)

## Modeling choices

* A **quaternion algebra over `K`** is presented concretely as `(a, b ∣ K) = ℍ[K, a, 0, b]`
  with `a, b ∈ Kˣ` (Voight's `(a, b ∣ K)`; `open scoped Quaternion`).  Over a field of
  characteristic `≠ 2` — in particular any number field — every quaternion algebra is
  isomorphic to such an `ℍ[K, a, 0, b]` with `a, b ≠ 0`, so quantifying over the parameters
  `a b : K` with `a ≠ 0`, `b ≠ 0` is a faithful (presentation-free) statement of the result.
  Using the concrete form makes `Algebra (𝓞 K) ℍ[K, a, 0, b]` and
  `IsScalarTower (𝓞 K) K ℍ[K, a, 0, b]` genuine Mathlib instances
  (`Mathlib/Algebra/Quaternion.lean`), so no algebra/scalar-tower structure need be assumed.
* An **`R`-lattice** (Voight, Definition 9.3.1) in a finite-dimensional `F`-vector space `V`,
  `F = Frac R`, is a finitely generated `R`-submodule `M ⊆ V` with `M F = V`. See `IsRLattice`.
* An **`R`-order** (Voight, Definition 10.2.1) in a finite-dimensional `F`-algebra `B`,
  `F = Frac R`, is an `R`-lattice that is also a subring of `B`.  This is stated for an
  arbitrary `B`; the main theorem instantiates `R = 𝓞 K`, `F = K`, `B = ℍ[K, a, 0, b]`.
  See `IsOrder`, `IsMaximalOrder`.
* A **maximal order** is an order not properly contained in another order — a maximal element
  of the orders under inclusion (Voight, Definition 10.4.1). See `IsMaximalOrder`.

## Main statements

Voight's Proposition 15.5.2 splits into its two halves:

* `exists_maximalOrder` — a maximal `𝓞 K`-order exists.
* `exists_maximalOrder_ge` — every `𝓞 K`-order is contained in a maximal one.
-/

open scoped NumberField Quaternion

namespace VoightMaximalOrder

/-! ### `R`-lattices -/

section RLattice

variable (R F V : Type*)
  [CommRing R] [Field F] [Algebra R F] [IsFractionRing R F]
  [AddCommGroup V] [Module R V] [Module F V] [IsScalarTower R F V]

/-- **Voight, *Quaternion Algebras*, Definition 9.3.1.**  An **`R`-lattice** in a
finite-dimensional `F`-vector space `V`, where `F = Frac R`, is a finitely generated
`R`-submodule `M ⊆ V` whose `F`-span is all of `V` (Voight writes `M F = V`; `M` is a
*full* lattice).  Voight calls a `ℤ`-lattice simply a *lattice*; over `R = ℤ` the analytic
counterpart of this predicate is Mathlib's `IsZLattice`. -/
structure IsRLattice (M : Submodule R V) : Prop where
  /-- `M` is finitely generated as an `R`-module. -/
  moduleFinite : Module.Finite R M
  /-- The `F`-span of `M` is all of `V` (`M` is *full*: `M F = V`). -/
  spans : Submodule.span F (M : Set V) = ⊤

end RLattice

/-! ### `R`-orders in an `F`-algebra -/

section Order

variable (R F B : Type*)
  [CommRing R] [Field F] [Algebra R F] [IsFractionRing R F]
  [Ring B] [Algebra R B] [Algebra F B] [IsScalarTower R F B] [FiniteDimensional F B]

/-- An **`R`-order** in a finite-dimensional `F`-algebra `B` (with `F = Frac R`), Voight's
Definition 10.2.1: an `R`-order is an `R`-lattice that is also a subring of `B`.  Since
`O : Subalgebra R B` is already a subring containing `R`, being an order is exactly that its
underlying `R`-submodule is an `R`-lattice in `B`. -/
def IsOrder (O : Subalgebra R B) : Prop :=
  IsRLattice R F B O.toSubmodule

/-- A **maximal `R`-order** in `B`: an order that is *maximal* under inclusion among orders
(Voight, Definition 10.4.1) — a maximal element of the sub-poset `IsOrder R F B` of
`Subalgebra R B`.  This is order-theoretic maximality (`Maximal`), *not* a greatest/`⊤` order:
maximal orders need not be unique.  Unfolding, `Maximal (IsOrder R F B) O` says `O` is an order
and every order `O' ⊇ O` satisfies `O' ≤ O` (equivalently `O' = O`). -/
def IsMaximalOrder (O : Subalgebra R B) : Prop :=
  Maximal (IsOrder R F B) O

end Order

/-! ### Quaternion algebras over number fields -/

variable (K : Type*) [Field K] [NumberField K] (a b : K)

/-- **Voight, *Quaternion Algebras*, Proposition 15.5.2** (number-field case), existence half.

If `a, b ∈ Kˣ` for a number field `K`, then the quaternion algebra `ℍ[K, a, 0, b]` contains a
maximal `𝓞 K`-order. -/
theorem exists_maximalOrder (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ O : Subalgebra (𝓞 K) ℍ[K, a, 0, b], IsMaximalOrder (𝓞 K) K ℍ[K, a, 0, b] O := by
  sorry

/-- **Voight, *Quaternion Algebras*, Proposition 15.5.2** (number-field case), enlargement half.

If `a, b ∈ Kˣ` for a number field `K`, then every `𝓞 K`-order in the quaternion algebra
`ℍ[K, a, 0, b]` is contained in a maximal `𝓞 K`-order. -/
theorem exists_maximalOrder_ge (ha : a ≠ 0) (hb : b ≠ 0)
    (O : Subalgebra (𝓞 K) ℍ[K, a, 0, b]) (hO : IsOrder (𝓞 K) K ℍ[K, a, 0, b] O) :
    ∃ O' : Subalgebra (𝓞 K) ℍ[K, a, 0, b],
      IsMaximalOrder (𝓞 K) K ℍ[K, a, 0, b] O' ∧ O ≤ O' := by
  sorry

end VoightMaximalOrder
