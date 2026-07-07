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
* An **`𝓞 K`-order** is an `𝓞 K`-lattice that is also a subring (Voight, Definition 10.2.1):
  an `𝓞 K`-subalgebra of `ℍ[K, a, 0, b]` whose underlying `𝓞 K`-submodule is an `𝓞 K`-lattice.
  See `IsOrder`.
* A **maximal order** is an order not properly contained in another order
  (Voight, Definition 10.4.1). See `IsMaximalOrder`.

## Main statement

* `exists_maximalOrder_and_forall_le` — Voight's Proposition 15.5.2.
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

variable (K : Type*) [Field K] [NumberField K] (a b : K)

/-- An **`𝓞 K`-order** in the quaternion algebra `ℍ[K, a, 0, b]` (Voight, Definition 10.2.1):
an `𝓞 K`-order is an `𝓞 K`-*lattice* that is also a subring, taken with `R = 𝓞 K`, `F = K`,
`V = ℍ[K, a, 0, b]`.  Since `O : Subalgebra (𝓞 K) ℍ[K, a, 0, b]` is already a subring containing
`𝓞 K`, being an order is exactly that its underlying `𝓞 K`-submodule is an `𝓞 K`-lattice in
`ℍ[K, a, 0, b]` (which is finite-dimensional over `K = Frac(𝓞 K)`). -/
def IsOrder (O : Subalgebra (𝓞 K) ℍ[K, a, 0, b]) : Prop :=
  IsRLattice (𝓞 K) K ℍ[K, a, 0, b] O.toSubmodule

/-- A **maximal `𝓞 K`-order** in `ℍ[K, a, 0, b]`: an order that is *maximal* under inclusion
among orders (Voight, Definition 10.4.1) — a maximal element of the sub-poset `IsOrder K a b`
of `Subalgebra (𝓞 K) ℍ[K, a, 0, b]`.  This is order-theoretic maximality (`Maximal`), *not* a
greatest/`⊤` order: maximal orders need not be unique.  Unfolding, `Maximal (IsOrder K a b) O`
says `O` is an order and every order `O' ⊇ O` satisfies `O' ≤ O` (equivalently `O' = O`). -/
def IsMaximalOrder (O : Subalgebra (𝓞 K) ℍ[K, a, 0, b]) : Prop :=
  Maximal (IsOrder K a b) O

/-- **Voight, *Quaternion Algebras*, Proposition 15.5.2** (number-field case).

If `a, b ∈ Kˣ` for a number field `K`, then the quaternion algebra `ℍ[K, a, 0, b]` contains
a maximal `𝓞 K`-order, and moreover every `𝓞 K`-order in it is contained in a maximal one. -/
theorem exists_maximalOrder_and_forall_le (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ O : Subalgebra (𝓞 K) ℍ[K, a, 0, b], IsMaximalOrder K a b O) ∧
      (∀ O : Subalgebra (𝓞 K) ℍ[K, a, 0, b], IsOrder K a b O →
        ∃ O' : Subalgebra (𝓞 K) ℍ[K, a, 0, b], IsMaximalOrder K a b O' ∧ O ≤ O') := by
  sorry

end VoightMaximalOrder
