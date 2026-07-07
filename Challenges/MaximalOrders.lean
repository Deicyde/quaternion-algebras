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
* An **`𝓞 K`-order** is a full `𝓞 K`-lattice that is a subring: an `𝓞 K`-subalgebra
  that is finitely generated as an `𝓞 K`-module and whose `K`-span is all of `ℍ[K, a, 0, b]`
  (Voight, §10.2). See `IsOrder`.
* A **maximal order** is an order not properly contained in another order
  (Voight, Definition 10.4.1). See `IsMaximalOrder`.

## Main statement

* `exists_maximalOrder_and_forall_le` — Voight's Proposition 15.5.2.
-/

open scoped NumberField Quaternion

namespace VoightMaximalOrder

variable (K : Type*) [Field K] [NumberField K] (a b : K)

/-- An **`𝓞 K`-order** in the quaternion algebra `ℍ[K, a, 0, b]`: an `𝓞 K`-subalgebra `O`
that is a *full lattice*, i.e. the `K`-span of `O` is all of `ℍ[K, a, 0, b]`.

Since `ℍ[K, a, 0, b]` is finite-dimensional over `K = Frac(𝓞 K)`, this is exactly Voight's
notion of an `R`-order (a subring that is simultaneously a full `R`-lattice). -/
structure IsOrder (O : Subalgebra (𝓞 K) ℍ[K, a, 0, b]) : Prop where
  /-- `O` spans `ℍ[K, a, 0, b]` over `K` (it is a *full* lattice). -/
  spans : Submodule.span K (O : Set ℍ[K, a, 0, b]) = ⊤

/-- A **maximal `𝓞 K`-order** in `ℍ[K, a, 0, b]`: an order that is not properly contained in
any other order (Voight, Definition 10.4.1). -/
def IsMaximalOrder (O : Subalgebra (𝓞 K) ℍ[K, a, 0, b]) : Prop :=
  IsOrder K a b O ∧
    ∀ O' : Subalgebra (𝓞 K) ℍ[K, a, 0, b], IsOrder K a b O' → O ≤ O' → O = O'

/-- **Voight, *Quaternion Algebras*, Proposition 15.5.2** (number-field case).

If `a, b ∈ Kˣ` for a number field `K`, then the quaternion algebra `ℍ[K, a, 0, b]` contains
a maximal `𝓞 K`-order, and moreover every `𝓞 K`-order in it is contained in a maximal one. -/
theorem exists_maximalOrder_and_forall_le (ha : a ≠ 0) (hb : b ≠ 0) :
    (∃ O : Subalgebra (𝓞 K) ℍ[K, a, 0, b], IsMaximalOrder K a b O) ∧
      (∀ O : Subalgebra (𝓞 K) ℍ[K, a, 0, b], IsOrder K a b O →
        ∃ O' : Subalgebra (𝓞 K) ℍ[K, a, 0, b], IsMaximalOrder K a b O' ∧ O ≤ O') := by
  sorry

end VoightMaximalOrder
