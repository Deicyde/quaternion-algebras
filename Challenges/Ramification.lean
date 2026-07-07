import Mathlib
import Challenges.QuaternionCSA
-- Challenge file for Voight, *Quaternion Algebras* (GTM 288), Proposition 27.5.15.
-- The quaternion central-simple / Brauer-group prerequisites live in
-- `Challenges/QuaternionCSA.lean`; this file states the theorem (ending in `sorry`).
-- Machine-elaborated clean against toolchain `leanprover/lean4:v4.32.0-rc1` /
-- Mathlib master `d255f67ec8` (only the expected `declaration uses 'sorry'` warning).

/-!
# Challenge: prescribing the ramification set of a quaternion algebra

A formalization target from John Voight, *Quaternion Algebras* (GTM 288, 2021;
open-access edition at https://quatalg.org).

> **Proposition 27.5.15** (existence half of Main Theorem 14.6.1).
> *Let `K` be a number field and let `S ⊆ Pl K` be a finite set of noncomplex places
> of even cardinality. Then there exists a quaternion algebra `B` over `K` with `Ram B = S`.*

## Modeling choices

* A **place** of `K` is either an infinite (archimedean) place, `InfinitePlace K`, or a finite
  place — a nonzero prime of `𝓞 K`, encoded by `IsDedekindDomain.HeightOneSpectrum (𝓞 K)`.
  See `Place`.  A place is **complex** iff it is a complex infinite place; all finite and all real
  infinite places are *noncomplex*.  See `Place.IsComplex`.
* The quaternion algebra is the concrete `(a, b | K) = ℍ[K, a, 0, b]` with `a, b ∈ Kˣ`; over a
  char-`0` field every quaternion algebra is of this form, so quantifying over `a b : K` with
  `a ≠ 0`, `b ≠ 0` is faithful.
* `B` is **split** at `v` iff the base change to the completion `K_v` has **trivial Brauer class**
  (`= 1 = ⟦K_v⟧`); see `IsSplitField` in `Challenges/QuaternionCSA.lean`, applied here via
  `IsSplitAt`.  `B` is **ramified** at `v` iff it is *not split* there (Voight, Def 14.5.1: `B_v`
  is a division ring); see `IsRamifiedAt`.

## Main statement

* `exists_quaternionAlgebra_ramificationSet_eq` — Voight's Proposition 27.5.15.
-/

open NumberField IsDedekindDomain
open scoped NumberField

namespace VoightRamification

variable (K : Type*) [Field K] [NumberField K]

/-- A **place** of the number field `K`: an infinite (archimedean) place, or a finite place
(a nonzero prime of `𝓞 K`). -/
abbrev Place := InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K)

/-- A place is **complex** when it is a complex infinite place; finite and real infinite places
are the *noncomplex* places. -/
def Place.IsComplex : Place K → Prop :=
  Sum.elim (fun v => v.IsComplex) (fun _ => False)

/-- `ℍ[K, a, 0, b]` is **split** at `v` when its base change to the completion `K_v` has trivial
Brauer class (`= 1 = ⟦K_v⟧`).  `K_v = v.Completion` (infinite) / `v.adicCompletion K` (finite);
we take the base change to be the quaternion algebra `ℍ[K_v, a, 0, b]` over the completion. -/
def IsSplitAt (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) : Place K → Prop :=
  Sum.elim
    (fun v : InfinitePlace K =>
      haveI : CharZero v.Completion :=
        charZero_of_injective_algebraMap (algebraMap K v.Completion).injective
      IsSplitField v.Completion (algebraMap K v.Completion a) (algebraMap K v.Completion b)
        (algebraMap_ne_zero_of_ne ha) (algebraMap_ne_zero_of_ne hb))
    (fun v : HeightOneSpectrum (𝓞 K) =>
      haveI : CharZero (v.adicCompletion K) :=
        charZero_of_injective_algebraMap (algebraMap K (v.adicCompletion K)).injective
      IsSplitField (v.adicCompletion K) (algebraMap K (v.adicCompletion K) a)
        (algebraMap K (v.adicCompletion K) b)
        (algebraMap_ne_zero_of_ne ha) (algebraMap_ne_zero_of_ne hb))

/-- `ℍ[K, a, 0, b]` is **ramified** at `v` iff it is **not split** at `v` (Voight, Def 14.5.1:
`B_v` is a division ring). -/
def IsRamifiedAt (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (v : Place K) : Prop :=
  ¬ IsSplitAt K a b ha hb v

/-- The **ramification set** of `ℍ[K, a, 0, b]`: the set of places at which it is ramified. -/
def RamificationSet (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) : Set (Place K) :=
  {v | IsRamifiedAt K a b ha hb v}

/-- **Voight, *Quaternion Algebras*, Proposition 27.5.15** (existence half of Main Theorem 14.6.1).

For every finite set `S` of noncomplex places of a number field `K` of even cardinality, there is
a quaternion algebra over `K` — realized as `(a, b | K) = ℍ[K, a, 0, b]` with `a, b ≠ 0` — whose
ramification set is exactly `S`. -/
theorem exists_quaternionAlgebra_ramificationSet_eq (S : Finset (Place K))
    (hnoncomplex : ∀ v ∈ S, ¬ Place.IsComplex K v) (heven : Even S.card) :
    ∃ (a b : K) (ha : a ≠ 0) (hb : b ≠ 0),
      RamificationSet K a b ha hb = (S : Set (Place K)) := by
  sorry

end VoightRamification
