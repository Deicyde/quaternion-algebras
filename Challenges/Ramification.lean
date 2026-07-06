import Mathlib
-- Self-contained challenge file: imports **only** Mathlib and defines every
-- prerequisite below.  Written against Mathlib master (commit d255f67ec8,
-- toolchain `leanprover/lean4:v4.32.0-rc1`), the checkout used by the
-- `quaternion-algebras` project.  The final statement ends in `sorry`.
--
-- NOTE: this file was authored by reading the Mathlib sources directly; it was
-- not machine-elaborated in the authoring session, so minor name/universe
-- adjustments may be needed.

/-!
# Challenge: prescribing the ramification set of a quaternion algebra

A formalization target from John Voight, *Quaternion Algebras* (GTM 288, 2021;
open-access edition at https://quatalg.org).

> **Proposition 27.5.15** (equivalently, the existence half of Main Theorem 14.6.1).
> *Let `K` be a number field and let `S ⊆ Pl K` be a finite set of noncomplex places
> of even cardinality. Then there exists a quaternion algebra `B` over `K` with
> `Ram B = S`.*

## Modeling choices

* A **place** of `K` is either an infinite (archimedean) place, `InfinitePlace K`, or a
  finite place — a nonzero prime of the ring of integers, encoded by
  `IsDedekindDomain.HeightOneSpectrum (𝓞 K)`.  See `Place`.
* The **completion** `K_v` is `v.Completion` for an infinite place and `v.adicCompletion K`
  for a finite place.
* A place is **complex** iff it is a complex infinite place; all finite places and all
  real infinite places are *noncomplex*.  See `Place.IsComplex`.
* A quaternion algebra `B` is **ramified** at `v` iff it is *not split* there, i.e. there
  is no `K_v`-algebra isomorphism `K_v ⊗[K] B ≃ₐ[K_v] M₂(K_v)`.  See `RamifiedAt`.
  (For complex places this can never happen, matching "noncomplex".)
* Every quaternion algebra over a number field `K` (which has characteristic `0`) is
  isomorphic to `(a, b | K) = ℍ[K, a, 0, b]` for some `a, b ∈ Kˣ`, so we quantify
  existentially over the parameters `a b : K` with `a ≠ 0`, `b ≠ 0`.

## Main statement

* `exists_quaternionAlgebra_ramificationSet_eq` — Voight's Proposition 27.5.15.
-/

open NumberField IsDedekindDomain
open scoped NumberField Quaternion TensorProduct

namespace VoightRamification

variable (K : Type*) [Field K] [NumberField K]

/-- A **place** of the number field `K`: either an infinite (archimedean) place, or a
finite place given by a nonzero prime of the ring of integers `𝓞 K`. -/
abbrev Place : Type _ :=
  InfinitePlace K ⊕ HeightOneSpectrum (𝓞 K)

/-- A place is **complex** when it is a complex infinite place.  Finite places and real
infinite places are the *noncomplex* places (Voight's `Ram B` consists of noncomplex
places). -/
def Place.IsComplex : Place K → Prop :=
  Sum.elim (fun v => v.IsComplex) (fun _ => False)

/-- The quaternion algebra `(a, b | K) = ℍ[K, a, 0, b]` is **ramified** at a place `v`
iff it is *not split* at `v`: there is no `K_v`-algebra isomorphism from the base change
`K_v ⊗[K] ℍ[K, a, 0, b]` to the `2 × 2` matrix algebra `M₂(K_v)`.  Here `K_v` is the
completion of `K` at `v` (`v.Completion` for infinite `v`, `v.adicCompletion K` for finite
`v`), and "not split" is expressed as emptiness of the type of such isomorphisms. -/
def RamifiedAt (a b : K) : Place K → Prop :=
  Sum.elim
    (fun v : InfinitePlace K =>
      IsEmpty (v.Completion ⊗[K] ℍ[K, a, 0, b] ≃ₐ[v.Completion]
        Matrix (Fin 2) (Fin 2) v.Completion))
    (fun v : HeightOneSpectrum (𝓞 K) =>
      IsEmpty (v.adicCompletion K ⊗[K] ℍ[K, a, 0, b] ≃ₐ[v.adicCompletion K]
        Matrix (Fin 2) (Fin 2) (v.adicCompletion K)))

/-- The **ramification set** `Ram (a, b | K)` of the quaternion algebra `ℍ[K, a, 0, b]`:
the set of places at which it is ramified (equivalently, not split). -/
def RamificationSet (a b : K) : Set (Place K) :=
  {v | RamifiedAt K a b v}

/-- **Voight, *Quaternion Algebras*, Proposition 27.5.15** (existence half of Main
Theorem 14.6.1).

For every finite set `S` of noncomplex places of a number field `K` of even cardinality,
there is a quaternion algebra over `K` — realized as `(a, b | K) = ℍ[K, a, 0, b]` with
`a, b ≠ 0` — whose ramification set is exactly `S`. -/
theorem exists_quaternionAlgebra_ramificationSet_eq
    (S : Finset (Place K))
    (hnoncomplex : ∀ v ∈ S, ¬ Place.IsComplex K v)
    (heven : Even S.card) :
    ∃ a b : K, a ≠ 0 ∧ b ≠ 0 ∧ RamificationSet K a b = (S : Set (Place K)) := by
  sorry

end VoightRamification
