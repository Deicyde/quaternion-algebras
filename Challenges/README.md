# Voight quaternion-algebra challenge files

Buzzard-style **challenge files** (autoformalization targets: `import Mathlib`, define
every prerequisite, state the theorem ending in `sorry`) for two results from
**John Voight, *Quaternion Algebras*** (GTM 288). They depend only on Mathlib, not on the
surrounding `QuaternionAlgebras` library.

- `MaximalOrders.lean` — single self-contained file (imports only Mathlib).
- `Ramification.lean` — the statement + core defs, with the central-simple / Brauer-group
  prerequisites (the quaternion-CSA facts Mathlib lacks) factored into `QuaternionCSA.lean`.
  `Ramification.lean` imports `Challenges.QuaternionCSA`, so this challenge spans two files.

## Building

Compile only inside this project (Mathlib is prebuilt here). The theorems carry a deliberate
`sorry`, so the `Challenges` library is kept out of `defaultTargets`; build explicitly:

```bash
lake build Challenges.MaximalOrders   # self-contained; also works via `lake env lean`
lake build Challenges.Ramification    # builds Challenges.QuaternionCSA (prerequisites) first
```

Because `Ramification.lean` imports `Challenges.QuaternionCSA`, build it with `lake build` (which
resolves the import) rather than `lake env lean`. Each elaborates **clean** — the only output is
the expected `declaration uses 'sorry'` warning at the theorem — against toolchain
`leanprover/lean4:v4.32.0-rc1` / Mathlib master `d255f67ec8`. (`QuaternionCSA.lean` itself builds
fully clean; its two proofs are `sorry`-free.)

## The two targets

### `MaximalOrders.lean` — Proposition 15.5.2 (p. 240, ch. "Discriminants")
> *There exists a maximal `R`-order `O ⊆ B`, and every order `O` is contained in a maximal
> `R`-order `O′ ⊆ B`* — for `R` a Dedekind domain, `F = Frac R`, `B` a quaternion algebra.
> Here specialized to `R = 𝓞 K`, `F = K` (the number-field case). Soft existence also at
> para 10.4.2 (p. 155, Zorn + Noetherian).

Modeling (as shipped):
- The quaternion algebra is the **concrete** `ℍ[K, a, 0, b]` (Voight's `(a, b ∣ K)`) with
  `a, b ∈ Kˣ`; over char-0 `K` every quaternion algebra is of this form, so quantifying over
  `a b : K` with `a ≠ 0, b ≠ 0` is faithful. This makes `Algebra (𝓞 K) ℍ[K,a,0,b]` and
  `IsScalarTower (𝓞 K) K ℍ[K,a,0,b]` genuine instances (`Mathlib/Algebra/Quaternion.lean`),
  so no algebra/scalar-tower structure is assumed. (An earlier abstract-CSA formulation via a
  bespoke `IsQuaternionAlgebra` predicate was dropped in favor of this.)
- `IsOrder O` (`O : Subalgebra (𝓞 K) ℍ[K,a,0,b]`) := `Module.Finite (𝓞 K) O` ∧
  `Submodule.span K (O : Set _) = ⊤` (a full `𝓞 K`-lattice that is a subring).
- `IsMaximalOrder O` := `IsOrder O` ∧ maximal under `≤`.
- Statement: `exists_maximalOrder_and_forall_le`.

### `Ramification.lean` — Proposition 27.5.15 (p. 456, ch. "Adelic framework")
> *Let `Σ ⊆ Pl F` be a finite subset of noncomplex places of `F` of even cardinality. Then
> there exists a quaternion algebra `B` over `F` with `Ram B = Σ`* — the existence half of
> Main Theorem 14.6.1 (p. 223, the bijection `B ↦ Ram B`). Proof uses class field theory +
> the Hasse norm theorem. Over **ℚ** the easier analogue is **Proposition 14.2.7** (p. 213),
> proved via Dirichlet's theorem on primes in arithmetic progressions — a much more
> self-contained target if the number-field case proves too heavy.

Modeling:
- `Place K := InfinitePlace K ⊕ IsDedekindDomain.HeightOneSpectrum (𝓞 K)` (infinite ⊕ finite).
- `Place.IsComplex := Sum.elim (·.IsComplex) (fun _ => False)`.
- **Split via the Brauer group.** `IsSplitField F a b := ⟦quatCSA⟧ = ⟦trivCSA⟧` in `BrauerGroup F`
  — the class of `ℍ[F,a,0,b]` equals `1 = ⟦F⟧`, the class of the trivial (split) algebra. To place
  `ℍ[F,a,0,b]` in `BrauerGroup F` we prove it is a central simple algebra: `quatCentral`
  (`Algebra.IsCentral`) and `quatSimple` (`IsSimpleRing`, via a reduced-trace averaging argument) —
  neither is in Mathlib, so both are proved in-file (genuine, axiom-clean). Mathlib's `BrauerGroup`
  is only a `Quotient` (no group instance / no literal `1`), so `1` is spelled as `⟦F⟧`.
- `IsSplitAt a b ha hb v` applies `IsSplitField` to the completion `K_v` (`= v.Completion` /
  `v.adicCompletion K`), base-changing `a,b` via `algebraMap`; `CharZero K_v` is derived from
  `CharZero K` along the injective `algebraMap`.
- `IsRamifiedAt a b ha hb v := ¬ IsSplitAt …` (Voight Def 14.5.1); `RamificationSet a b ha hb :=
  {v | IsRamifiedAt …}`. The `a ≠ 0`, `b ≠ 0` hypotheses are threaded through (needed to form the CSA).
- Statement `exists_quaternionAlgebra_ramificationSet_eq`: for `S : Finset (Place K)`, all places
  noncomplex and `Even S.card`, `∃ a b (ha : a ≠ 0) (hb : b ≠ 0), RamificationSet K a b ha hb = ↑S`.

## Source

Voight, *Quaternion Algebras*, open-access edition v1.0.6u (6 Oct 2025), 883 pp. Page numbers
above are for that edition (they differ slightly from the printed Springer edition).

## Next steps

- Discharge the `sorry`s. MaximalOrders is the more tractable (Zorn over the poset of orders +
  a Noetherian boundedness argument); Ramification needs class field theory not yet usable in
  Mathlib — the ℚ-only Prop 14.2.7 (Dirichlet) is the realistic proof target there.
- Cross-reference the `quaternion-algebras` blueprint under `numina/`.
