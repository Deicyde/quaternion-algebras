import Mathlib

open QuaternionAlgebra
open scoped Quaternion

/-!
# Quaternion algebras over a field are central simple; the Brauer-group "split" predicate

General-purpose prerequisites for `Challenges/Ramification.lean` (Voight, *Quaternion Algebras*,
Prop 27.5.15).  Mathlib does not yet record that a quaternion algebra `(a,b | F) = ℍ[F,a,0,b]`
(`a,b ≠ 0`, `char F = 0`) is a central simple algebra, so we prove it here and use it to place
`ℍ[F,a,0,b]` in Mathlib's `BrauerGroup`:

* `quatCentral` — `ℍ[F,a,0,b]` is central (needs only `a ≠ 0`).
* `quatSimple`  — `ℍ[F,a,0,b]` is a simple ring (`a,b ≠ 0`), via a reduced-trace averaging argument.
* `quatCSA` / `trivCSA` — `ℍ[F,a,0,b]` and `F` packaged as `CSA F`.
* `IsSplitField` — `ℍ[F,a,0,b]` has trivial Brauer class (`= 1 = ⟦F⟧`).

`quatCentral` and `quatSimple` are candidates for upstreaming to Mathlib.
-/

/-- `ℍ[F,a,0,b]` over a field `F` of characteristic `0`, with `a ≠ 0`, is **central**
(centrality does not need `b ≠ 0`; simplicity does). -/
theorem quatCentral {F : Type*} [Field F] [CharZero F] {a b : F} (ha : a ≠ 0) :
    Algebra.IsCentral F ℍ[F, a, 0, b] := by
  refine ⟨fun z hz => ?_⟩
  rw [Subalgebra.mem_center_iff] at hz
  have hi := hz ⟨0, 1, 0, 0⟩
  have hj := hz ⟨0, 0, 1, 0⟩
  obtain ⟨t, x, y, w⟩ := z
  rw [QuaternionAlgebra.ext_iff] at hi hj
  simp only [QuaternionAlgebra.mk_mul_mk] at hi hj
  obtain ⟨_, _, hiJ, hiK⟩ := hi
  obtain ⟨_, _, _, hjK⟩ := hj
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  have hw : w = 0 := by
    have h : a * (2 * w) = 0 := by linear_combination hiJ
    have h2w : (2 : F) * w = 0 := (mul_eq_zero.1 h).resolve_left ha
    exact (mul_eq_zero.1 h2w).resolve_left h2
  have hy : y = 0 := by
    have h : (2 : F) * y = 0 := by linear_combination hiK
    exact (mul_eq_zero.1 h).resolve_left h2
  have hx : x = 0 := by
    have h : (2 : F) * x = 0 := by linear_combination -hjK
    exact (mul_eq_zero.1 h).resolve_left h2
  subst hw hy hx
  rw [Algebra.mem_bot]
  exact ⟨t, by rw [QuaternionAlgebra.algebraMap_eq]⟩

namespace QuatSimple

variable {F : Type*} [Field F] {a b : F}

/-- The imaginary units `i, j, k` of `ℍ[F,a,0,b]`. -/
def qi (a b : F) : ℍ[F, a, 0, b] := ⟨0, 1, 0, 0⟩
def qj (a b : F) : ℍ[F, a, 0, b] := ⟨0, 0, 1, 0⟩
def qk (a b : F) : ℍ[F, a, 0, b] := ⟨0, 0, 0, 1⟩

theorem re_qi_mul (z : ℍ[F, a, 0, b]) : (qi a b * z).re = a * z.imI := by
  simp [qi, re_mul]
theorem re_qj_mul (z : ℍ[F, a, 0, b]) : (qj a b * z).re = b * z.imJ := by
  simp [qj, re_mul]
theorem re_qk_mul (z : ℍ[F, a, 0, b]) : (qk a b * z).re = -(a * b) * z.imK := by
  simp only [qk, re_mul]; ring

/-- Reduced-trace ("averaging") identity: conjugating `z` by `i, j, k` (each divided by its
square, so only `F`-scalar inverses are used and every term stays in a two-sided ideal) and
summing isolates `4 · z.re`. -/
theorem avg_eq (z : ℍ[F, a, 0, b]) (ha : a ≠ 0) (hb : b ≠ 0) :
    z + qi a b * z * (a⁻¹ • qi a b) + qj a b * z * (b⁻¹ • qj a b)
      + qk a b * z * ((-(a * b))⁻¹ • qk a b) = ((4 * z.re : F) : ℍ[F, a, 0, b]) := by
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  ext <;> simp [qi, qj, qk] <;> field_simp <;> ring

/-- A two-sided ideal containing an element of nonzero real part contains `1`. -/
theorem one_mem_of_re_ne [CharZero F] (I : TwoSidedIdeal ℍ[F, a, 0, b]) (ha : a ≠ 0) (hb : b ≠ 0)
    {w : ℍ[F, a, 0, b]} (hwI : w ∈ I) (hw : w.re ≠ 0) : (1 : ℍ[F, a, 0, b]) ∈ I := by
  have hmem : ((4 * w.re : F) : ℍ[F, a, 0, b]) ∈ I := by
    rw [← avg_eq w ha hb]
    refine I.add_mem (I.add_mem (I.add_mem hwI ?_) ?_) ?_
    · exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hwI)
    · exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hwI)
    · exact I.mul_mem_right _ _ (I.mul_mem_left _ _ hwI)
  have h4 : (4 * w.re : F) ≠ 0 := mul_ne_zero (by norm_num) hw
  have hone : (((4 * w.re : F)⁻¹ : F) : ℍ[F, a, 0, b]) * ((4 * w.re : F) : ℍ[F, a, 0, b]) ∈ I :=
    I.mul_mem_left _ _ hmem
  rwa [← coe_mul, inv_mul_cancel₀ h4, coe_one] at hone

end QuatSimple

open QuatSimple in
/-- `ℍ[F,a,0,b]` over a field `F` of characteristic `0`, with `a,b ≠ 0`, is a **simple ring**. -/
theorem quatSimple {F : Type*} [Field F] [CharZero F] {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    IsSimpleRing ℍ[F, a, 0, b] := by
  apply IsSimpleRing.of_eq_bot_or_eq_top
  intro I
  rw [or_iff_not_imp_left, ← TwoSidedIdeal.one_mem_iff]
  intro hI
  obtain ⟨z, hzI, hz⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr hI : ⊥ < I)
  have hz0 : z ≠ 0 := by simpa using hz
  by_cases hzre : z.re ≠ 0
  · exact one_mem_of_re_ne I ha hb hzI hzre
  rw [not_ne_iff] at hzre
  by_cases hi : z.imI ≠ 0
  · refine one_mem_of_re_ne I ha hb (I.mul_mem_left (qi a b) _ hzI) ?_
    rw [re_qi_mul]; exact mul_ne_zero ha hi
  rw [not_ne_iff] at hi
  by_cases hj : z.imJ ≠ 0
  · refine one_mem_of_re_ne I ha hb (I.mul_mem_left (qj a b) _ hzI) ?_
    rw [re_qj_mul]; exact mul_ne_zero hb hj
  rw [not_ne_iff] at hj
  by_cases hk : z.imK ≠ 0
  · refine one_mem_of_re_ne I ha hb (I.mul_mem_left (qk a b) _ hzI) ?_
    rw [re_qk_mul]; exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero ha hb)) hk
  rw [not_ne_iff] at hk
  exact absurd (QuaternionAlgebra.ext hzre hi hj hk) hz0

/-- `ℍ[F,a,0,b]` (a,b ≠ 0, char 0) packaged as a central simple algebra over `F`. -/
noncomputable def quatCSA {F : Type*} [Field F] [CharZero F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    CSA F where
  toAlgCat := AlgCat.of F ℍ[F, a, 0, b]
  isCentral := quatCentral ha
  isSimple := quatSimple ha hb
  fin_dim := inferInstanceAs (FiniteDimensional F ℍ[F, a, 0, b])

/-- The trivial (split) central simple algebra over `F`: the field `F` itself.  Its Brauer class
is the identity `1` of `BrauerGroup F`. -/
noncomputable def trivCSA (F : Type*) [Field F] : CSA F where
  toAlgCat := AlgCat.of F F

/-- `ℍ[F,a,0,b]` is **split** over `F` iff its Brauer class is trivial — i.e. equal to
`1 = ⟦F⟧`, the class of the trivial algebra in `BrauerGroup F`. -/
def IsSplitField (F : Type*) [Field F] [CharZero F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) : Prop :=
  Quotient.mk (Brauer.CSA_Setoid F) (quatCSA a b ha hb) =
    Quotient.mk (Brauer.CSA_Setoid F) (trivCSA F)

/-- The image of a nonzero scalar under `algebraMap K F` (for a field extension `F`) is nonzero. -/
theorem algebraMap_ne_zero_of_ne {K F : Type*} [Field K] [Field F] [Algebra K F] {c : K}
    (hc : c ≠ 0) : algebraMap K F c ≠ 0 := by
  simpa only [map_zero] using (algebraMap K F).injective.ne hc
