import Mathlib
import QuaternionAlgebras.Chapter3.Quadratic

/-!
# Classification of division algebras of degree two (Voight, Chapter 3)

Throughout this file `char F ≠ 2` (written `(2 : F) ≠ 0`) and `B` is a division
`F`-algebra of degree `2` with `B ≠ F`.  We fix `i ∈ B \ F` with `i² = a ∈ Fˣ`, set
`K = F[i] = Algebra.adjoin F {i}`, and study the conjugation `φ(α) = i⁻¹ α i`.  The
main theorem classifies degree-two division algebras as `F`, quadratic field
extensions, or quaternion algebras.
-/

namespace QuaternionAlgebras.Chapter3

open scoped Quaternion

/-- **A commutative subring of a division ring is a field.** If `S` is a subring of a
division ring `D` that is commutative and closed under inverses, then `S` is a field. -/
theorem comm_subring_isField {D : Type*} [DivisionRing D] (S : Subring D)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x)
    (hinv : ∀ x ∈ S, x ≠ 0 → x⁻¹ ∈ S) : IsField S := by
  sorry

variable {F B : Type*} [Field F] [DivisionRing B] [Algebra F B]

/-- **A generated quadratic subalgebra is a field.** For `i ∈ B \ F` in a division
`F`-algebra of degree `2`, `K = F[i]` is a field with `dim_F K = 2`. -/
theorem quadratic_subfield (i : B) (hi : i ∉ Set.range (algebraMap F B))
    (hdeg : HasDegreeLE F B 2) :
    Module.finrank F (Algebra.adjoin F ({i} : Set B)) = 2 ∧
      IsField (Algebra.adjoin F ({i} : Set B)) := by
  sorry

/-- **Conjugation by `i` is a ring automorphism of order two.** -/
theorem conjugation_ring_auto (i : B) (hi : i ≠ 0) (a : F)
    (hi2 : i * i = algebraMap F B a) :
    ∃ φ : B ≃+* B, (∀ α, φ α = i⁻¹ * α * i) ∧ ∀ α, φ (φ α) = α := by
  sorry

/-- **Conjugation by `i` is a `K`-linear involution of order two.** Regarding `B` as a
left `K`-vector space, `φ(α) = i⁻¹ α i` commutes with left multiplication by
`K = F[i]`. -/
theorem conjugation_involution (i : B) (hi : i ≠ 0) (a : F)
    (hi2 : i * i = algebraMap F B a) :
    ∃ φ : B ≃+* B, (∀ α, φ α = i⁻¹ * α * i) ∧ (∀ α, φ (φ α) = α) ∧
      ∀ κ ∈ Algebra.adjoin F ({i} : Set B), ∀ α, φ (κ * α) = κ * φ α := by
  sorry

/-- **Complementary idempotents from the conjugation.** With `char F ≠ 2`, the
operators `e± = ½(1 ± φ)` are complementary orthogonal idempotents summing to `1`. -/
theorem conjugation_idempotents (φ : Module.End F B) (hφ : φ * φ = 1)
    (hchar : (2 : F) ≠ 0) :
    ((2 : F)⁻¹ • (1 + φ)) + ((2 : F)⁻¹ • (1 - φ)) = 1 ∧
      IsIdempotentElem ((2 : F)⁻¹ • (1 + φ)) ∧
      IsIdempotentElem ((2 : F)⁻¹ • (1 - φ)) ∧
      ((2 : F)⁻¹ • (1 + φ)) * ((2 : F)⁻¹ • (1 - φ)) = 0 ∧
      ((2 : F)⁻¹ • (1 - φ)) * ((2 : F)⁻¹ • (1 + φ)) = 0 := by
  sorry

/-- **Eigenspace decomposition of the conjugation.** With `char F ≠ 2`, `B` is the
direct sum of the `+1`- and `-1`-eigenspaces of `φ`. -/
theorem eigenspace_decomp (φ : Module.End F B) (hφ : φ * φ = 1) (hchar : (2 : F) ≠ 0) :
    IsCompl (Module.End.eigenspace φ 1) (Module.End.eigenspace φ (-1)) := by
  sorry

/-- **The fixed space is the centralizer of `i`.** An element lies in `B⁺` iff it
commutes with `i`. -/
theorem Bplus_eq_centralizer (i : B) (hi : i ≠ 0) (α : B) :
    i⁻¹ * α * i = α ↔ α * i = i * α := by
  sorry

/-- **A commuting element generates a subfield.** If `α` commutes with `i` then
`L = F[i, α]` is a field containing `K = F[i]`. -/
theorem commuting_subring_field (i α : B) (hcomm : α * i = i * α)
    (hdeg : HasDegreeLE F B 2) :
    IsField (Algebra.adjoin F ({i, α} : Set B)) ∧
      Algebra.adjoin F ({i} : Set B) ≤ Algebra.adjoin F ({i, α} : Set B) := by
  sorry

/-- **The generated field is finite and separable.** With `char F ≠ 2`, if `α`
commutes with `i` then `L = F[i, α]` is finite-dimensional and separable over `F`. -/
theorem commuting_finite_separable (hchar : (2 : F) ≠ 0) (i α : B)
    (hcomm : α * i = i * α) (hdeg : HasDegreeLE F B 2) :
    Module.Finite F (Algebra.adjoin F ({i, α} : Set B)) ∧
      Algebra.IsSeparable F (Algebra.adjoin F ({i, α} : Set B)) := by
  sorry

/-- **A commuting element lies in `K`.** With `char F ≠ 2`, if `α` commutes with `i`
then `dim_F F[i, α] = 2`, so `F[i, α] = K` and `α ∈ K`. -/
theorem commuting_quadratic_field (hchar : (2 : F) ≠ 0) (i α : B)
    (hi : i ∉ Set.range (algebraMap F B)) (hcomm : α * i = i * α)
    (hdeg : HasDegreeLE F B 2) :
    Module.finrank F (Algebra.adjoin F ({i, α} : Set B)) = 2 ∧
      α ∈ Algebra.adjoin F ({i} : Set B) := by
  sorry

/-- **The fixed space equals `K`.** `B⁺ = K`. -/
theorem Bplus_eq_K (hchar : (2 : F) ≠ 0) (i : B) (hi : i ≠ 0)
    (hi' : i ∉ Set.range (algebraMap F B)) (hdeg : HasDegreeLE F B 2) (α : B) :
    i⁻¹ * α * i = α ↔ α ∈ Algebra.adjoin F ({i} : Set B) := by
  sorry

/-- **The anti-fixed space is at most one-dimensional.** Any two nonzero elements of
`B⁻` are `K`-multiples of each other. -/
theorem Bminus_dim_one (hchar : (2 : F) ≠ 0) (i : B) (hi : i ≠ 0)
    (hi' : i ∉ Set.range (algebraMap F B)) (hdeg : HasDegreeLE F B 2) (j₁ j₂ : B)
    (h₁ : i⁻¹ * j₁ * i = -j₁) (h₂ : i⁻¹ * j₂ * i = -j₂)
    (hj₁ : j₁ ≠ 0) (hj₂ : j₂ ≠ 0) :
    ∃ κ ∈ Algebra.adjoin F ({i} : Set B), j₁ = κ * j₂ := by
  sorry

/-- **Conjugate of a standard involution is standard.** If `inv` is a standard
involution and `u` is a unit, then `α ↦ ψ⁻¹(ψ(α)‾)` (with `ψ(α) = u⁻¹ α u`) is again a
standard involution. -/
theorem conjugate_involution_standard (inv : Involution F B) (h : inv.IsStandard)
    (u : B) (hu : u ≠ 0) :
    ∃ inv' : Involution F B, inv'.IsStandard ∧
      ∀ α, inv'.toLinearMap α = u * inv.toLinearMap (u⁻¹ * α * u) * u⁻¹ := by
  sorry

/-- **Reduced trace is invariant under conjugation.** -/
theorem trd_conjugation_invariant (inv : Involution F B) (h : inv.IsStandard)
    (u : B) (hu : u ≠ 0) (α : B) :
    inv.reducedTrace h (u⁻¹ * α * u) = inv.reducedTrace h α := by
  sorry

/-- **An anti-fixed element has reduced trace zero.** If `j ∈ B⁻` then `trd(j) = 0`
and hence `j² = -nrd(j) ∈ F`. -/
theorem Bminus_trace_zero (hchar : (2 : F) ≠ 0) (inv : Involution F B)
    (h : inv.IsStandard) (i j : B) (hi : i ≠ 0) (hj : i⁻¹ * j * i = -j) :
    inv.reducedTrace h j = 0 ∧ j ^ 2 = -algebraMap F B (inv.reducedNorm h j) := by
  sorry

/-- **Decomposition `B = K ⊕ Kj`.** If `B⁻ ≠ 0`, fix `0 ≠ j ∈ B⁻`; then
`1, i, j, ij` is an `F`-basis of `B`. -/
theorem B_decomp_K_Kj (hchar : (2 : F) ≠ 0) (i : B)
    (hi : i ∉ Set.range (algebraMap F B)) (a : F) (hi2 : i * i = algebraMap F B a)
    (hdeg : HasDegreeLE F B 2) (j : B) (hj : j ≠ 0) (hjm : i⁻¹ * j * i = -j) :
    ∃ b : Module.Basis (Fin 4) F B, b 0 = 1 ∧ b 1 = i ∧ b 2 = j ∧ b 3 = i * j := by
  sorry

/-- **Quaternion multiplication relations.** With `i² = a ∈ Fˣ`, we have `ji = -ij`
and `j² = b ∈ Fˣ`. -/
theorem quaternion_relations (hchar : (2 : F) ≠ 0) (i : B)
    (hi' : i ∉ Set.range (algebraMap F B)) (a : F) (ha : a ≠ 0)
    (hi2 : i * i = algebraMap F B a) (hdeg : HasDegreeLE F B 2) (j : B) (hj : j ≠ 0)
    (hjm : i⁻¹ * j * i = -j) :
    j * i = -(i * j) ∧ ∃ b : F, b ≠ 0 ∧ j * j = algebraMap F B b := by
  sorry

/-- **The quaternion lift homomorphism.** From the relations `i² = a`, `j² = b`,
`ij = -ji`, `QuaternionAlgebra.Basis.liftHom` yields an `F`-algebra homomorphism
`ℍ[F,a,0,b] → B` sending the standard generators to `i, j, ij`. -/
theorem quaternion_lift_hom (a b : F) (i j : B) (hi2 : i * i = algebraMap F B a)
    (hj2 : j * j = algebraMap F B b) (hij : i * j = -(j * i)) :
    ∃ Φ : ℍ[F, a, 0, b] →ₐ[F] B,
      Φ (QuaternionAlgebras.gi a b) = i ∧ Φ (QuaternionAlgebras.gj a b) = j ∧
        Φ (QuaternionAlgebras.gk a b) = i * j := by
  sorry

/-- **Construction of the quaternion isomorphism.** Under the relations, the lift `Φ`
is an `F`-algebra isomorphism `ℍ[F,a,0,b] ≃ₐ[F] B`. -/
theorem build_quaternion_iso (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) (hchar : (2 : F) ≠ 0)
    (i j : B) (hi0 : i ≠ 0) (hj0 : j ≠ 0) (hi2 : i * i = algebraMap F B a)
    (hj2 : j * j = algebraMap F B b) (hij : i * j = -(j * i))
    (hgen : Algebra.adjoin F ({i, j} : Set B) = ⊤) :
    ∃ Φ : ℍ[F, a, 0, b] ≃ₐ[F] B,
      Φ (QuaternionAlgebras.gi a b) = i ∧ Φ (QuaternionAlgebras.gj a b) = j ∧
        Φ (QuaternionAlgebras.gk a b) = i * j := by
  sorry

/-- **Each classification case has degree at most two.** -/
theorem classification_forward (hchar : (2 : F) ≠ 0)
    (hcase : Module.finrank F B = 1 ∨ Module.finrank F B = 2 ∨
      (∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (ℍ[F, a, 0, b] ≃ₐ[F] B))) :
    HasDegreeLE F B 2 := by
  sorry

/-- **Classification of degree-two division algebras.** A division `F`-algebra
(`char F ≠ 2`) has degree at most `2` iff it is `F`, a quadratic field extension, or a
division quaternion algebra. -/
theorem degree_two_classification (hchar : (2 : F) ≠ 0) :
    HasDegreeLE F B 2 ↔
      (Function.Surjective (algebraMap F B) ∨ Module.finrank F B = 2 ∨
        (∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (ℍ[F, a, 0, b] ≃ₐ[F] B))) := by
  sorry

/-- **Degree two versus standard involution.** A division `F`-algebra (`char F ≠ 2`)
has degree at most `2` iff it has a standard involution. -/
theorem degree_two_iff_involution (hchar : (2 : F) ≠ 0) :
    HasDegreeLE F B 2 ↔ HasStandardInvolution F B := by
  sorry

/-- **Noncommutativity and center of a quaternion algebra.** For `a, b ∈ Fˣ` and
`char F ≠ 2`, `ji = -ij ≠ ij`, so `ℍ[F,a,0,b]` is noncommutative, and its center is
exactly `F`. -/
theorem quaternion_center_eq_base (a b : F) (ha : a ≠ 0) (hb : b ≠ 0)
    (hchar : (2 : F) ≠ 0) :
    QuaternionAlgebras.gj a b * QuaternionAlgebras.gi a b ≠
        QuaternionAlgebras.gi a b * QuaternionAlgebras.gj a b ∧
      ∀ z : ℍ[F, a, 0, b],
        z ∈ Set.center ℍ[F, a, 0, b] ↔ z ∈ Set.range (algebraMap F ℍ[F, a, 0, b]) := by
  sorry

/-- **Characterizations of quaternion division algebras.** For a division `F`-algebra
(`char F ≠ 2`), the following are equivalent: (i) `B` is a quaternion algebra;
(ii) `B` is noncommutative of degree `2`; (iii) `B` is central of degree `2`. -/
theorem quaternion_characterization (hchar : (2 : F) ≠ 0) :
    [ (∃ a b : F, a ≠ 0 ∧ b ≠ 0 ∧ Nonempty (ℍ[F, a, 0, b] ≃ₐ[F] B)),
      ((∃ x y : B, x * y ≠ y * x) ∧ HasDegreeLE F B 2),
      (Algebra.IsCentral F B ∧ HasDegreeLE F B 2 ∧
        ¬ Function.Surjective (algebraMap F B)) ].TFAE := by
  sorry

end QuaternionAlgebras.Chapter3
