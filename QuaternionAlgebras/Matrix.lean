import QuaternionAlgebras.Beginnings

/-!
# Quaternion algebras: matrix representations

Over a splitting field `K = F(√a)` containing a root `s` of `x² - a`, the
quaternion algebra `(a,b/F)` embeds into `M₂(K)`.  When `a` is already a square
in `F` (e.g. `a = 1`) the embedding is an isomorphism onto `M₂(F)`.
-/

namespace QuaternionAlgebras

open scoped Quaternion

variable {F : Type*} [Field F] (a b : F)

/-- The matrix `I = !![s, 0; 0, -s]` over a ring `K`. -/
def matI {K : Type*} [Ring K] (s : K) : Matrix (Fin 2) (Fin 2) K :=
  !![s, 0; 0, -s]

/-- The matrix `J = !![0, b; 1, 0]` over a ring `K`. -/
def matJ {K : Type*} [Ring K] (b : K) : Matrix (Fin 2) (Fin 2) K :=
  !![0, b; 1, 0]

/-- Matrix basis relations: with `s² = a`, the matrices `I, J` satisfy
`I² = a • 1`, `J² = b • 1` and `J I = -(I J)`. -/
lemma matrix_basis_relations {K : Type*} [CommRing K] (s a b : K) (hs : s * s = a) :
    matI s * matI s = a • (1 : Matrix (Fin 2) (Fin 2) K) ∧
      matJ b * matJ b = b • (1 : Matrix (Fin 2) (Fin 2) K) ∧
      matJ b * matI s = -(matI s * matJ b) := by sorry

/-- Matrix `liftHom`: over a field extension `K/F` containing a square root `s`
of `a`, there is an `F`-algebra homomorphism `(a,b/F) → M₂(K)` sending
`i ↦ I`, `j ↦ J`, `k ↦ IJ`. -/
lemma matrix_lifthom {K : Type*} [Field K] [Algebra F K] (s : K)
    (hs : s * s = algebraMap F K a) :
    ∃ φ : ℍ[F, a, 0, b] →ₐ[F] Matrix (Fin 2) (Fin 2) K,
      φ (gi a b) = matI s ∧
      φ (gj a b) = matJ (algebraMap F K b) ∧
      φ (gk a b) = matI s * matJ (algebraMap F K b) := by sorry

/-- Matrix embedding: any `F`-algebra homomorphism `(a,b/F) → M₂(K)` sending the
standard generators to `I` and `J` is injective. -/
lemma matrix_embedding {K : Type*} [Field K] [Algebra F K] (s : K)
    (hs : s * s = algebraMap F K a)
    (φ : ℍ[F, a, 0, b] →ₐ[F] Matrix (Fin 2) (Fin 2) K)
    (h1 : φ (gi a b) = matI s) (h2 : φ (gj a b) = matJ (algebraMap F K b)) :
    Function.Injective φ := by sorry

/-- The split quaternion algebra `(1,b/F)` is isomorphic to `M₂(F)`.  In
particular `(1,1/F) ≅ M₂(F)`. -/
theorem split_matrix (b : F) :
    Nonempty (ℍ[F, 1, 0, b] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) := by sorry

end QuaternionAlgebras
