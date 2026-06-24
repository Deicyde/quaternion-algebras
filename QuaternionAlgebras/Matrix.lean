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
      matJ b * matI s = -(matI s * matJ b) := by
  have hI : matI s * matI s = a • (1 : Matrix (Fin 2) (Fin 2) K) := by
    calc
      matI s * matI s = !![s, 0; 0, -s] * !![s, 0; 0, -s] := rfl
      _ = !![s*s + 0*0, s*0 + 0*(-s); 0*s + (-s)*0, 0*0 + (-s)*(-s)] := by
        rw [Matrix.mul_fin_two]
      _ = !![s*s, 0; 0, s*s] := by
        simp
      _ = !![a, 0; 0, a] := by rw [hs]
      _ = a • !![1, 0; 0, 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp
      _ = a • (1 : Matrix (Fin 2) (Fin 2) K) := by rw [Matrix.one_fin_two]
  have hJ : matJ b * matJ b = b • (1 : Matrix (Fin 2) (Fin 2) K) := by
    calc
      matJ b * matJ b = !![0, b; 1, 0] * !![0, b; 1, 0] := rfl
      _ = !![0*0 + b*1, 0*b + b*0; 1*0 + 0*1, 1*b + 0*0] := by
        rw [Matrix.mul_fin_two]
      _ = !![b, 0; 0, b] := by
        simp
      _ = b • !![1, 0; 0, 1] := by
        ext i j; fin_cases i <;> fin_cases j <;> simp
      _ = b • (1 : Matrix (Fin 2) (Fin 2) K) := by rw [Matrix.one_fin_two]
  have hJI : matJ b * matI s = -(matI s * matJ b) := by
    calc
      matJ b * matI s = !![0, b; 1, 0] * !![s, 0; 0, -s] := rfl
      _ = !![0*s + b*0, 0*0 + b*(-s); 1*s + 0*0, 1*0 + 0*(-s)] := by
        rw [Matrix.mul_fin_two]
      _ = !![0, -(b * s); s, 0] := by
        simp
      _ = -(!![0, s*b; -s, 0]) := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [mul_comm b s]
      _ = -(!![s, 0; 0, -s] * !![0, b; 1, 0]) := by
        rw [Matrix.mul_fin_two]
        simp
      _ = -(matI s * matJ b) := rfl
  exact ⟨hI, hJ, hJI⟩

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
