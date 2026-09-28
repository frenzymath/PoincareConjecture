import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLBoundary
import PoincareConjecture.Proofs.M76.Mathlib.UniformPolygonSimplicity










set_option autoImplicit false

open Set

namespace Polygon



noncomputable def uniformEdgeParameters (m : ℕ) (i : Fin (m + 2)) : ℝ :=
  (i : ℝ) / (m + 1 : ℝ)



theorem strictMono_uniformEdgeParameters (m : ℕ) :
    StrictMono (uniformEdgeParameters m) := by
  intro i j hij
  exact (div_lt_div_iff_of_pos_right (by positivity : (0 : ℝ) < m + 1)).mpr
    (by exact_mod_cast hij)



theorem uniformEdgeParameters_zero (m : ℕ) : uniformEdgeParameters m 0 = 0 := by
  simp [uniformEdgeParameters]



theorem uniformEdgeParameters_last (m : ℕ) :
    uniformEdgeParameters m (Fin.last (m + 1)) = 1 := by
  simp [uniformEdgeParameters, Nat.cast_add, Nat.cast_one, show (m + 1 : ℝ) ≠ 0 by positivity]

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



theorem subdivide_uniform_zero {n : ℕ} (P : Polygon E (n + 3)) (m : ℕ) :
    P.subdivide (uniformEdgeParameters m) 0 = P 0 := by
  rw [show (0 : Fin ((n + 3) * (m + 1))) =
    finProdFinEquiv ((0 : Fin (n + 3)), (0 : Fin (m + 1))) by
      apply Fin.ext
      simp only [Fin.val_zero, finProdFinEquiv_apply_val, mul_zero, zero_add]]
  rw [P.subdivide_apply]
  simp [uniformEdgeParameters]




theorem exists_finitePL_boundary_edge_coordinates_of_size_eq
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n m : ℕ}
    (P : Polygon E n) (Q : Polygon F m) (hsize : n = m) (hn : 3 ≤ n)
    (hP : P.HasSimplicialEdges) (hQ : Q.HasSimplicialEdges)
    (hinjP : Function.Injective P) (hinjQ : Function.Injective Q) :
    ∃ e : P.boundary ℝ ≃ₜ Q.boundary ℝ, e.IsFinitePL ∧
      ∀ (i : Fin n) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1)
        (hx : AffineMap.lineMap (P i) (P (finRotate n i)) t ∈ P.boundary ℝ),
        (e ⟨AffineMap.lineMap (P i) (P (finRotate n i)) t, hx⟩ : F) =
          AffineMap.lineMap (Q (Fin.cast hsize i))
            (Q (finRotate m (Fin.cast hsize i))) t := by
  subst m
  obtain ⟨k, hk⟩ : ∃ k : ℕ, n = k + 3 := ⟨n - 3, (Nat.sub_add_cancel hn).symm⟩
  subst n
  exact P.exists_finitePL_boundary_edge_coordinates Q hP hQ hinjP hinjQ

end Polygon
