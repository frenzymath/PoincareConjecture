import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Curvature.JetBounds








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.SpacetimeBounds

open CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem exists_uniform_coordinate_curvature_jet_bound
    (n q l : ℕ) (c : ℝ) (hc : 0 ≤ c) (K B : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g)
        (b : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
        (x : EuclideanSpace ℝ (Fin n)),
        (∀ v, g.tangentNorm x v ≤ c * ‖v‖) →
        (∀ s ≤ l + q, D.curvatureDerivativeNorm s x ≤ K s) →
        (∀ j < q, ∀ i a u, ‖iteratedFDeriv ℝ j
          (fun y => b.repr (christoffelBilinear g.euclideanCoefficients y u (b i)) a) x‖ ≤
            B j * ‖u‖) →
        ∀ j ≤ q, ∀ J : Fin (4 + l) → Fin n,
          ‖iteratedFDeriv ℝ j (coordinateCurvatureComponent D l (fun i => b (J i))) x‖ ≤ C := by
  induction q generalizing l with
  | zero =>
      refine ⟨K l * c ^ (4 + l), mul_nonneg (hK l) (pow_nonneg hc _), ?_⟩
      intro g D b x hmetric hcurv _ j hj J
      have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
      subst j
      simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
        abs_coordinateCurvatureComponent_le D b l J x hc (hK l) hmetric
          (hcurv l (by omega))
  | succ q ih =>
      obtain ⟨C, hC, hbound⟩ := ih l
      obtain ⟨C', _, hbound'⟩ := ih (l + 1)
      let E : ℝ := n * |C'| + n * (4 + l) * scalarJetProductBound q B (fun _ => C)
      refine ⟨max C E, le_max_of_le_left hC, ?_⟩
      intro g D b x hmetric hcurv hΓ j hj J
      have hlow := hbound g D b x hmetric
        (fun s hs => hcurv s (by omega)) (fun s hs => hΓ s (by omega))
      have hnext := hbound' g D b x hmetric
        (fun s hs => hcurv s (by omega)) (fun s hs => hΓ s (by omega))
      rcases Nat.eq_or_lt_of_le hj with rfl | hj
      · apply le_trans _ (le_max_right C E)
        exact norm_iteratedFDeriv_coordinateCurvatureComponent_succ_le D b l q
          B (fun _ => C) (fun _ => C') x
          (fun s hs => hΓ s (by omega)) hlow (hnext q le_rfl) J
      · exact (hlow j (by omega) J).trans (le_max_left C E)

end PoincareConjecture.SpacetimeBounds
