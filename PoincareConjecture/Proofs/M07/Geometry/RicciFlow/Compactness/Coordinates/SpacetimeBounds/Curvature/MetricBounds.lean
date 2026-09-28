import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Curvature.FiniteOrder
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Connection.JetBounds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxSynthPendingDepth 8
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.SpacetimeBounds

open CoordinateExponential

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_uniform_coordinate_curvature_jet_bound_of_metric
    (n q l : ℕ) (c : ℝ) (hc : 0 ≤ c) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a : ℝ} (ha : 0 < a) (b A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g)
        (e : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
        (x : EuclideanSpace ℝ (Fin n)),
        ‖g.euclideanCoefficients x‖ ≤ b →
        (∀ v, a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v) →
        (∀ v, g.tangentNorm x v ≤ c * ‖v‖) →
        (∀ s ≤ l + q, D.curvatureDerivativeNorm s x ≤ K s) →
        (∀ j, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℝ j g.euclideanCoefficients x‖ ≤ A ^ j) →
        ∀ j ≤ q, ∀ J : Fin (4 + l) → Fin n,
          ‖iteratedFDeriv ℝ j (coordinateCurvatureComponent D l (fun i => e (J i))) x‖ ≤ C := by
  cases q with
  | zero =>
      obtain ⟨C, hC, hbound⟩ := exists_uniform_coordinate_curvature_jet_bound
        n 0 l c hc K (fun _ => 0) hK
      exact ⟨C, hC, fun g D e x _ _ hm hcurv _ =>
        hbound g D e x hm hcurv (fun j hj => by omega)⟩
  | succ q =>
      obtain ⟨G, hG, hΓ⟩ := exists_uniform_christoffel_jet_bound
        (E := EuclideanSpace ℝ (Fin n)) q ha b A hA
      obtain ⟨C, hC, hbound⟩ := exists_uniform_coordinate_curvature_jet_bound
        n (q + 1) l c hc K (fun _ => G) hK
      refine ⟨C, hC, ?_⟩
      intro g D e x hnorm hell hm hcurv hjets
      apply hbound g D e x hm hcurv
      intro j hj i k u
      have h := (norm_iteratedFDeriv_christoffel_repr_le
        (g.contDiffAt_euclideanCoefficients x) (g.inner_isInvertible x) e k j u (e i)).trans
        (hΓ g.euclideanCoefficients x (g.contDiffAt_euclideanCoefficients x)
          hnorm hell hjets j (by omega) u (e i))
      simpa only [e.norm_eq_one, mul_one] using h

theorem exists_affine_coordinate_curvature_jet_bound
    (n q l : ℕ) (c : ℝ) (hc : 0 ≤ c) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    {a : ℝ} (ha : 0 < a) (b A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (D : LeviCivitaData g)
        (e : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)))
        (x : EuclideanSpace ℝ (Fin n)),
        ‖g.euclideanCoefficients x‖ ≤ b →
        (∀ v, a * ‖v‖ ^ 2 ≤ g.euclideanCoefficients x v v) →
        (∀ v, g.tangentNorm x v ≤ c * ‖v‖) →
        (∀ s ≤ l + (q + 1), D.curvatureDerivativeNorm s x ≤ K s) →
        (∀ j, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℝ j g.euclideanCoefficients x‖ ≤ A ^ j) →
        ∀ J : Fin (4 + l) → Fin n,
          ‖iteratedFDeriv ℝ (q + 1) (coordinateCurvatureComponent D l (fun i => e (J i))) x‖ ≤
            C * (1 + ‖iteratedFDeriv ℝ (q + 1) g.euclideanCoefficients x‖) := by
  obtain ⟨C, hC, hcurv⟩ := exists_uniform_coordinate_curvature_jet_bound_of_metric
    n q l c hc K hK ha b A hA
  obtain ⟨C', hC', hcurv'⟩ := exists_uniform_coordinate_curvature_jet_bound_of_metric
    n q (l + 1) c hc K hK ha b A hA
  obtain ⟨G, hG, hΓ⟩ := exists_affine_christoffel_jets_bound
    (E := EuclideanSpace ℝ (Fin n)) q ha b A hA
  let S : ℝ := ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  refine ⟨n * C' + n * (4 + l) * (G * C * S), by positivity, ?_⟩
  intro g D e x hnorm hell hm hKx hjets J
  let T : ℝ := 1 + ‖iteratedFDeriv ℝ (q + 1) g.euclideanCoefficients x‖
  have hT : 1 ≤ T := le_add_of_nonneg_right (norm_nonneg _)
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hlow := hcurv g D e x hnorm hell hm (fun s hs => hKx s (by omega)) hjets
  have hnext := hcurv' g D e x hnorm hell hm (fun s hs => hKx s (by omega)) hjets
  have hΓx (j : ℕ) (hj : j ≤ q) (i k : Fin n) (u : EuclideanSpace ℝ (Fin n)) :
      ‖iteratedFDeriv ℝ j (fun y =>
        e.repr (christoffelBilinear g.euclideanCoefficients y u (e i)) k) x‖ ≤
          (G * T) * ‖u‖ := by
    have h := (norm_iteratedFDeriv_christoffel_repr_le
      (g.contDiffAt_euclideanCoefficients x) (g.inner_isInvertible x) e k j u (e i)).trans
      (hΓ g.euclideanCoefficients x (g.contDiffAt_euclideanCoefficients x)
        hnorm hell hjets j hj u (e i))
    simpa only [e.norm_eq_one, mul_one] using h
  have h := norm_iteratedFDeriv_coordinateCurvatureComponent_succ_le D e l q
    (fun _ => G * T) (fun _ => C) (fun _ => C') x hΓx hlow (hnext q le_rfl) J
  have hproduct : scalarJetProductBound q (fun _ => G * T) (fun _ => C) =
      (G * C * S) * T := by
    simp only [scalarJetProductBound, abs_of_nonneg (mul_nonneg hG hT0),
      abs_of_nonneg hC, ← Finset.sum_mul, S]
    ring
  rw [hproduct, abs_of_nonneg hC'] at h
  apply h.trans
  change (n : ℝ) * C' + n * (4 + l) * (G * C * S * T) ≤
    (n * C' + n * (4 + l) * (G * C * S)) * T
  have : 0 ≤ (n : ℝ) * C' := mul_nonneg (Nat.cast_nonneg _) hC'
  nlinarith

end PoincareConjecture.SpacetimeBounds
