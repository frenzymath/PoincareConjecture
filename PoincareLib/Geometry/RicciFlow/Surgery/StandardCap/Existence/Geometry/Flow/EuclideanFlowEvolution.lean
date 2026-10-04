import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Geometry.Coordinates.ClosedPullbackCoefficients
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Construction.Coordinates.PartialFlowJetLimits
import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter

/-!
# Actual Euclidean Ricci-flow coefficients and their evolution

The identity spatial chart reads the genuine metric family and the
finite-jet Ricci equation. These identities apply to any Euclidean
dimension and actual time domain, with ordinary derivatives restricted
to open time domains. They are used for Morgan-Tian Theorem 12.5,
pp. 296-297.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- The two-jet target is a finite product of nested multilinear maps.
set_option maxSynthPendingDepth 8

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.RicciFlow

open SpacetimeBounds SpacetimeBounds.Bootstrap

variable {n : ℕ} {J : Set ℝ} (F : RicciFlow n (EuclideanSpace ℝ (Fin n)) J)

/-- The actual metric coefficients are jointly within-smooth on the
original time domain (Theorem 12.5, pp. 296-297). -/
theorem contDiffOn_euclideanCoefficients :
    ContDiffOn ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.metric p.1).euclideanCoefficients p.2) (J ×ˢ univ) := by
  simpa only [RiemannianMetric.pullbackCoefficients_id] using
    F.smooth.contDiffOn_spacetime_pullbackCoefficients
      isOpen_univ (contMDiffOn_id (I := 𝓡 n))

set_option synthInstance.maxHeartbeats 100000 in
-- The genuine coefficient equation uses the actual dependent two-jet.
/-- On an open time domain the metric coefficients have the ordinary
time derivative given by the actual finite-jet Ricci operator
(Theorem 12.5, pp. 296-297). -/
theorem hasDerivAt_euclideanCoefficients (hJ : IsOpen J) {t : ℝ} (ht : t ∈ J)
    (x : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s => (F.metric s).euclideanCoefficients x)
      (jetRicciFlowOperator n (spatialJet 2
        (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
          (F.metric p.1).euclideanCoefficients p.2) (t, x))) t := by
  have hinv (y : EuclideanSpace ℝ (Fin n)) (_hy : y ∈ (univ : Set _)) :
      (mfderiv (𝓡 n) (𝓡 n) id y).IsInvertible := by
    rw [mfderiv_id]
    exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩
  have heq := deriv_pullbackCoefficients_eq_ricciFlowOperator F hJ isOpen_univ
    contMDiffOn_id hinv ht (mem_univ x)
  simp only [RiemannianMetric.pullbackCoefficients_id] at heq
  have hpoint := F.contDiffOn_euclideanCoefficients.contDiffAt (x := (t, x))
    ((hJ.prod isOpen_univ).mem_nhds ⟨ht, mem_univ x⟩)
  have hd := (hpoint.comp t (contDiffAt_id.prodMk contDiffAt_const)).differentiableAt
    (by simp)
  rw [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet]
  convert! hd.hasDerivAt using 1
  exact heq.symm

set_option synthInstance.maxHeartbeats 100000 in
-- The Ricci domain reads exactly the zeroth coefficient of the two-jet.
/-- Every actual metric slice has an elliptic two-jet, independently
of the total time representative (Theorem 12.5, pp. 296-297). -/
theorem euclideanSpatialJet_mem_domain (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    spatialJet 2 (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.metric p.1).euclideanCoefficients p.2) (t, x) ∈ jetRicciFlowDomain n := by
  change ((twoJetProjection n (spatialJet 2
    (fun p : ℝ × EuclideanSpace ℝ (Fin n) =>
      (F.metric p.1).euclideanCoefficients p.2) (t, x))).1).IsInvertible
  rw [twoJetProjection_spatialJet]
  convert! (F.metric t).inner_isInvertible x

end PoincareMT.RicciFlow
