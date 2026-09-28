import PoincareConjecture.Proofs.M44.Mathlib.SpatialEvolutionGluing
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M44

open SpacetimeBounds SpacetimeBounds.Bootstrap





theorem contDiffOn_ricci_coefficients_off_finite
    {n : ℕ} {J S : Set ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hJ : IsOpen J) (hU : IsOpen U) (hS : S.Finite)
    {B : ℝ × EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    (hsmooth : ContDiffOn ℝ ∞ B ((J \ S) ×ˢ U))
    (hspace : ∀ t ∈ J, ContDiffOn ℝ ∞ (fun x => B (t, x)) U)
    (hjets : ∀ m : ℕ, ContinuousOn
      (fun p => iteratedFDeriv ℝ m (fun x => B (p.1, x)) p.2) (J ×ˢ U))
    (hinv : ∀ p ∈ J ×ˢ U, (B p).IsInvertible)
    (hevol : ∀ t ∈ J, t ∉ S → ∀ x ∈ U,
      HasDerivAt (fun s => B (s, x))
        (ricciFlowOperator n (metricTwoJet (fun y => B (t, y)) x)) t) :
    ContDiffOn ℝ ∞ B (J ×ˢ U) := by
  apply contDiffOn_of_spatial_evolution_off_finite hJ hU hS
    (isOpen_jetRicciFlowDomain n) (contDiffOn_jetRicciFlowOperator n)
    hsmooth hspace hjets
  · intro p hp
    change (twoJetProjection n (spatialJet 2 B p)).1.IsInvertible
    rw [twoJetProjection_spatialJet]
    exact hinv p hp
  · intro t ht hnot x hx
    simpa only [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet]
      using hevol t ht hnot x hx

set_option maxHeartbeats 800000 in




theorem hasDerivAt_ricci_coefficients_off_finite
    {n : ℕ} {J S : Set ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}
    (hJ : IsOpen J) (hS : S.Finite)
    {B : ℝ × EuclideanSpace ℝ (Fin n) → MetricCoefficient n}
    (hB : ContinuousOn B (J ×ˢ U))
    (hjets : ∀ m : ℕ, ContinuousOn
      (fun p => iteratedFDeriv ℝ m (fun x => B (p.1, x)) p.2) (J ×ˢ U))
    (hinv : ∀ p ∈ J ×ˢ U, (B p).IsInvertible)
    (hevol : ∀ t ∈ J, t ∉ S → ∀ x ∈ U,
      HasDerivAt (fun s => B (s, x))
        (ricciFlowOperator n (metricTwoJet (fun y => B (t, y)) x)) t)
    {t : ℝ} (ht : t ∈ J) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    HasDerivAt (fun s => B (s, x))
      (ricciFlowOperator n (metricTwoJet (fun y => B (t, y)) x)) t := by
  have hjet : ContinuousOn (spatialJet 2 B) (J ×ˢ U) :=
    continuousOn_pi.mpr fun m => hjets m.1
  have hQ : ContinuousOn (fun p => jetRicciFlowOperator n (spatialJet 2 B p))
      (J ×ˢ U) := by
    apply (contDiffOn_jetRicciFlowOperator n).continuousOn.comp hjet
    intro p hp
    change (twoJetProjection n (spatialJet 2 B p)).1.IsInvertible
    rw [twoJetProjection_spatialJet]
    exact hinv p hp
  have htime := hQ.comp (continuousOn_id.prodMk continuousOn_const)
    (fun _ hs => ⟨hs, hx⟩)
  simp only [jetRicciFlowOperator, Function.comp_apply, twoJetProjection_spatialJet] at htime
  exact Poincare.hasDerivAt_of_hasDerivAt_off_finite hJ hS
    (hB.comp (continuousOn_id.prodMk continuousOn_const) (fun _ hs => ⟨hs, hx⟩))
    htime (fun s hs hnot => hevol s hs hnot x hx) ht




theorem hasDerivAt_pullbackCoefficients_ricci
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {J : Set ℝ} (F : RicciFlow n M J) (hJ : IsOpen J)
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U)
    {e : EuclideanSpace ℝ (Fin n) → M} (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e U)
    (hi : ∀ x ∈ U, (mfderiv (𝓡 n) (𝓡 n) e x).IsInvertible)
    {t : ℝ} (ht : t ∈ J) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    HasDerivAt (fun s => (F.metric s).pullbackCoefficients e x)
      (ricciFlowOperator n (metricTwoJet ((F.metric t).pullbackCoefficients e) x)) t := by
  rw [← deriv_pullbackCoefficients_eq_ricciFlowOperator F hJ hU he hi ht hx]
  have hd : DifferentiableAt ℝ (fun s => (F.metric s).pullbackCoefficients e x) t :=
    F.differentiableAt_pullbackCoefficients_time hJ hU he ht hx
  exact hd.hasDerivAt

end PoincareConjecture.M44
