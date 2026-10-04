import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.Analysis.Compactness.SpatialEvolutionGluing
import PoincareLib.Geometry.RicciFlow.Compactness.Coordinates.SpacetimeBounds.Ricci.BootstrapAdapter

/-!
# The coordinate Ricci equation across retained times

Continuous actual spatial jets recover joint smoothness and the
Ricci equation at finitely many exceptional times. The evolution
operator is the published actual coordinate Ricci operator.
Morgan--Tian, Lemma 16.8 and Proposition 16.5, pp. 372-375;
see M44 derivation 51.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
-- Spatial Ricci jets contain nested continuous-linear coefficient spaces.
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M44

open SpacetimeBounds SpacetimeBounds.Bootstrap

/-- Positive metric coefficients with continuous spatial jets and
the Ricci equation away from finitely many times are jointly smooth
at those times too. Source: retained transport in Proposition 16.5;
M44 derivation 51. -/
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
-- Unfolding the Ricci two-jet projection needs additional definitional reduction.
/-- The actual coordinate Ricci equation extends to the exceptional
times once the spatial jets are continuous. Source: Proposition 16.5,
pp. 374-375; M44 derivation 51. -/
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

/-- Fixed smooth coordinates on an ordinary flow satisfy precisely
the coefficient equation used for retained gluing. Source: Lemma
16.8, pp. 372-373; M44 derivation 51. -/
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

end PoincareMT.M44
