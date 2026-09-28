import PoincareConjecture.Proofs.M34.Standard.UniformConnectionDifference
import PoincareConjecture.Proofs.M34.Standard.ConnectionVelocityJets











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped ContDiff BigOperators

namespace PoincareConjecture.M34.DifferenceEnergy

open SpacetimeBounds SpacetimeBounds.Bootstrap



noncomputable def connectionDifferenceRateFromJets {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    (J0 J1 : Jet (V n) (MetricCoefficient n) 3)
    (d : Fin dS × Fin n → ℝ) (H : FH n) (A : FA n) (S : FS n) : FA n :=
  connectionDifferenceRate qS (inverseMetricThreeJet n J0) (connectionThreeJet n J0)
    (curvatureThreeJet n J1) (connectionVelocityThreeJet n J1) d H A S




theorem exists_uniform_connectionJetRate_bound
    {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ J0 J1 : Jet (V n) (MetricCoefficient n) 3,
      ‖J0‖ ≤ M → ‖J1‖ ≤ M →
      (∀ v, a * ‖v‖ ^ 2 ≤
        (continuousMultilinearCurryFin0 ℝ (V n) (MetricCoefficient n) (J0 0)) v v) →
      (∀ v, a * ‖v‖ ^ 2 ≤
        (continuousMultilinearCurryFin0 ℝ (V n) (MetricCoefficient n) (J1 0)) v v) →
      ∀ (d : Fin dS × Fin n → ℝ) (H : FH n) (A : FA n) (S : FS n) (ε : ℝ), 0 < ε →
        (∑ alpha : Fin dA, 2 * qA A alpha *
          qA (connectionDifferenceRateFromJets qS J0 J1 d H A S) alpha) ≤
          ε * (∑ beta, d beta ^ 2) + (C / ε + C) *
            ((∑ j, qH H j ^ 2) + (∑ j, qA A j ^ 2) + (∑ j, qS S j ^ 2)) := by
  obtain ⟨K, hK, hKU, hbox⟩ := exists_compact_elliptic_jet_box n 1 ha M
  have hf : ContinuousOn
      (Prod.fst : Jet (V n) (MetricCoefficient n) 3 × Jet (V n) (MetricCoefficient n) 3 →
        Jet (V n) (MetricCoefficient n) 3) (K ×ˢ K) := continuous_fst.continuousOn
  have hs : ContinuousOn
      (Prod.snd : Jet (V n) (MetricCoefficient n) 3 × Jet (V n) (MetricCoefficient n) 3 →
        Jet (V n) (MetricCoefficient n) 3) (K ×ˢ K) := continuous_snd.continuousOn
  have hI := (contDiffOn_inverseMetricThreeJet n).continuousOn.comp hf
    (fun _ hp => hKU hp.1)
  have hg := (continuousOn_connectionThreeJet n).comp hf (fun _ hp => hKU hp.1)
  have hR := (continuousOn_curvatureThreeJet n).comp hs (fun _ hp => hKU hp.2)
  have hv := (continuousOn_connectionVelocityThreeJet n).comp hs (fun _ hp => hKU hp.2)
  obtain ⟨C, hC, hbound⟩ := exists_uniform_connectionDifference_bound (hK.prod hK)
    qH qA qS hI hg hR hv
  refine ⟨C, hC, fun J0 J1 h0 h1 he0 he1 => ?_⟩
  exact hbound (J0, J1) ⟨hbox J0 h0 he0, hbox J1 h1 he1⟩

end PoincareConjecture.M34.DifferenceEnergy
