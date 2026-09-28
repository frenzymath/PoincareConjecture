import PoincareConjecture.Proofs.M34.Standard.DifferenceJetFluxParameters
import PoincareConjecture.Proofs.M34.Standard.UniformDifferenceRemainder











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

set_option maxSynthPendingDepth 8

open Set
open scoped BigOperators

namespace PoincareConjecture.M34.DifferenceEnergy

open SpacetimeBounds SpacetimeBounds.Bootstrap



noncomputable def curvatureDifferenceFluxFromJets {n : ℕ}
    (J0 J1 : Jet (V n) (MetricCoefficient n) 3) (H : FH n) (A : FA n) (S : FS n) : Flux n :=
  curvatureDifferenceFlux (inverseMetricThreeJet n J0) (inverseMetricThreeJet n J1)
    (connectionThreeJet n J0) (curvatureThreeJet n J1)
      (covariantCurvatureThreeJet n J1) H A S



noncomputable def curvatureDifferenceRemainderFromJets {n dS : ℕ}
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    (J0 J1 : Jet (V n) (MetricCoefficient n) 3)
    (d : Fin dS × Fin n → ℝ) (H : FH n) (A : FA n) (S : FS n) : Fin dS → ℝ :=
  curvatureDifferenceRemainder qS (inverseMetricThreeJet n J0) (inverseMetricThreeJet n J1)
    (connectionThreeJet n J0) (curvatureThreeJet n J1)
      (covariantCurvatureThreeJet n J1) (raisedCurvatureFluxThreeJet n J1) d H A S




theorem exists_uniform_differenceJetFlux_bounds
    {n dH dA dS : ℕ}
    (qH : FH n ≃L[ℝ] EuclideanSpace ℝ (Fin dH))
    (qA : FA n ≃L[ℝ] EuclideanSpace ℝ (Fin dA))
    (qS : FS n ≃L[ℝ] EuclideanSpace ℝ (Fin dS))
    {a : ℝ} (ha : 0 < a) (M : ℝ) :
    ∃ CF CW : ℝ, 0 ≤ CF ∧ 0 ≤ CW ∧
      ∀ J0 J1 : Jet (V n) (MetricCoefficient n) 3,
        ‖J0‖ ≤ M → ‖J1‖ ≤ M →
        (∀ v, a * ‖v‖ ^ 2 ≤
          (continuousMultilinearCurryFin0 ℝ (V n) (MetricCoefficient n) (J0 0)) v v) →
        (∀ v, a * ‖v‖ ^ 2 ≤
          (continuousMultilinearCurryFin0 ℝ (V n) (MetricCoefficient n) (J1 0)) v v) →
        (∀ (H : FH n) (A : FA n) (S : FS n),
          (∑ alpha : Fin dS, ∑ i : Fin n,
            curvatureContraction qS (curvatureDifferenceFluxFromJets J0 J1 H A S i) alpha ^ 2) ≤
            CF * ((∑ j, qH H j ^ 2) + (∑ j, qA A j ^ 2) + (∑ j, qS S j ^ 2))) ∧
        (∀ (d : Fin dS × Fin n → ℝ) (H : FH n) (A : FA n) (S : FS n) (ε : ℝ), 0 < ε →
          (∑ alpha : Fin dS, 2 * qS S alpha *
            curvatureDifferenceRemainderFromJets qS J0 J1 d H A S alpha) ≤
            ε * (∑ beta, d beta ^ 2) + (CW / ε + CW) *
              ((∑ j, qH H j ^ 2) + (∑ j, qA A j ^ 2) + (∑ j, qS S j ^ 2))) := by
  obtain ⟨K, hK, hKU, hbox⟩ := exists_compact_elliptic_jet_box n 1 ha M
  have hf : ContinuousOn
      (Prod.fst : Jet (V n) (MetricCoefficient n) 3 × Jet (V n) (MetricCoefficient n) 3 →
        Jet (V n) (MetricCoefficient n) 3) (K ×ˢ K) := continuous_fst.continuousOn
  have hs : ContinuousOn
      (Prod.snd : Jet (V n) (MetricCoefficient n) 3 × Jet (V n) (MetricCoefficient n) 3 →
        Jet (V n) (MetricCoefficient n) 3) (K ×ˢ K) := continuous_snd.continuousOn
  have hI0 := (contDiffOn_inverseMetricThreeJet n).continuousOn.comp hf
    (fun _ hp => hKU hp.1)
  have hI1 := (contDiffOn_inverseMetricThreeJet n).continuousOn.comp hs
    (fun _ hp => hKU hp.2)
  have hg := (continuousOn_connectionThreeJet n).comp hf (fun _ hp => hKU hp.1)
  have hR := (continuousOn_curvatureThreeJet n).comp hs (fun _ hp => hKU hp.2)
  have hk := (continuousOn_covariantCurvatureThreeJet n).comp hs (fun _ hp => hKU hp.2)
  have hv := (continuousOn_raisedCurvatureFluxThreeJet n).comp hs (fun _ hp => hKU hp.2)
  have hgc (i j l : Fin n) :=
    continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_pi.mp hg i) j) l
  have hRc (l j k m : Fin n) := continuousOn_pi.mp (continuousOn_pi.mp
    (continuousOn_pi.mp (continuousOn_pi.mp hR l) j) k) m
  have hkc (d l j k m : Fin n) := continuousOn_pi.mp (continuousOn_pi.mp
    (continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_pi.mp hk d) l) j) k) m
  have hvc (i l j k m : Fin n) := continuousOn_pi.mp (continuousOn_pi.mp
    (continuousOn_pi.mp (continuousOn_pi.mp (continuousOn_pi.mp hv i) l) j) k) m
  obtain ⟨CF, hCF, hflux⟩ := exists_uniform_curvatureDifferenceFlux_bound
    (hK.prod hK) qH qA qS hI0 hI1 hgc hRc hkc
  obtain ⟨CW, hCW, hrem⟩ := exists_uniform_curvatureDifferenceRemainder_bound
    (hK.prod hK) qH qA qS hI0 hI1 hgc hRc hkc hvc
  refine ⟨CF, CW, hCF, hCW, fun J0 J1 h0 h1 he0 he1 => ?_⟩
  have hp : (J0, J1) ∈ K ×ˢ K := ⟨hbox J0 h0 he0, hbox J1 h1 he1⟩
  exact ⟨hflux (J0, J1) hp, hrem (J0, J1) hp⟩

end PoincareConjecture.M34.DifferenceEnergy
