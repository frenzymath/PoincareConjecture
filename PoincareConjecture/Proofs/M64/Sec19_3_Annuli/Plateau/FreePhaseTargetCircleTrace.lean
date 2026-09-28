import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreePhaseCircleTrace

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M64FreeWeakPhaseAnnulus

open Proofs.M58

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  {e : M → EuclideanSpace ℝ (Fin m)}
  {R : EuclideanSpace ℝ (Fin m) →L[ℝ] LoopPlane} {c0 c1 : ℝ → M}
  {H0 H1 : ℝ ≃o ℝ} {k D : ℝ}

local notation "S" => interior m64AnnulusDomain
local notation "circleMu" => volume.restrict (Icc (0 : ℝ) curvePeriod)

theorem local_circle_phase
    (A : M64FreeWeakPhaseAnnulus (n := n) e R c0 c1 H0 H1 k D) (he : Continuous e)
    (a : LoopPlane) {rho : ℝ} (hrho : 0 < rho) (hKS : closedBall a rho ⊆ S) :
    ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1),
      ∃ L : ℝ → ℝ, Continuous L ∧ Function.Periodic L curvePeriod ∧
        (L =ᵐ[circleMu] fun x => A.phase (m64MorreyPolarStrip a rho (annulusPoint x s))) ∧
        (∀ (phi : LoopPlane → ℝ), ContDiff ℝ 1 phi → ∀ i : Fin 2,
          (∫ p in closedBall a (rho * Real.exp (-s)), phi p * A.phaseColumn i p) +
            (∫ p in closedBall a (rho * Real.exp (-s)),
              fderiv ℝ phi p (EuclideanSpace.single i 1) * A.phase p) =
            rho * Real.exp (-s) * ∫ x in Icc (0 : ℝ) curvePeriod,
              angularPoint (x - Real.pi) i *
                (phi (a + (rho * Real.exp (-s)) • angularPoint (x - Real.pi)) * L x)) ∧
        ∀ gamma : ℝ → M, Continuous gamma → Function.Periodic gamma curvePeriod →
          gamma =ᵐ[circleMu]
            (fun x => A.annulus.map (m64MorreyPolarStrip a rho (annulusPoint x s))) →
          ∀ x, R (e (gamma x)) = angularPoint (k * L x) := by
  have htrace := m64WeakScalar_local_circle_trace isOpen_interior a hrho hKS A.phase
    (fun i => A.phaseColumn i) (Lp.memLp A.phase)
    (fun i => Lp.memLp (A.phaseColumn i)) A.phase_weak
  have hpull := m64MorreyPolarStrip_ae a hrho
    (ae_restrict_of_ae_restrict_of_subset hKS A.phase_observation)
  have hprod := m64AnnulusPoint_measurePreserving.quasiMeasurePreserving.ae hpull
  have hslices : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) 1), ∀ᵐ x ∂circleMu,
      R (e (A.annulus.map (m64MorreyPolarStrip a rho (annulusPoint x s)))) =
        angularPoint (k * A.phase (m64MorreyPolarStrip a rho (annulusPoint x s))) :=
    Measure.ae_ae_of_ae_prod (Measure.measurePreserving_swap.quasiMeasurePreserving.ae hprod)
  filter_upwards [htrace, hslices] with s hs hobs
  obtain ⟨L, hL, hLP, hLA, hgreen⟩ := hs
  refine ⟨L, hL, hLP, hLA, hgreen, ?_⟩
  intro gamma hgamma hgammaP hgammaAE
  have hAE : (fun x => R (e (gamma x))) =ᵐ[circleMu] fun x => angularPoint (k * L x) := by
    filter_upwards [hgammaAE, hLA, hobs] with x hg hl ho
    rw [hg, hl]
    exact ho
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hc : Continuous (fun x => angularPoint (k * L x)) :=
    contDiff_angularPoint.continuous.comp (continuous_const.mul hL)
  have heq := Measure.eqOn_Icc_of_ae_eq volume hP.ne hAE
    (R.continuous.comp (he.comp hgamma)).continuousOn hc.continuousOn
  intro x
  let y := toIcoMod hP 0 x
  have hy : y ∈ Icc (0 : ℝ) curvePeriod := Ico_subset_Icc_self (toIcoMod_mem_Ico' hP x)
  have hgy : gamma y = gamma x := by
    simpa only [y, toIcoMod, neg_smul, sub_eq_add_neg] using
      (hgammaP.zsmul (-toIcoDiv hP 0 x)) x
  have hLy : L y = L x := by
    simpa only [y, toIcoMod, neg_smul, sub_eq_add_neg] using
      (hLP.zsmul (-toIcoDiv hP 0 x)) x
  simpa only [hgy, hLy] using heq hy

end PoincareConjecture.M64FreeWeakPhaseAnnulus
