import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetFiniteCollar
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetRadialStokes











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory Complex
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Gauss

private theorem integral_disk_tendsto {G : LoopPlane → ℝ}
    (hG : IntegrableOn G loopDiskSet volume) {R : ℕ → ℝ}
    (hR : ∀ n, R n < 1) (hlim : Tendsto R atTop (𝓝 1)) :
    Tendsto (fun n => ∫ z in closedBall (0 : LoopPlane) (R n), G z)
      atTop (𝓝 (∫ z in loopDiskSet, G z)) := by
  have hsub (n : ℕ) : closedBall (0 : LoopPlane) (R n) ⊆ loopDiskSet :=
    closedBall_subset_closedBall (hR n).le
  have hnull : ∀ᵐ z : LoopPlane ∂volume, z ∉ sphere (0 : LoopPlane) 1 := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using Measure.addHaar_sphere volume (0 : LoopPlane) 1
  have hh := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict loopDiskSet)
    (F := fun n => (closedBall (0 : LoopPlane) (R n)).indicator G)
    (f := G) (fun z => ‖G z‖)
    (fun _ => hG.aestronglyMeasurable.indicator measurableSet_closedBall) hG.norm
    (fun _ => Eventually.of_forall fun _ => norm_indicator_le_norm_self _ _)
    (by
      filter_upwards [ae_restrict_mem (measurableSet_closedBall : MeasurableSet loopDiskSet),
        ae_restrict_of_ae hnull] with z hz hn
      have hz1 : ‖z‖ < 1 := lt_of_le_of_ne (mem_closedBall_zero_iff.mp hz)
        (by simpa only [mem_sphere_zero_iff_norm] using hn)
      apply tendsto_const_nhds.congr'
      filter_upwards [hlim.eventually (lt_mem_nhds hz1)] with n hnR
      rw [indicator_of_mem (mem_closedBall_zero_iff.mpr hnR.le)])
  have heq (n : ℕ) : (∫ z in loopDiskSet, (closedBall (0 : LoopPlane) (R n)).indicator G z) =
      ∫ z in closedBall (0 : LoopPlane) (R n), G z := by
    rw [integral_indicator measurableSet_closedBall,
      Measure.restrict_restrict measurableSet_closedBall, inter_eq_left.mpr (hsub n)]
  simpa only [heq] using hh

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65MinimalDisk

open M65Gauss

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}






theorem logarithmicGaussDensity_gaussBonnet (S : M65MinimalDisk g connection gamma)
    (hinj : Function.Injective (gamma : LoopCircle → M))
    (hsmooth : ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (periodicFreeLoop gamma))
    (hregular : ∀ t : ℝ, curveVelocity (n := 3) (periodicFreeLoop gamma) t ≠ 0)
    (W : (p : M) → TangentSpace (𝓡 3) p)
    (hW : ∀ s, W (periodicFreeLoop gamma s) = M65Filling.loopCurvature connection gamma s) :
    let G := logarithmicGaussDensity S.conformalFactor
    let B := fun theta => g.inner (S.disk.map (Proofs.M58.angularPoint theta))
      (W (S.disk.map (Proofs.M58.angularPoint theta)))
      (mfderivWithin (𝓡 2) (𝓡 3) S.disk.map loopDiskSet
        (Proofs.M58.angularPoint theta) (Proofs.M58.angularPoint theta))
    IntegrableOn G loopDiskSet volume ∧ IntervalIntegrable B volume (-Real.pi) Real.pi ∧
      2 * Real.pi ≤ (∫ z in loopDiskSet, G z) - ∫ theta in (-Real.pi)..Real.pi, B theta := by
  have hperiodic : periodicFreeLoop gamma = gamma ∘ m65LoopAngular := by
    funext t
    exact gamma.boundary (m65LoopAngular t)
  have hG := S.logarithmicGaussDensity_integrable hinj
    (hperiodic ▸ hsmooth) (hperiodic ▸ hregular)
  obtain ⟨hB, h, A, hh, hlim, hAlim, hbound⟩ :=
    S.exists_boundary_radial_lower_limit hinj hsmooth hregular W hW
  obtain ⟨R0, _hR0, hR01, hstokes⟩ := S.exists_curvature_radial_bound
  let R := fun n => Real.exp (-h n)
  have hR (n : ℕ) : R n < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos (hh n))
  have hRlim : Tendsto R atTop (𝓝 1) := by
    simpa only [neg_zero, Real.exp_zero, Function.comp_def, R] using
      (Real.continuous_exp.tendsto (-0)).comp hlim.neg
  have hcurvature := integral_disk_tendsto hG hR hRlim
  have hle : ∀ᶠ n in atTop,
      A n ≤ ∫ z in closedBall (0 : LoopPlane) (R n),
        logarithmicGaussDensity S.conformalFactor z := by
    filter_upwards [hRlim.eventually (lt_mem_nhds hR01)] with n hn
    exact (hbound n).2.trans (hstokes (R n) hn (hR n)).2
  have hfinal := le_of_tendsto_of_tendsto hAlim hcurvature hle
  refine ⟨hG, hB, ?_⟩
  linarith

end PoincareConjecture.M65MinimalDisk
