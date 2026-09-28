import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMetricIntegral












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}





theorem m64AnnulusArea_forward_majorant_of_conformal_moving_metric
    (F : RicciFlow n M (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {U : Set LoopPlane} (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U))
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      m60AreaGram (F.metric t) (fun z => v (0, z)) p 0 0 =
        m60AreaGram (F.metric t) (fun z => v (0, z)) p 1 1 ∧
      m60AreaGram (F.metric t) (fun z => v (0, z)) p 0 1 = 0) :
    let E := fun q : ℝ × LoopPlane =>
      m60EnergyDensity (F.metric (t + q.1)) (fun z => v (q.1, z)) q.2
    let d := ∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)
    ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
      m64AnnulusArea (F.metric (t + h)) (fun p => v (h, p)) ≤
        m64AnnulusArea (F.metric t) (fun p => v (0, p)) + h * (d + eta) := by
  let E := fun q : ℝ × LoopPlane =>
    m60EnergyDensity (F.metric (t + q.1)) (fun z => v (q.1, z)) q.2
  let energy := fun r => ∫ p in m64AnnulusDomain, E (r, p)
  let d := ∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)
  obtain ⟨_, hderiv, hint⟩ :=
    m64AnnulusEnergy_hasDerivAt_of_local_moving_metric F ht hepsilon hU hdom hv
  have hcenter : m64AnnulusArea (F.metric t) (fun p => v (0, p)) = energy 0 := by
    apply integral_congr_ae
    filter_upwards [hconformal] with p hp
    simpa only [E, add_zero] using
      m60AreaDensity_eq_energyDensity_of_gram (F.metric t) (fun p => v (0, p)) p hp.1 hp.2
  have hquot : Tendsto (fun h => (energy h - energy 0) / h) (𝓝[>] 0) (𝓝 d) := by
    simpa only [zero_add, smul_eq_mul, ← div_eq_inv_mul] using
      hderiv.tendsto_slope_zero_right
  change ∀ eta : ℝ, 0 < eta → ∀ᶠ h : ℝ in 𝓝[>] 0,
    m64AnnulusArea (F.metric (t + h)) (fun p => v (h, p)) ≤
      m64AnnulusArea (F.metric t) (fun p => v (0, p)) + h * (d + eta)
  intro eta heta
  have hev := hquot.eventually (Iio_mem_nhds (lt_add_of_pos_right d heta))
  filter_upwards [hev, nhdsWithin_le_nhds hint, self_mem_nhdsWithin] with h hh hi hpos
  have hupper : m64AnnulusArea (F.metric (t + h)) (fun p => v (h, p)) ≤ energy h :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun p =>
        m60AreaDensity_nonneg (F.metric (t + h)) (fun p => v (h, p)) p) hi
      (Eventually.of_forall fun p =>
        m60AreaDensity_le_energyDensity (F.metric (t + h)) (fun p => v (h, p)) p)
  have hdiff := (div_le_iff₀ hpos).mp hh.le
  rw [hcenter]
  exact hupper.trans (by linarith)

end PoincareConjecture
