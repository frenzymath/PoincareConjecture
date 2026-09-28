import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMetricEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapVariation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

theorem m64Annulus_moving_metric_energy_contDiffAt
    (F : RicciFlow n M (Icc a b)) {v : ℝ × LoopPlane → M}
    (t : ℝ) {q : ℝ × LoopPlane} (ht : t + q.1 ∈ Ioo a b)
    (hv : ContMDiffAt 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v q) :
    ContDiffAt ℝ ∞ (fun w : ℝ × LoopPlane =>
      m60EnergyDensity (F.metric (t + w.1)) (fun z => v (w.1, z)) w.2) q := by
  exact (m64MixedAnnulusEnergy_contDiffAt F
    (q := (t + q.1, q)) ht hv).comp (f := fun w : ℝ × LoopPlane => (t + w.1, w)) q
      ((contDiffAt_const.add contDiffAt_fst).prodMk contDiffAt_id)

theorem m64AnnulusEnergy_hasDerivAt_of_local_moving_metric
    (F : RicciFlow n M (Icc a b)) {t : ℝ} (ht : t ∈ Ioo a b)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {U : Set LoopPlane} (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ U)) :
    let E := fun q : ℝ × LoopPlane =>
      m60EnergyDensity (F.metric (t + q.1)) (fun z => v (q.1, z)) q.2
    IntegrableOn (fun p => fderiv ℝ E (0, p) (1, 0)) m64AnnulusDomain volume ∧
      HasDerivAt (fun r => ∫ p in m64AnnulusDomain, E (r, p))
        (∫ p in m64AnnulusDomain, fderiv ℝ E (0, p) (1, 0)) 0 ∧
      ∀ᶠ r : ℝ in 𝓝 0, IntegrableOn (fun p => E (r, p)) m64AnnulusDomain volume := by
  let E := fun q : ℝ × LoopPlane =>
    m60EnergyDensity (F.metric (t + q.1)) (fun z => v (q.1, z)) q.2
  let delta := min epsilon (min (t - a) (b - t))
  have hdelta : 0 < delta := lt_min hepsilon (lt_min (sub_pos.mpr ht.1) (sub_pos.mpr ht.2))
  have hsmall : Ioo (-delta) delta ⊆ Ioo (-epsilon) epsilon :=
    Ioo_subset_Ioo (neg_le_neg (min_le_left _ _)) (min_le_left _ _)
  have htime {r : ℝ} (hr : r ∈ Ioo (-delta) delta) : t + r ∈ Ioo a b := by
    have ha : delta ≤ t - a := (min_le_right _ _).trans (min_le_left _ _)
    have hb : delta ≤ b - t := (min_le_right _ _).trans (min_le_right _ _)
    constructor <;> linarith [hr.1, hr.2]
  have hopen : IsOpen (Ioo (-delta) delta ×ˢ U) := isOpen_Ioo.prod hU
  have hE : ContDiffOn ℝ ∞ E (Ioo (-delta) delta ×ˢ U) := by
    intro q hq
    exact (m64Annulus_moving_metric_energy_contDiffAt F t (htime hq.1)
      (hv.contMDiffAt ((isOpen_Ioo.prod hU).mem_nhds
        ⟨hsmall hq.1, hq.2⟩))).contDiffWithinAt
  have hint (r : ℝ) (hr : r ∈ Ioo (-delta) delta) :
      IntegrableOn (fun p => E (r, p)) m64AnnulusDomain volume :=
    (hE.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp => ⟨hr, hdom hp⟩)).integrableOn_compact m64AnnulusDomain_isCompact
  obtain ⟨hderivInt, hderiv⟩ :=
    m64AnnulusIntegral_hasDerivAt_of_local_continuous_derivative
      (F := fun r p => E (r, p)) (F' := fun r p => fderiv ℝ E (r, p) (1, 0))
      hdelta
      (fun r hr => hE.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun p hp => ⟨hr, hdom hp⟩))
      ((((hE.fderiv_of_isOpen hopen (m := ∞) (by simp)).clm_apply
        (contDiffOn_const (c := (1, (0 : LoopPlane))))).continuousOn).mono
          (prod_mono_right hdom))
      (fun r hr p hp =>
        ((hE.contDiffAt (hopen.mem_nhds ⟨hr, hdom hp⟩)).differentiableAt
          (by simp)).hasFDerivAt.comp_hasDerivAt (l := E)
            (f := fun s : ℝ => (s, p)) r
            ((hasDerivAt_id r).prodMk (hasDerivAt_const r p)))
  refine ⟨hderivInt, hderiv, ?_⟩
  filter_upwards [isOpen_Ioo.mem_nhds
    (show (0 : ℝ) ∈ Ioo (-delta) delta from ⟨by linarith, hdelta⟩)] with r hr
  exact hint r hr

end PoincareConjecture
