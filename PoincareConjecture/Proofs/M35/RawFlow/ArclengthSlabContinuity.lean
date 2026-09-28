import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicInverseFamily
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness

variable {g₀ : StandardInitialMetric} (G : PartialStandardCapFlow g₀)

theorem raw_radialArclength_continuousOn_slab {T : ℝ} (hT : 0 ≤ T)
    (hTlt : T < G.lifetime) :
    ContinuousOn (fun p : ℝ × ℝ => radialArclength (G.flow.metric p.1) p.2)
      (Icc 0 T ×ˢ univ) := by
  let c (t : ℝ) := min T (max 0 t)
  have hc : Continuous c := continuous_const.min (continuous_const.max continuous_id)
  have hcG (t : ℝ) : c t ∈ Ico 0 G.lifetime :=
    ⟨le_min hT (le_max_left _ _), (min_le_left _ _).trans_lt hTlt⟩
  have hceq {t : ℝ} (ht : t ∈ Icc 0 T) : c t = t := by
    simp only [c, max_eq_right ht.1, min_eq_right ht.2]
  let F (p : ℝ × ℝ) (a : ℝ) := axisRadialSpeed (G.flow.metric (c p.1)) (p.2 * a)
  have hF : Continuous (Function.uncurry F) := by
    have hm : Continuous (fun z : (ℝ × ℝ) × ℝ => (c z.1.1, z.1.2 * z.2)) :=
      (hc.comp continuous_fst.fst).prodMk (continuous_fst.snd.mul continuous_snd)
    exact (raw_axisRadialSpeed_contDiffOn G).continuousOn.comp_continuous hm
      (fun z => ⟨hcG z.1.1, mem_univ _⟩)
  have hI : Continuous (fun p : ℝ × ℝ => ∫ a in Icc (0 : ℝ) 1, F p a) :=
    continuous_parametric_integral_of_continuous hF isCompact_Icc
  apply (continuous_snd.mul hI).continuousOn.congr
  intro p hp
  change radialArclength (G.flow.metric p.1) p.2 = p.2 * ∫ a in Icc (0 : ℝ) 1, F p a
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  have hscale := intervalIntegral.mul_integral_comp_mul_left
    (f := fun a => axisRadialSpeed (G.flow.metric p.1) a) p.2 (a := (0 : ℝ)) (b := 1)
  simp only [mul_zero, mul_one] at hscale
  change (∫ a in (0 : ℝ)..p.2, axisRadialSpeed (G.flow.metric p.1) a) = _
  simpa only [F, hceq hp.1] using hscale.symm

variable (P : RicciFlowCurvatureTheory.{0})
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)

theorem rawInverseRadius_continuousOn_slab {T : ℝ} (hT : 0 ≤ T)
    (hTlt : T < G.lifetime) :
    ContinuousOn (Function.uncurry (rawInverseRadius P G hrotation))
      (Icc 0 T ×ˢ univ) := by
  change ContinuousOn (fun p : ℝ × ℝ => rawInverseRadius P G hrotation p.1 p.2) _
  let U : Set (ℝ × ℝ) := Icc 0 T ×ˢ univ
  have hS := raw_radialArclength_continuousOn_slab G hT hTlt
  have hJ (p : ℝ × ℝ) (hp : p ∈ U) : p.1 ∈ Ico 0 G.lifetime :=
    ⟨hp.1.1, hp.1.2.trans_lt hTlt⟩
  have hfixed (a : ℝ) : ContinuousOn (fun p : ℝ × ℝ =>
      radialArclength (G.flow.metric p.1) a) U :=
    hS.comp (continuousOn_fst.prodMk continuousOn_const) (fun _ hp => ⟨hp.1, mem_univ _⟩)
  intro p hp
  apply tendsto_order.mpr
  constructor
  · intro a ha
    have hpa : radialArclength (G.flow.metric p.1) a < p.2 := by
      have hh := radialArclength_strictMono (G.flow.metric p.1) ha
      rwa [radialArclength_rawInverseRadius P G hrotation (hJ p hp)] at hh
    have he := ((hfixed a p hp).sub continuousWithinAt_snd).eventually
      (eventually_lt_nhds (sub_neg.mpr hpa))
    filter_upwards [he, self_mem_nhdsWithin] with q hq hqU
    apply (radialArclength_strictMono (G.flow.metric q.1)).lt_iff_lt.mp
    rw [radialArclength_rawInverseRadius P G hrotation (hJ q hqU)]
    exact sub_neg.mp hq
  · intro b hb
    have hpb : p.2 < radialArclength (G.flow.metric p.1) b := by
      have hh := radialArclength_strictMono (G.flow.metric p.1) hb
      rwa [radialArclength_rawInverseRadius P G hrotation (hJ p hp)] at hh
    have he := ((hfixed b p hp).sub continuousWithinAt_snd).eventually
      (eventually_gt_nhds (sub_pos.mpr hpb))
    filter_upwards [he, self_mem_nhdsWithin] with q hq hqU
    apply (radialArclength_strictMono (G.flow.metric q.1)).lt_iff_lt.mp
    rw [radialArclength_rawInverseRadius P G hrotation (hJ q hqU)]
    exact sub_pos.mp hq

end PoincareConjecture.M35.Uniqueness
