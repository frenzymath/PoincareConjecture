import PoincareConjecture.Proofs.M28.Mathlib.MetricEndRayChord
import PoincareConjecture.Proofs.M28.Mathlib.ChordConeDistance











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M28.MetricEndRay

variable {X : Type u} [MetricSpace X]
  {E : UniformSpace.Completion X} {alpha : ℝ}




theorem dist_sq_le_of_chordDefect_le (P Q : MetricEndRay E alpha) {K : ℝ}
    (hupper : ∀ s ∈ Ioo (0 : ℝ) P.length, ∀ t ∈ Ioo (0 : ℝ) Q.length,
      chordDefect (fun u v => dist (P.point u) (Q.point v)) s t ≤ K)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) P.length)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) Q.length) :
    dist (P.point s) (Q.point t) ^ 2 ≤ (s - t) ^ 2 + s * t * K := by
  have hid : Tendsto (fun v : ℝ => v) (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    tendsto_nhds_of_tendsto_nhdsWithin tendsto_id
  have hunit : ∀ᶠ v : ℝ in 𝓝[<] (1 : ℝ), v ∈ Ioo (0 : ℝ) 1 := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds zero_lt_one),
      self_mem_nhdsWithin] with v hv0 hv1
    exact ⟨hv0, hv1⟩
  have hparameter {a l v : ℝ} (ha : a ∈ Ioc (0 : ℝ) l)
      (hv : v ∈ Ioo (0 : ℝ) 1) : v * a ∈ Ioo (0 : ℝ) l := by
    refine ⟨mul_pos hv.1 ha.1, ?_⟩
    have hh : v * a < a := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hv.2 ha.1
    exact hh.trans_le ha.2
  have hsmap : Tendsto (fun v : ℝ => v * s) (𝓝[<] (1 : ℝ)) (𝓝 s) := by
    simpa only [one_mul] using hid.mul_const s
  have htmap : Tendsto (fun v : ℝ => v * t) (𝓝[<] (1 : ℝ)) (𝓝 t) := by
    simpa only [one_mul] using hid.mul_const t
  have hswithin : Tendsto (fun v : ℝ => v * s) (𝓝[<] (1 : ℝ))
      (𝓝[Ioc (0 : ℝ) P.length] s) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hsmap, ?_⟩
    filter_upwards [hunit] with v hv
    exact ⟨(hparameter hs hv).1, (hparameter hs hv).2.le⟩
  have htwithin : Tendsto (fun v : ℝ => v * t) (𝓝[<] (1 : ℝ))
      (𝓝[Ioc (0 : ℝ) Q.length] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨htmap, ?_⟩
    filter_upwards [hunit] with v hv
    exact ⟨(hparameter ht hv).1, (hparameter ht hv).2.le⟩
  have hp := (P.continuousOn_point s hs).tendsto.comp hswithin
  have hq := (Q.continuousOn_point t ht).tendsto.comp htwithin
  have hright : Tendsto
      (fun v : ℝ => (v * s - v * t) ^ 2 + (v * s) * (v * t) * K)
      (𝓝[<] (1 : ℝ)) (𝓝 ((s - t) ^ 2 + s * t * K)) :=
    ((hsmap.sub htmap).pow 2).add ((hsmap.mul htmap).mul_const K)
  apply le_of_tendsto_of_tendsto ((hp.dist hq).pow 2) hright
  filter_upwards [hunit] with v hv
  change dist (P.point (v * s)) (Q.point (v * t)) ^ 2 ≤
    (v * s - v * t) ^ 2 + (v * s) * (v * t) * K
  have hdefect := hupper (v * s) (hparameter hs hv) (v * t) (hparameter ht hv)
  change (dist (P.point (v * s)) (Q.point (v * t)) ^ 2 - (v * s - v * t) ^ 2) /
    ((v * s) * (v * t)) ≤ K at hdefect
  have hmul := (div_le_iff₀
    (mul_pos (hparameter hs hv).1 (hparameter ht hv).1)).mp hdefect
  nlinarith only [hmul]




theorem dist_le_chordConeDistance [PseudoMetricSpace (MetricEndRay E alpha)]
    (P Q : MetricEndRay E alpha)
    (hupper : ∀ s ∈ Ioo (0 : ℝ) P.length, ∀ t ∈ Ioo (0 : ℝ) Q.length,
      chordDefect (fun u v => dist (P.point u) (Q.point v)) s t ≤ dist P Q ^ 2)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) P.length)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) Q.length) :
    dist (P.point s) (Q.point t) ≤ chordConeDistance s t (dist P Q) :=
  Real.le_sqrt_of_sq_le (P.dist_sq_le_of_chordDefect_le Q hupper s hs t ht)

end PoincareConjecture.M28.MetricEndRay
