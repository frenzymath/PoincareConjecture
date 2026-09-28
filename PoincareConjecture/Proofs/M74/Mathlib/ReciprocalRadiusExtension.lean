import PoincareConjecture.Proofs.M74.Mathlib.RadialBallDiffeomorph
import Mathlib.Topology.Algebra.Order.Field










set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M74




theorem exists_reciprocalRadiusChart (σ : ℝ → ℝ) {a0 a b R : ℝ}
    (ha0 : 0 < a0) (ha : a0 < a) (hab : a < b) (hbR : b < R)
    (hσ : ContDiffOn ℝ ∞ σ (Ioo a0 R))
    (hpos : ∀ r ∈ Ioo a0 R, 0 < σ r)
    (hder : ∀ r ∈ Ioo a0 R, deriv σ r < 0)
    (hcont : ContinuousAt σ R) (hzero : σ R = 0) :
    ∃ (k : ℝ) (e : OpenPartialHomeomorph ℝ ℝ),
      0 < k ∧ e.source = Ioo 0 R ∧ e.target = Ioi 0 ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      (∀ r ∈ Ioo (0 : ℝ) a, e r = k * r) ∧
      (∀ r ∈ Ioo b R, e r = 1 / σ r) := by
  let g : ℝ → ℝ := fun r => 1 / σ r
  have haR : a < R := hab.trans hbR
  have ha0R : a0 < R := ha.trans haR
  have hR : 0 < R := ha0.trans ha0R
  have hg : ContDiffOn ℝ ∞ g (Ioo a0 R) :=
    contDiffOn_const.div hσ (fun r hr => (hpos r hr).ne')
  have hgd : ∀ r ∈ Ioo a0 R, 0 < deriv g r := by
    intro r hr
    have hd := ((hσ.contDiffAt (isOpen_Ioo.mem_nhds hr)).differentiableAt
      (by simp)).hasDerivAt.inv (hpos r hr).ne'
    change HasDerivAt (fun t => (σ t)⁻¹) (-(deriv σ r) / (σ r) ^ 2) r at hd
    have hgder : deriv g r = -(deriv σ r) / (σ r) ^ 2 := by
      simpa only [g, one_div] using hd.deriv
    rw [hgder]
    exact div_pos (neg_pos.mpr (hder r hr)) (sq_pos_of_pos (hpos r hr))
  have hgm : StrictMonoOn g (Ioo a0 R) := by
    apply strictMonoOn_of_deriv_pos (convex_Ioo a0 R) hg.continuousOn
    intro r hr
    exact hgd r (interior_subset hr)
  have hga : 0 < g a := one_div_pos.mpr (hpos a ⟨ha, haR⟩)
  let k := g a / (2 * R)
  have hk : 0 < k := div_pos hga (mul_pos (by norm_num) hR)
  have hkR : k * R = g a / 2 := by
    dsimp only [k]
    field_simp
  have hbound : ∀ r ∈ Ico a R, k * r ≤ g r := by
    intro r hr
    calc
      k * r ≤ k * R := mul_le_mul_of_nonneg_left hr.2.le hk.le
      _ = g a / 2 := hkR
      _ ≤ g a := by linarith
      _ ≤ g r := hgm.monotoneOn ⟨ha, haR⟩ ⟨ha.trans_le hr.1, hr.2⟩ hr.1
  have hgd' : ∀ r ∈ Ico a R, 0 < deriv g r :=
    fun r hr => hgd r ⟨ha.trans_le hr.1, hr.2⟩
  let f := positiveRadiusSplice g a0 a b k
  have hfm : StrictMonoOn f (Iio R) :=
    positiveRadiusSplice_strictMonoOn ha hab hk hg hgd' hbound
  have hfc : ∀ r < R, ContDiffAt ℝ ∞ f r :=
    fun _ hr => positiveRadiusSplice_contDiffAt ha hab hg hr
  have hfd : ∀ r < R, 0 < deriv f r :=
    fun _ hr => positiveRadiusSplice_deriv_pos ha hab hk hg hgd' hbound hr
  have hfzero : f 0 = 0 := by
    rw [show f 0 = k * 0 from positiveRadiusSplice_linear g hab (ha0.trans ha).le]
    ring
  have hlimσ : Tendsto σ (𝓝[<] R) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [hzero] using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [Ioo_mem_nhdsLT ha0R] with r hr
      exact hpos r hr
  have hlim : Tendsto g (𝓝[<] R) atTop := by
    simpa only [g, one_div, Function.comp_def] using tendsto_inv_nhdsGT_zero.comp hlimσ
  have himage : f '' Ioo (0 : ℝ) R = Ioi 0 := by
    apply subset_antisymm
    · rintro y ⟨r, hr, rfl⟩
      have h := hfm hR hr.2 hr.1
      rwa [hfzero] at h
    · intro y hy
      have hevent : ∀ᶠ r in 𝓝[<] R, r ∈ Ioo b R ∧ y < g r := by
        filter_upwards [Ioo_mem_nhdsLT hbR, hlim.eventually (eventually_gt_atTop y)] with r hr hyr
        exact ⟨hr, hyr⟩
      obtain ⟨r, hr, hyr⟩ := hevent.exists
      have hr0 : 0 < r := (ha0.trans (ha.trans hab)).trans hr.1
      have hfr : f r = g r := positiveRadiusSplice_outer g ha hab hr.1.le
      have hc : ContinuousOn f (Icc 0 r) := by
        intro t ht
        exact (hfc t (ht.2.trans_lt hr.2)).continuousAt.continuousWithinAt
      obtain ⟨t, ht, hty⟩ := intermediate_value_Icc hr0.le hc
        (show y ∈ Icc (f 0) (f r) by rw [hfzero, hfr]; exact ⟨hy.le, hyr.le⟩)
      have ht0 : 0 < t := by
        apply lt_of_le_of_ne ht.1
        intro h
        have htzero : t = 0 := h.symm
        rw [htzero, hfzero] at hty
        exact (ne_of_gt hy) hty.symm
      exact ⟨t, ⟨ht0, ht.2.trans_lt hr.2⟩, hty⟩
  have hfm' : StrictMonoOn f (Ioo (0 : ℝ) R) := hfm.mono (fun _ hr => hr.2)
  let e := increasingRadiusChart f R hfm' himage
  have hfs : ContDiffOn ℝ ∞ f (Ioo (0 : ℝ) R) :=
    fun r hr => (hfc r hr.2).contDiffWithinAt
  refine ⟨k, e, hk, rfl, rfl, hfs, ?_, ?_, ?_⟩
  · exact increasingRadiusChart_symm_contDiffOn f R hfm' himage hfs
      (fun r hr => (hfd r hr.2).ne')
  · intro r hr
    exact positiveRadiusSplice_linear g hab hr.2.le
  · intro r hr
    exact positiveRadiusSplice_outer g ha hab hr.1.le

end PoincareConjecture.M74
