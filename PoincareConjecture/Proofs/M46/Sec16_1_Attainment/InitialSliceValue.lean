import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.CappedSliceValue
import PoincareConjecture.Proofs.M14.Sec6_7_InitialReducedLength

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}
  {T start : ℝ} {x : G.Point}

theorem exists_initial_cappedSliceAction_bound
    (hM04 : RicciFlowCurvatureTheory.{0})
    (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    (LG : GeneralizedLGeometryConclusion G)
    (E : M14ExponentialFamily G T x) (C : ActionConfinement G T start x)
    (hstrip : Icc start T ⊆ I.domain)
    {c : ℝ} (hcpos : 0 < c) (hc : c ^ 2 ≤ T - start) :
    ∃ a : ℝ, 0 < a ∧ a ≤ c ∧
      cappedSliceAction G T x C.barrier a / (2 * a) ≤ 3 / 2 := by
  obtain ⟨U, hU, hUzero, hsub⟩ := E.domain_relative_open (0, 0) (E.domain_zero 0)
  have hUnear : ∀ᶠ s in 𝓝[>] (0 : ℝ), ((0 : G.Horizontal x), s) ∈ U :=
    mem_nhdsWithin_of_mem_nhds
      ((continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds
        (hU.mem_nhds hUzero))
  have hsurv : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioc 0 c ∧ ((0 : G.Horizontal x), s) ∈ E.domain := by
    filter_upwards [hUnear, Ioc_mem_nhdsGT hcpos] with s hsU hs
    have hsq : s ^ 2 ≤ T - start := ((sq_le_sq₀ hs.1.le hcpos.le).mpr hs.2).trans hc
    exact ⟨hs, hsub ⟨hsU, hs.1.le,
      hstrip ⟨by linarith, sub_le_self _ (sq_nonneg s)⟩⟩⟩
  obtain ⟨b, ⟨hb, hbc⟩, hZb⟩ := hsurv.exists
  have hlim := M14.tendsto_exponential_reducedLength_zero hM04 hM12 E hZb hb
  simp only [map_zero] at hlim
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), E.reduced_length 0 s < 3 / 2 :=
    hlim.eventually (Iio_mem_nhds (by norm_num))
  have hinterval : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioc 0 b := Ioc_mem_nhdsGT hb
  obtain ⟨a, ha, hared⟩ := (hinterval.and hsmall).exists
  have hac := ha.2.trans hbc
  have hZa : ((0 : G.Horizontal x), a) ∈ E.domain :=
    (E.maximal_lifetime 0).out (E.domain_zero 0) hZb ⟨ha.1.le, ha.2⟩
  have hsq : a ^ 2 ≤ T - start := ((sq_le_sq₀ ha.1.le hcpos.le).mpr hac).trans hc
  have hm := (cappedSliceAction_alternative hM04 hM12 LG E C ha.1 hsq).2.1
    (E.gamma 0 a) (E.path 0 a hZa ha.1)
  rw [← E.action_eq 0 a hZa ha.1] at hm
  have hdiv := div_le_div_of_nonneg_right hm (by nlinarith [ha.1] : (0 : ℝ) ≤ 2 * a)
  rw [← E.reduced_length_eq 0 a hZa ha.1] at hdiv
  exact ⟨a, ha.1, hac, hdiv.trans hared.le⟩

end PoincareConjecture.Proofs.M46
