import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_GraphStripFrontier

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff
open Poincare.Topology.Plane.Curves

namespace PoincareConjecture

private theorem positive_strip_of_point
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {delta : ℝ}
    (hsource : Icc (0 : ℝ) 1 ×ˢ Ioo (-delta) delta ⊆ H.source)
    (hfront : ∀ q ∈ H.source, H q ∈ frontier U ↔ q.2 = 0)
    (hpoint : ∃ z ∈ Ioo (0 : ℝ) delta, H (0, z) ∈ U) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Ioo (0 : ℝ) delta, H (t, z) ∈ U := by
  let S := Icc (0 : ℝ) 1 ×ˢ Ioo (0 : ℝ) delta
  have hS : S ⊆ H.source :=
    fun q hq => hsource ⟨hq.1, ⟨by linarith [hq.2.1, hq.2.2], hq.2.2⟩⟩
  have hconn : IsPreconnected (H '' S) :=
    (isPreconnected_Icc.prod isPreconnected_Ioo).image H (H.continuousOn.mono hS)
  obtain ⟨z, hz, hzU⟩ := hpoint
  have hsub : H '' S ⊆ U := hconn.subset_of_closure_inter_subset hU
    ⟨H (0, z), ⟨(0, z), ⟨by simp, hz⟩, rfl⟩, hzU⟩ (by
      rintro p ⟨hp, q, hq, rfl⟩
      by_contra hn
      have hpf : H q ∈ frontier U := ⟨hp, by simpa only [hU.interior_eq] using hn⟩
      exact hq.2.1.ne' ((hfront q (hS hq)).mp hpf))
  exact fun t ht z hz => hsub ⟨(t, z), ⟨ht, hz⟩, rfl⟩

theorem m64Intrinsic_exists_inward_graph_strip
    {gamma : ℝ → AnnulusCoordinates} (hg : Continuous gamma) {T a b : ℝ}
    (hend : gamma 0 = gamma T) (hinj : InjOn gamma (Ico 0 T))
    (hab : a < b) (ha : 0 < a) (hb : b < T)
    {U : Set AnnulusCoordinates} (hU : IsOpen U)
    (hfront : frontier U = gamma '' Icc 0 T)
    (L : AnnulusCoordinates ≃L[ℝ] (ℝ × ℝ))
    (G : OpenPartialHomeomorph ℝ ℝ) {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ ∞ f G.target)
    (hI : Icc a b ⊆ G.source) (hmono : StrictMonoOn G G.source)
    (hgraph : ∀ t ∈ G.source, L (gamma t) = (G t, f (G t)))
    (himage : G '' Icc a b = Icc (G a) (G b))
    (htarget : Icc (G a) (G b) ⊆ G.target)
    {ua wa ub wb : ℝ} (P : TransverseGraphCuts f (G a) (G b) ua wa ub wb)
    (hray : ∀ᶠ r in 𝓝[>] (0 : ℝ), gamma a + r • L.symm (ua, wa) ∈ U) :
    ∃ delta > 0, ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Icc (0 : ℝ) delta,
      (t, z) ∈ (P.linearCoordinates L.symm G.open_target hf).source ∧
      P.linearCoordinates L.symm G.open_target hf (t, z) ∈ closure U ∧
      (0 < z → P.linearCoordinates L.symm G.open_target hf (t, z) ∈ U) := by
  obtain ⟨rho, hrho, H, hsource, hmap, _, _, hline⟩ :=
    m64Intrinsic_exists_graph_strip_frontier_chart hg hend hinj hab ha hb L G hf
      hI hmono hgraph himage htarget P
  have hfrontH : ∀ q ∈ H.source, H q ∈ frontier U ↔ q.2 = 0 := by
    simpa only [hfront] using hline
  obtain ⟨epsilon, hepsilon, hcut⟩ :=
    P.left.exists_small_positive_parameters (lt_min hrho P.radius_pos)
  have hsmall : ∀ᶠ r in 𝓝[>] (0 : ℝ), r ∈ Ioo (0 : ℝ) epsilon :=
    Ioo_mem_nhdsGT hepsilon
  obtain ⟨r, hr, hrU⟩ := (hsmall.and hray).exists
  have hrcut := hcut r hr
  let z := P.left.parameter r
  have hz : z ∈ Ioo (0 : ℝ) rho :=
    ⟨hrcut.2.1, hrcut.2.2.trans_le (min_le_left _ _)⟩
  have hzP : z ∈ Ioo (-P.radius) P.radius :=
    ⟨by linarith [hrcut.2.1, P.radius_pos], hrcut.2.2.trans_le (min_le_right _ _)⟩
  have hpoint : H (0, z) ∈ U := by
    rw [hmap, P.linearCoordinates_left L.symm G.open_target hf hzP,
      ← hgraph a (hI (left_mem_Icc.mpr hab.le)), L.symm_apply_apply]
    change gamma a + P.left.parameter.symm (P.left.parameter r) • L.symm (ua, wa) ∈ U
    rw [P.left.parameter.left_inv hrcut.1]
    exact hrU
  have hinside := positive_strip_of_point hU H hsource hfrontH ⟨z, hz, hpoint⟩
  obtain ⟨eta, heta, hetasource⟩ := exists_strip_source_width
    (P.linearCoordinates L.symm G.open_target hf)
    (fun t ht => P.linearCoordinates_axis_mem_source L.symm G.open_target hf
      (hmono (hI (left_mem_Icc.mpr hab.le)) (hI (right_mem_Icc.mpr hab.le)) hab)
      htarget ht)
  have hmin : 0 < min rho eta := lt_min hrho heta
  refine ⟨min rho eta / 2, half_pos hmin, ?_⟩
  intro t ht s hs
  have hsmin : s < min rho eta := hs.2.trans_lt (half_lt_self hmin)
  have hsr : s < rho := hsmin.trans_le (min_le_left _ _)
  have hse : s < eta := hsmin.trans_le (min_le_right _ _)
  have hFs : (t, s) ∈ (P.linearCoordinates L.symm G.open_target hf).source := by
    exact hetasource ⟨ht, ⟨by linarith [hs.1], hse⟩⟩
  refine ⟨hFs, ?_, fun hpos => by simpa only [hmap] using hinside t ht s ⟨hpos, hsr⟩⟩
  rcases hs.1.eq_or_lt with hs0 | hpos
  · have hs0' : s = 0 := hs0.symm
    apply frontier_subset_closure
    rw [hs0']
    have hH0 : (t, (0 : ℝ)) ∈ H.source :=
      hsource ⟨ht, ⟨by linarith, hrho⟩⟩
    simpa only [hmap] using (hfrontH _ hH0).mpr rfl
  · exact subset_closure (by simpa only [hmap] using hinside t ht s ⟨hpos, hsr⟩)

end PoincareConjecture
