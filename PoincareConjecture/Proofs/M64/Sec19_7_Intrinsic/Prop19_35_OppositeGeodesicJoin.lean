import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CrossRayTangents

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

private theorem geodesic_germ_congr
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {f g : ℝ → AnnulusCoordinates} {x : ℝ}
    (hg : G.IsGeodesicOn g {x}) (heq : f =ᶠ[𝓝 x] g) :
    G.IsGeodesicOn f {x} := by
  intro t ht
  have ht' : t = x := mem_singleton_iff.mp ht
  subst t
  obtain ⟨p, q, w, hlocal⟩ := hg x (mem_singleton x)
  refine ⟨p, q, w, ?_⟩
  filter_upwards [hlocal, heq] with y hy hey
  exact ⟨hey.trans hy.1, hy.2⟩

theorem m64Intrinsic_opposite_meeting_smooth_geodesic_join
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} {s t : ℝ}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (hga : G.IsGeodesicOn alpha (Icc 0 s)) (hgb : G.IsGeodesicOn beta (Icc 0 t))
    (hs : 0 < s) (ht : 0 < t) (hmeet : alpha s = beta t)
    (hopposite : deriv alpha s = -deriv beta t) :
    ∃ gamma : ℝ → AnnulusCoordinates,
      (∀ x ≤ s, gamma x = alpha x) ∧
      (∀ x ≥ s, gamma x = beta (s + t - x)) ∧
      ContDiff ℝ ∞ gamma ∧ G.IsGeodesicOn gamma (Icc 0 (s + t)) ∧
      gamma 0 = alpha 0 ∧ gamma (s + t) = beta 0 ∧
      gamma '' Icc 0 (s + t) = alpha '' Icc 0 s ∪ beta '' Icc 0 t := by
  classical
  let eta : ℝ → AnnulusCoordinates := fun x => beta (s + t - x)
  have he : ContDiff ℝ ∞ eta := hb.comp (contDiff_const.sub contDiff_id)
  have hes : eta s = beta t := by
    dsimp only [eta]
    congr 1
    ring
  have hd : deriv eta s = -deriv beta t := by
    rw [deriv_comp_const_sub]
    congr 2
    ring
  have hegeo : G.IsGeodesicOn eta (Icc s (s + t)) := by
    have h : G.IsGeodesicOn (fun x => beta (-1 * x + (s + t))) (Icc s (s + t)) := by
      intro x hx
      apply hgb.comp_affine (-1) (s + t)
      exact ⟨by linarith [hx.2], by linarith [hx.1]⟩
    have hf : eta = (fun x => beta (-1 * x + (s + t))) := by
      funext x
      dsimp only [eta]
      congr 1
      ring
    rwa [hf]
  have hagerm : G.IsGeodesicOn alpha {s} := by
    intro x hx
    have hx' : x = s := mem_singleton_iff.mp hx
    subst x
    exact hga s ⟨hs.le, le_rfl⟩
  have hegerm : G.IsGeodesicOn eta {s} := by
    intro x hx
    have hx' : x = s := mem_singleton_iff.mp hx
    subst x
    exact hegeo s ⟨le_rfl, by linarith⟩
  have hcoord : deriv (fun x => extChartAt (𝓡 2) (alpha s) (alpha x)) s =
      deriv (fun x => extChartAt (𝓡 2) (alpha s) (eta x)) s := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, id_eq]
      using hopposite.trans hd.symm
  have hagree : alpha =ᶠ[𝓝 s] eta :=
    hagerm.eq_nhds_of_initial_data hegerm (mem_singleton s) (alpha s) (by simp)
      (hmeet.trans hes.symm) hcoord
  let gamma : ℝ → AnnulusCoordinates := fun x => if x ≤ s then alpha x else eta x
  have hleft (x : ℝ) (hx : x < s) : gamma =ᶠ[𝓝 x] alpha := by
    filter_upwards [Iio_mem_nhds hx] with y hy
    exact if_pos hy.le
  have hright (x : ℝ) (hx : s < x) : gamma =ᶠ[𝓝 x] eta := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact if_neg (not_le.mpr hy)
  have hjoin : gamma =ᶠ[𝓝 s] alpha := by
    filter_upwards [hagree] with y hy
    by_cases hys : y ≤ s
    · exact if_pos hys
    · exact (if_neg hys).trans hy.symm
  have hgc : ContDiff ℝ ∞ gamma := by
    rw [contDiff_iff_contDiffAt]
    intro x
    rcases lt_trichotomy x s with hx | rfl | hx
    · exact ha.contDiffAt.congr_of_eventuallyEq (hleft x hx)
    · exact ha.contDiffAt.congr_of_eventuallyEq hjoin
    · exact he.contDiffAt.congr_of_eventuallyEq (hright x hx)
  have hgg : G.IsGeodesicOn gamma (Icc 0 (s + t)) := by
    intro x hx
    rcases lt_trichotomy x s with hxs | rfl | hsx
    · have hgx : G.IsGeodesicOn alpha {x} := by
        intro y hy
        have hxy : y = x := mem_singleton_iff.mp hy
        subst y
        exact hga x ⟨hx.1, hxs.le⟩
      exact geodesic_germ_congr G hgx (hleft x hxs) x (mem_singleton x)
    · exact geodesic_germ_congr G hagerm hjoin x (mem_singleton x)
    · have hgx : G.IsGeodesicOn eta {x} := by
        intro y hy
        have hxy : y = x := mem_singleton_iff.mp hy
        subst y
        exact hegeo x ⟨hsx.le, hx.2⟩
      exact geodesic_germ_congr G hgx (hright x hsx) x (mem_singleton x)
  have hgl (x : ℝ) (hx : x ≤ s) : gamma x = alpha x := if_pos hx
  have hgr (x : ℝ) (hx : s ≤ x) : gamma x = beta (s + t - x) := by
    rcases hx.eq_or_lt with hxs | hxs
    · rw [← hxs, hgl s le_rfl, hmeet]
      congr 1
      ring
    · exact if_neg (not_le.mpr hxs)
  refine ⟨gamma, hgl, hgr, hgc, hgg, hgl 0 hs.le, ?_, ?_⟩
  · rw [hgr (s + t) (by linarith), sub_self]
  · ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hxs : x ≤ s
      · exact Or.inl ⟨x, ⟨hx.1, hxs⟩, (hgl x hxs).symm⟩
      · exact Or.inr ⟨s + t - x, ⟨by linarith [hx.2], by linarith⟩,
          (hgr x (le_of_not_ge hxs)).symm⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨x, ⟨hx.1, by linarith [hx.2]⟩, hgl x hx.2⟩
      · refine ⟨s + t - x, ⟨by linarith [hx.2], by linarith [hx.1]⟩, ?_⟩
        rw [hgr (s + t - x) (by linarith [hx.2])]
        congr 1
        ring

theorem m64Intrinsic_opposite_first_contact_embedded_join
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {alpha beta : ℝ → AnnulusCoordinates} {s t : ℝ}
    (ha : ContDiff ℝ ∞ alpha) (hb : ContDiff ℝ ∞ beta)
    (hga : G.IsGeodesicOn alpha (Icc 0 s)) (hgb : G.IsGeodesicOn beta (Icc 0 t))
    (hs : 0 < s) (ht : 0 < t) (hmeet : alpha s = beta t)
    (hopposite : deriv alpha s = -deriv beta t)
    (hai : InjOn alpha (Icc 0 s)) (hbi : InjOn beta (Icc 0 t))
    (hcontact : ∀ x ∈ Icc 0 s, ∀ y ∈ Icc 0 t,
      alpha x = beta y → x = s ∧ y = t) :
    ∃ gamma : ℝ → AnnulusCoordinates,
      (∀ x ≤ s, gamma x = alpha x) ∧
      (∀ x ≥ s, gamma x = beta (s + t - x)) ∧
      ContDiff ℝ ∞ gamma ∧ G.IsGeodesicOn gamma (Icc 0 (s + t)) ∧
      InjOn gamma (Icc 0 (s + t)) ∧
      gamma 0 = alpha 0 ∧ gamma (s + t) = beta 0 ∧
      gamma '' Icc 0 (s + t) = alpha '' Icc 0 s ∪ beta '' Icc 0 t := by
  obtain ⟨gamma, hleft, hright, hgc, hgg, hg0, hgend, hgi⟩ :=
    m64Intrinsic_opposite_meeting_smooth_geodesic_join G ha hb hga hgb hs ht hmeet hopposite
  refine ⟨gamma, hleft, hright, hgc, hgg, ?_, hg0, hgend, hgi⟩
  intro x hx y hy heq
  by_cases hxs : x ≤ s
  · by_cases hys : y ≤ s
    · rw [hleft x hxs, hleft y hys] at heq
      exact hai ⟨hx.1, hxs⟩ ⟨hy.1, hys⟩ heq
    · rw [hleft x hxs, hright y (le_of_not_ge hys)] at heq
      obtain ⟨hxeq, hyeq⟩ := hcontact x ⟨hx.1, hxs⟩ (s + t - y)
        ⟨by linarith [hy.2], by linarith⟩ heq
      linarith
  · by_cases hys : y ≤ s
    · rw [hright x (le_of_not_ge hxs), hleft y hys] at heq
      obtain ⟨hyeq, hxeq⟩ := hcontact y ⟨hy.1, hys⟩ (s + t - x)
        ⟨by linarith [hx.2], by linarith⟩ heq.symm
      linarith
    · rw [hright x (le_of_not_ge hxs), hright y (le_of_not_ge hys)] at heq
      have h := hbi ⟨by linarith [hx.2], by linarith⟩
        ⟨by linarith [hy.2], by linarith⟩ heq
      linarith

end PoincareConjecture
