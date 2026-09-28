import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_Continuation
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Uniqueness

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_geodesic_to_annulus_exit
    (N : IntrinsicAnnulus) {R epsilon eta : ℝ}
    (hR : 0 < R) (hepsilon : 0 < epsilon) (heta : 0 < eta)
    {q : ℝ → AnnulusCoordinates}
    (hgeo : N.metric.IsGeodesicOn q (Ioo (-epsilon) epsilon))
    (hinside : ∀ t ∈ Ioo (0 : ℝ) eta, 1 < ‖q t‖ ∧ ‖q t‖ < 2) :
    ∃ b left right : ℝ, 0 < b ∧ b ≤ R ∧ 0 < left ∧ 0 < right ∧
      ∃ gamma : ℝ → AnnulusCoordinates,
        N.metric.IsGeodesicOn gamma (Ioo (-left) (b + right)) ∧
        gamma =ᶠ[𝓝 0] q ∧
        (∀ t ∈ Ioo (0 : ℝ) b, 1 < ‖gamma t‖ ∧ ‖gamma t‖ < 2) ∧
        gamma b ∈ standardAnnulusDomain ∧
        (b = R ∨ ‖gamma b‖ = 1 ∨ ‖gamma b‖ = 2) := by
  classical
  let d := min (epsilon / 2) (min (eta / 2) (R / 2))
  have hd : 0 < d := lt_min (half_pos hepsilon) (lt_min (half_pos heta) (half_pos hR))
  have hdE : d < epsilon := (min_le_left _ _).trans_lt (half_lt_self hepsilon)
  have hdEta : d < eta :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (half_lt_self heta)
  have hdR : d < R :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hR)
  have hgeo0 : N.metric.IsGeodesicOn q (Ioo (-d) d) := by
    intro t ht
    exact hgeo t ⟨by linarith [ht.1], ht.2.trans hdE⟩
  let T : Set ℝ := {b | d ≤ b ∧ b ≤ R ∧ ∃ gamma : ℝ → AnnulusCoordinates,
    N.metric.IsGeodesicOn gamma (Ioo (-d) b) ∧ gamma =ᶠ[𝓝 0] q ∧
      ∀ t ∈ Ioo (0 : ℝ) b, 1 < ‖gamma t‖ ∧ ‖gamma t‖ < 2}
  have hdT : d ∈ T := ⟨le_rfl, hdR.le, q, hgeo0, EventuallyEq.rfl,
    fun t ht => hinside t ⟨ht.1, ht.2.trans hdEta⟩⟩
  have hbounded : BddAbove T := ⟨R, fun _ ht => ht.2.1⟩
  let b := sSup T
  have hdb : d ≤ b := le_csSup hbounded hdT
  have hb : 0 < b := hd.trans_le hdb
  have hbR : b ≤ R := csSup_le ⟨d, hdT⟩ (fun _ ht => ht.2.1)
  choose f hf using fun r (hr : r ∈ T) => hr.2.2
  have hcompat (r : ℝ) (hr : r ∈ T) (s : ℝ) (hs : s ∈ T) :
      EqOn (f r hr) (f s hs) (Ioo (-d) (min r s)) := by
    have hzero : (0 : ℝ) ∈ Ioo (-d) (min r s) :=
      ⟨by linarith, lt_min (hd.trans_le hr.1) (hd.trans_le hs.1)⟩
    exact (show N.metric.IsGeodesicOn (f r hr) (Ioo (-d) (min r s)) from
      fun t ht => (hf r hr).1 t ⟨ht.1, ht.2.trans_le (min_le_left _ _)⟩)
      |>.eqOn_of_eventuallyEq
        (fun t ht => (hf s hs).1 t ⟨ht.1, ht.2.trans_le (min_le_right _ _)⟩)
        isOpen_Ioo (convex_Ioo _ _).isPreconnected hzero
        ((hf r hr).2.1.trans (hf s hs).2.1.symm)
  let G : ℝ → AnnulusCoordinates := fun t =>
    if ht : ∃ r ∈ T, t < r then f ht.choose ht.choose_spec.1 t else q t
  have hGeq (r : ℝ) (hr : r ∈ T) : EqOn G (f r hr) (Ioo (-d) r) := by
    intro t ht
    have hex : ∃ s ∈ T, t < s := ⟨r, hr, ht.2⟩
    change (if h : ∃ s ∈ T, t < s then f h.choose h.choose_spec.1 t else q t) = _
    rw [dif_pos hex]
    exact hcompat hex.choose hex.choose_spec.1 r hr
      ⟨ht.1, lt_min hex.choose_spec.2 ht.2⟩
  have hGgerm (r : ℝ) (hr : r ∈ T) {t : ℝ} (ht : t ∈ Ioo (-d) r) :
      G =ᶠ[𝓝 t] f r hr := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    exact hGeq r hr hs
  have hGgeo : N.metric.IsGeodesicOn G (Ioo (-d) b) := by
    intro t ht
    obtain ⟨r, hr, htr⟩ := exists_lt_of_lt_csSup ⟨d, hdT⟩ ht.2
    obtain ⟨p, q', w, hlocal⟩ := (hf r hr).1 t ⟨ht.1, htr⟩
    refine ⟨p, q', w, ?_⟩
    filter_upwards [hlocal, hGgerm r hr ⟨ht.1, htr⟩] with s hs heq
    exact ⟨heq.trans hs.1, hs.2⟩
  have hzero : (0 : ℝ) ∈ Ioo (-d) d := ⟨by linarith, hd⟩
  have hgerm : G =ᶠ[𝓝 0] q := (hGgerm d hdT hzero).trans (hf d hdT).2.1
  have hGinside (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) b) :
      1 < ‖G t‖ ∧ ‖G t‖ < 2 := by
    obtain ⟨r, hr, htr⟩ := exists_lt_of_lt_csSup ⟨d, hdT⟩ ht.2
    rw [hGeq r hr ⟨by linarith [ht.1], htr⟩]
    exact (hf r hr).2.2 t ⟨ht.1, htr⟩
  have hGinitial : EqOn G q (Ioo (-d) d) :=
    (show N.metric.IsGeodesicOn G (Ioo (-d) d) from
      fun t ht => hGgeo t ⟨ht.1, ht.2.trans_le hdb⟩).eqOn_of_eventuallyEq hgeo0
        isOpen_Ioo (convex_Ioo _ _).isPreconnected hzero hgerm
  let C := q '' Icc (-d) 0 ∪ standardAnnulusDomain
  have hC : IsCompact C := by
    apply IsCompact.union _ m64Intrinsic_standardAnnulus_isCompact
    apply isCompact_Icc.image_of_continuousOn
    exact hgeo.contMDiffOn.continuousOn.mono (fun t ht =>
      ⟨by linarith [ht.1], ht.2.trans_lt hepsilon⟩)
  have hGC : MapsTo G (Ioo (-d) b) C := by
    intro t ht
    by_cases hpos : 0 < t
    · exact Or.inr ⟨(hGinside t ⟨hpos, ht.2⟩).1.le,
        (hGinside t ⟨hpos, ht.2⟩).2.le⟩
    · have ht0 : t ≤ 0 := le_of_not_gt hpos
      exact Or.inl ⟨t, ⟨ht.1.le, ht0⟩, (hGinitial ⟨ht.1, ht0.trans_lt hd⟩).symm⟩
  obtain ⟨right, hright, gamma, hgammaEq, hgamma⟩ :=
    N.metric.exists_geodesic_continuation_of_compact_confinement
      (by linarith : -d < b) hGgeo hC hGC
  have hgammaGerm : gamma =ᶠ[𝓝 0] q := by
    apply EventuallyEq.trans _ hgerm
    filter_upwards [isOpen_Ioo.mem_nhds
      (show (0 : ℝ) ∈ Ioo (-d) b from ⟨by linarith, hb⟩)] with t ht
    exact hgammaEq ht
  have hgammaInside (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) b) :
      1 < ‖gamma t‖ ∧ ‖gamma t‖ < 2 := by
    rw [hgammaEq ⟨by linarith [ht.1], ht.2⟩]
    exact hGinside t ht
  have hcont : ContinuousAt gamma b :=
    hgamma.contMDiffOn.continuousOn.continuousAt
      (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  have hend : gamma b ∈ standardAnnulusDomain := by
    have hIoo : Ioo (0 : ℝ) b ∈ 𝓝[<] b := by
      rw [← nhdsWithin_Ioo_eq_nhdsLT hb]
      exact self_mem_nhdsWithin
    apply m64Intrinsic_standardAnnulus_isCompact.isClosed.mem_of_tendsto
      (b := 𝓝[<] b) (hcont.tendsto.mono_left nhdsWithin_le_nhds)
    filter_upwards [hIoo] with t ht
    exact ⟨(hgammaInside t ht).1.le, (hgammaInside t ht).2.le⟩
  refine ⟨b, d, right, hb, hbR, hd, hright, gamma,
    hgamma, hgammaGerm, hgammaInside, hend, ?_⟩
  by_contra hnot
  push Not at hnot
  have hbRlt : b < R := lt_of_le_of_ne hbR hnot.1
  have hinterior : 1 < ‖gamma b‖ ∧ ‖gamma b‖ < 2 :=
    ⟨lt_of_le_of_ne hend.1 hnot.2.1.symm, lt_of_le_of_ne hend.2 hnot.2.2⟩
  have hnear : {t : ℝ | 1 < ‖gamma t‖ ∧ ‖gamma t‖ < 2} ∈ 𝓝 b :=
    hcont.norm.preimage_mem_nhds (Ioo_mem_nhds hinterior.1 hinterior.2)
  obtain ⟨lo, hi, hbLoHi, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnear
  let e := min (right / 2) (min ((hi - b) / 2) ((R - b) / 2))
  have he : 0 < e := lt_min (half_pos hright)
    (lt_min (half_pos (sub_pos.mpr hbLoHi.2)) (half_pos (sub_pos.mpr hbRlt)))
  have heright : e < right := (min_le_left _ _).trans_lt (half_lt_self hright)
  have hehi : e < hi - b :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt
      (half_lt_self (sub_pos.mpr hbLoHi.2))
  have heR : e < R - b :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
      (half_lt_self (sub_pos.mpr hbRlt))
  have hnew : b + e ∈ T := by
    refine ⟨by linarith, by linarith, gamma, ?_, hgammaGerm, ?_⟩
    · intro t ht
      exact hgamma t ⟨ht.1, ht.2.trans_le (by linarith)⟩
    · intro t ht
      by_cases htb : t < b
      · exact hgammaInside t ⟨ht.1, htb⟩
      · exact hsub ⟨hbLoHi.1.trans_le (le_of_not_gt htb), by linarith [ht.2]⟩
  have hle := le_csSup hbounded hnew
  change b + e ≤ b at hle
  linarith

end PoincareConjecture
