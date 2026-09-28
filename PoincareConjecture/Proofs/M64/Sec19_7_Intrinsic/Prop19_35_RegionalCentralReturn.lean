import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalEndpointCapacity
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionalEmbeddedContact
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_TransverseRetainedBases

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology ContDiff Manifold Bundle Matrix

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem m64Intrinsic_exists_regional_central_return
    (N : IntrinsicAnnulus) {K delta r q mu alpha h : ℝ}
    (hK : N.GaussianCurvatureBound K) (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 100)
    (hq : 0 < q) (hqr : q ≤ r) (hh : 0 < h) (hhq : h ≤ q / 100)
    (hturn : N.SmallBoundaryTurning delta r) (halpha : 100 * delta / q ≤ alpha)
    (harea : intrinsicAnnulusArea N.metric < mu)
    (hbudget : max K 0 * mu + delta ≤ Real.pi / 2)
    (hmodel : Real.sqrt (max K 1) * q ≤ 1 / 2)
    (hareaLoss : intrinsicAnnulusArea N.metric < (1 - delta) ^ 2 * h * (q / 10))
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hpV : IsPreconnected V) (hbV : ¬ Bornology.IsBounded V) (hUV : Disjoint U V)
    (hcover : U ∪ V = (frontier U)ᶜ) (hfront : frontier U = frontier V)
    (hsub : closure U ⊆ standardAnnulusDomain)
    {a b l u : ℝ} (hal : a ≤ l) (hlu : l < u) (hub : u ≤ b)
    (hperiod : b - a < rampPeriod) (hlength : intrinsicBoundaryLength N.metric 1 l u = q)
    {beta : ℝ → AnnulusCoordinates} (hbeta : ContDiff ℝ ∞ beta)
    {T : ℝ} (hT : 0 < T) (hTh : T ≤ h) (hbetaInj : InjOn beta (Icc 0 T))
    (hends : (beta 0 = intrinsicAnnulusBoundary 1 a ∧
        beta T = intrinsicAnnulusBoundary 1 b) ∨
      (beta 0 = intrinsicAnnulusBoundary 1 b ∧ beta T = intrinsicAnnulusBoundary 1 a))
    (hbetaInside : ∀ t ∈ Ioo 0 T, 1 < ‖beta t‖)
    (hbetaGeo : N.metric.IsGeodesicOn beta (Icc 0 T))
    (hbetaUnit0 : N.metric.inner (beta 0) (deriv beta 0) (deriv beta 0) = 1)
    (hfU : frontier U = intrinsicAnnulusBoundary 1 '' Icc a b ∪ beta '' Icc 0 T)
    (e : AnnulusCoordinates → AnnulusCoordinates) (he : ContDiff ℝ ∞ e)
    (normal : ℝ → AnnulusCoordinates) (annularHeight : ℝ → ℝ)
    (hbase : ∀ p ∈ Ioo a b, e !₂[p, 0] = intrinsicAnnulusBoundary 1 p)
    (hderiv : ∀ p ∈ Ioo a b, HasDerivAt (fun t => e !₂[p, t]) (normal p) 0)
    (hunit0 : ∀ p ∈ Ioo a b,
      N.metric.inner (intrinsicAnnulusBoundary 1 p) (normal p) (normal p) = 1)
    (horth : ∀ p ∈ Ioo a b, N.metric.inner (intrinsicAnnulusBoundary 1 p)
      (deriv (intrinsicAnnulusBoundary 1) p) (normal p) = 0)
    (hinward : ∀ p ∈ Ioo a b, 0 < inner ℝ (intrinsicAnnulusBoundary 1 p) (normal p))
    (hAnn : ∀ p ∈ Ioo a b, 0 < annularHeight p ∧
      (annularHeight p = h ∨ ‖e !₂[p, annularHeight p]‖ = 1 ∨
        ‖e !₂[p, annularHeight p]‖ = 2))
    (hgeo : ∀ p ∈ Ioo a b,
      N.metric.IsGeodesicOn (fun t => e !₂[p, t]) (Icc 0 (annularHeight p)))
    (hmetric : ∀ p ∈ Ioo a b,
      intrinsicGeodesicCurvature N.metric N.connection 1 p ≤ alpha →
      ∀ t ∈ Icc 0 (annularHeight p), ∀ v : AnnulusCoordinates,
        (1 - delta) ^ 2 *
          (intrinsicBoundarySpeed N.metric 1 p ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
          N.metric.inner (e !₂[p, t])
            (fderiv ℝ e !₂[p, t] v) (fderiv ℝ e !₂[p, t] v)) :
    ∃ p ∈ Ioo l u, ∃ w ∈ Icc a b, ∃ s ∈ Ioc 0 h,
      s ≤ annularHeight p ∧ InjOn (fun t => e !₂[p, t]) (Icc 0 s) ∧
      (∀ t ∈ Ioo 0 s, e !₂[p, t] ∈ U) ∧ e !₂[p, s] = intrinsicAnnulusBoundary 1 w ∧
      LinearIndependent ℝ
        (![deriv (intrinsicAnnulusBoundary 1) w, deriv (fun t => e !₂[p, t]) s] :
          Fin 2 → AnnulusCoordinates) := by
  classical
  have hab : a < b := hal.trans_lt (hlu.trans_le hub)
  have hlocal : Ioo l u ⊆ Ioo a b := fun _ hp => ⟨hal.trans_lt hp.1, hp.2.trans_le hub⟩
  have hc : 0 < 1 - delta := by linarith
  have hsmall : max K 0 * intrinsicAnnulusArea N.metric < Real.pi := by
    have hscaled := mul_le_mul_of_nonneg_left harea.le (le_max_right K 0)
    linarith [Real.pi_pos]
  have hcircleInj := m64Intrinsic_boundary_injOn_short_arc hperiod
  have hcircle : intrinsicAnnulusBoundary 1 '' Icc a b ⊆ frontier U := by
    rw [hfU]
    exact subset_union_left
  have havoid : ∀ p ∈ Ioo a b, intrinsicAnnulusBoundary 1 p ∉ beta '' Icc 0 T := by
    rintro p hp ⟨t, ht, hpoint⟩
    have hpa : intrinsicAnnulusBoundary 1 p ≠ intrinsicAnnulusBoundary 1 a := by
      intro heq
      exact hp.1.ne' (hcircleInj (Ioo_subset_Icc_self hp) ⟨le_rfl, hab.le⟩ heq)
    have hpb : intrinsicAnnulusBoundary 1 p ≠ intrinsicAnnulusBoundary 1 b := by
      intro heq
      exact hp.2.ne (hcircleInj (Ioo_subset_Icc_self hp) ⟨hab.le, le_rfl⟩ heq)
    by_cases ht0 : t = 0
    · subst t
      rcases hends with h | h
      · exact hpa (hpoint.symm.trans h.1)
      · exact hpb (hpoint.symm.trans h.1)
    by_cases htT : t = T
    · subst t
      rcases hends with h | h
      · exact hpb (hpoint.symm.trans h.2)
      · exact hpa (hpoint.symm.trans h.2)
    have hn := hbetaInside t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 htT⟩
    rw [hpoint, m64Intrinsic_inner_boundary_norm] at hn
    exact (lt_irrefl (1 : ℝ)) hn
  obtain ⟨f, hf, _, hcontact, hray⟩ :=
    m64Intrinsic_exists_embedded_regional_contact_times N hK hsmall hcircleInj
      (isCompact_Icc.image hbeta.continuous) havoid hU hV hpV hbV hUV hcover
      hfU hfront.symm hsub e he normal hbase hderiv hinward hunit0 hh annularHeight hAnn hgeo
  obtain ⟨Good, hGood, _, hGoodAE, _, _, htransverse⟩ :=
    m64Intrinsic_exists_transverse_retained_bases e he
      (m64Intrinsic_contDiff_boundary 1) MeasurableSet.univ
  let H : ℝ → ℝ := Good.piecewise f 0
  have hH : Measurable H := hf.piecewise hGood measurable_const
  have hHeq (p : ℝ) (hp : p ∈ Good) : H p = f p := piecewise_eq_of_mem Good f 0 hp
  have hHzero (p : ℝ) (hp : p ∉ Good) : H p = 0 := piecewise_eq_of_notMem Good f 0 hp
  have hHnonneg (p : ℝ) (hp : p ∈ Ioo a b) : 0 ≤ H p := by
    by_cases hg : p ∈ Good
    · rw [hHeq p hg]
      exact (hcontact p hp).1.le
    · rw [hHzero p hg]
  have hHle (p : ℝ) (hp : p ∈ Ioo a b) : H p ≤ f p := by
    by_cases hg : p ∈ Good
    · rw [hHeq p hg]
    · rw [hHzero p hg]
      exact (hcontact p hp).1.le
  have hHann (p : ℝ) (hp : p ∈ Ioo a b) : H p ≤ annularHeight p :=
    (hHle p hp).trans (hcontact p hp).2.2.1
  have hHcap (p : ℝ) (hp : p ∈ Ioo a b) : H p ≤ h :=
    (hHle p hp).trans (hcontact p hp).2.1
  have hHgood (p t : ℝ) (ht : 0 < t) (htH : t ≤ H p) : p ∈ Good := by
    by_contra hp
    rw [hHzero p hp] at htH
    exact (not_lt_of_ge htH) ht
  have hprefix (p : ℝ) (hp : p ∈ Ioo a b) {s : ℝ} (hs : s ≤ H p) :
      ∀ t ∈ Ioo 0 s, e !₂[p, t] ∈ U := by
    intro t ht
    exact (hcontact p hp).2.2.2.1 t ⟨ht.1, ht.2.trans_le (hs.trans (hHle p hp))⟩
  have hclosed (p : ℝ) (hp : p ∈ Ioo a b) (t : ℝ) (ht : t ∈ Icc 0 (H p)) :
      e !₂[p, t] ∈ closure U := by
    by_cases ht0 : t = 0
    · rw [ht0, hbase p hp]
      exact frontier_subset_closure (hcircle (mem_image_of_mem _ (Ioo_subset_Icc_self hp)))
    by_cases htf : t = f p
    · rw [htf]
      exact (hcontact p hp).2.2.2.2.1
    exact subset_closure ((hcontact p hp).2.2.2.1 t
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne (ht.2.trans (hHle p hp)) htf⟩)
  have hbetaUnit : ∀ t ∈ Icc 0 T,
      N.metric.inner (beta t) (deriv beta t) (deriv beta t) = 1 := by
    have hu := m64Intrinsic_geodesic_velocity_unit N hT hbetaGeo Subset.rfl
      (by simpa only [m64Intrinsic_curveVelocity_eq_deriv] using hbetaUnit0)
    simpa only [m64Intrinsic_curveVelocity_eq_deriv] using hu
  by_contra hno
  apply m64Intrinsic_no_inner_contact_regional_capacity N hK hdelta hdeltaSmall hq hqr hh hhq
    hturn halpha harea hbudget hmodel hareaLoss hU hV hpV hbV hUV hcover hfront hsub
    hal hlu hub hperiod hlength hbeta hT.le hTh hbetaInj hbetaUnit hfU e he normal hH
    hGood hGoodAE
    (fun p hp hg => by rw [hHeq p hg]; exact (hcontact p (hlocal hp)).1)
    (fun p hp => hHnonneg p (hlocal hp)) (fun p hp => hHcap p (hlocal hp))
    (fun p hp => hbase p (hlocal hp)) (fun p hp => hderiv p (hlocal hp))
    (fun p hp => hunit0 p (hlocal hp)) (fun p hp => horth p (hlocal hp))
    (fun p hp => hinward p (hlocal hp))
    (fun p hp t ht => hgeo p (hlocal hp) t ⟨ht.1, ht.2.trans (hHann p (hlocal hp))⟩)
    (fun p hp => (hray p (hlocal hp)).mono (Icc_subset_Icc_right (hHle p (hlocal hp))))
    (fun p hp => hclosed p (hlocal hp))
  · intro p hp hk t ht
    have hpP := hlocal hp
    have hnle : 1 ≤ ‖e !₂[p, t]‖ := (hsub (hclosed p hpP t ⟨ht.1.le, ht.2⟩)).1
    by_contra hn
    have hnorm : ‖e !₂[p, t]‖ = 1 := le_antisymm (le_of_not_gt hn) hnle
    have hnot : e !₂[p, t] ∉ U := by
      intro hu
      have hs := (m64Intrinsic_open_region_strictly_inside_annulus hU hsub _ hu).1
      rw [hnorm] at hs
      exact (lt_irrefl (1 : ℝ)) hs
    have hfrontier : e !₂[p, t] ∈ frontier U := by
      rw [frontier, hU.interior_eq]
      exact ⟨hclosed p hpP t ⟨ht.1.le, ht.2⟩, hnot⟩
    have hpoint : ∃ w ∈ Icc a b, e !₂[p, t] = intrinsicAnnulusBoundary 1 w := by
      rw [hfU] at hfrontier
      rcases hfrontier with ⟨w, hw, heq⟩ | ⟨s, hs, heq⟩
      · exact ⟨w, hw, heq.symm⟩
      by_cases hs0 : s = 0
      · subst s
        rcases hends with hd | hd
        · exact ⟨a, ⟨le_rfl, hab.le⟩, heq.symm.trans hd.1⟩
        · exact ⟨b, ⟨hab.le, le_rfl⟩, heq.symm.trans hd.1⟩
      by_cases hsT : s = T
      · subst s
        rcases hends with hd | hd
        · exact ⟨b, ⟨hab.le, le_rfl⟩, heq.symm.trans hd.2⟩
        · exact ⟨a, ⟨le_rfl, hab.le⟩, heq.symm.trans hd.2⟩
      have hsNorm := hbetaInside s
        ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hsT⟩
      rw [heq, hnorm] at hsNorm
      exact ((lt_irrefl (1 : ℝ)) hsNorm).elim
    obtain ⟨w, hw, hpoint⟩ := hpoint
    have hregular : Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[p, t]) := by
      have hi := m64Intrinsic_normal_map_injective_of_metric_lower N hc
        (x := !₂[p, t]) (by
          simpa only [Matrix.cons_val_zero] using
            hmetric p hpP hk t ⟨ht.1.le, ht.2.trans (hHann p hpP)⟩)
      simpa only [TangentSpace, mfderiv_eq_fderiv] using hi
    have hind : LinearIndependent ℝ
        (![deriv (intrinsicAnnulusBoundary 1) w, deriv (fun s => e !₂[p, s]) t] :
          Fin 2 → AnnulusCoordinates) := by
      rw [m64Intrinsic_coordinate_normal_ray_deriv (he.differentiable (by simp) !₂[p, t])]
      exact htransverse p (hHgood p t ht.1 ht.2) t w hpoint hregular
    exact hno ⟨p, hp, w, hw, t, ⟨ht.1, ht.2.trans (hHcap p hpP)⟩,
      ht.2.trans (hHann p hpP),
      (hray p hpP).mono (Icc_subset_Icc_right (ht.2.trans (hHle p hpP))),
      hprefix p hpP ht.2, hpoint, hind⟩
  · intro p hp hpos hlt
    have hg := hHgood p (H p) hpos le_rfl
    have hd := hcontact p (hlocal hp)
    rw [hHeq p hg] at hlt ⊢
    exact hd.2.2.2.2.2.resolve_left hlt.ne
  · intro p hp hk t ht
    exact hmetric p (hlocal hp) hk t ⟨ht.1, ht.2.trans (hHann p (hlocal hp))⟩

end PoincareConjecture
