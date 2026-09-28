import PoincareConjecture.Proofs.M25.Mathlib.RadialBallChart
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.TwoCapInnerChart
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.TwoCapOuterChart
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.TwoCapRadialMatching
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SphereRadialExtension
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.BoundedSphereAtlas












set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D




theorem capCertificates_exists_sphere_diffeomorph_of_services
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C1 C2 : ClosedModelCapData g)
    (hkind1 : C1.model_kind = CapModelKind.euclidean)
    (hkind2 : C2.model_kind = CapModelKind.euclidean)
    (hcompact : IsCompact (C1.carrier ∪ C2.carrier)) :
    let U : TopologicalSpace.Opens M :=
      ⟨C1.carrier ∪ C2.carrier, C1.carrier_open.union C2.carrier_open⟩
    Nonempty (Diffeomorph (𝓡 3) (𝓡 3) U UnitThreeSphere ∞) := by
  classical
  let L := C1.epsilon⁻¹
  let Y := C1.carrier ∪ C2.carrier
  let N := C1
  let Cut : ℝ → Set M := fun s => C1.carrier \ N.region s L
  let V : ℝ → Set M := fun s => interior (Cut s)
  obtain ⟨v, hv, _, hdata⟩ :=
    capCertificates_exists_second_buffered_ball_chart hS C1 C2 hkind2 hcompact
  let c := (v + L) / 2
  let h := (L - v) / 4
  let a := c - h * (3 / 4)
  let b := c - h * (1 / 2)
  rcases hdata with ⟨hh, hleft, hright, hva, hab, hbL, Phi2, e, S, J,
    _, _, _, _, _, _, hpsi, _, _, hJs, hJt, hJ, hJi, _, _, hcover,
    hoverlap, _, hJray, _⟩
  change 0 < h at hh
  change v < c - h at hleft
  change c + h < L at hright
  change v < a at hva
  change a < b at hab
  change b < L at hbL
  change J.source = Y \ Cut a at hJs
  change V b ∪ J.source = Y at hcover
  change V b ∩ J.source = N.region a b at hoverlap
  obtain ⟨Phi, A, r0, sigma, I, hr0, hss, hst, hsigma, _, hsmono, hsderiv,
    _, _, hIs, hIt, hI, hIi, _, _, hIannulus, hIray⟩ :=
    capCertificate_exists_radial_lower_cut_chart_of_services
      hS hD C1 hkind1 hv hva hab hbL
  have hsmem {s : ℝ} (hs : s ∈ Ioo v L) : s ∈ sigma.source := hss.symm ▸ hs
  have hspos {s : ℝ} (hs : s ∈ Ioo v L) : 0 < sigma s := by
    have hr : r0 < sigma s := by
      simpa only [hst, mem_Ioi] using sigma.map_source (hsmem hs)
    exact hr0.trans hr
  have ha : a ∈ Ioo v L := ⟨hva, hab.trans hbL⟩
  have hb : b ∈ Ioo v L := ⟨hva.trans hab, hbL⟩
  have hsa : 0 < sigma a := hspos ha
  have hsb : 0 < sigma b := hspos hb
  have hsab : sigma a < sigma b := hsmono (hsmem ha) (hsmem hb) hab
  let Rminus := 4 / sigma a
  have hMinus : 0 < Rminus := div_pos (by norm_num) hsa
  have hproduct : 4 < sigma b * Rminus := by
    change 4 < sigma b * (4 / sigma a)
    rw [← mul_div_assoc, lt_div_iff₀ hsa]
    nlinarith
  obtain ⟨pole, hpole⟩ :=
    (NormedSpace.sphere_nonempty (E := EuclideanSpace ℝ (Fin 4))).mpr
      (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨B, c0, c1, _, _, _, _, _, _, _, hc0t, hc1t, hccover,
    hc0, hc1, hci0, hci1, hcts, hctf⟩ :=
    exists_bounded_threeSphere_stereographic_atlas ⟨pole, hpole⟩ hsb hMinus hproduct
  let O := A.trans B
  let OD : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞ :=
    O.toContinuousLinearEquiv.toDiffeomorph
  let R := S.radial (3 / 4)
  let m := S.radial (3 / 8)
  let mid := S.radial (1 / 2)
  obtain ⟨tau, k, hm, hmMid, hMidR, _, _, htaus, htaut, htau, htaui,
    _, htaumono, _, htau0, _, hmatch, _, _, _, htaum, hcenter, hicenter, _, _⟩ :=
    S.exists_inward_matching_radial_chart hpsi sigma hh hleft hright hr0
      (show (0 : ℝ) < 4 by norm_num) hss hst hsigma hsderiv
  have hmR : m < R := hmMid.trans hMidR
  have hR : 0 < R := hm.trans hmR
  have hmSource : m ∈ tau.source := by
    rw [htaus]
    exact ⟨(neg_neg_of_pos hR).trans hm, hmR⟩
  have hnS : tau m < Rminus := (htaut ▸ tau.map_source hmSource).2
  obtain ⟨P, hPs, hPt, hPf, _, hP, hPi, _, _, _, _, _, _, _⟩ :=
    tau.exists_smooth_radialBall_chart (E := E3) (R := R) (S := Rminus)
      (m := m) (n := tau m) (k := k) hR hMinus hm hmR htaum hnS
      htaus htaut htau htaui (htaumono.mono Ioo_subset_Icc_self) htau0
      (fun r hr => hcenter r ⟨(neg_nonpos.mpr hm.le).trans hr.1, hr.2⟩)
      (fun r hr => hicenter r ⟨(neg_nonpos.mpr htaum.le).trans hr.1, hr.2⟩)
  have hPM : ContMDiffOn (𝓡 3) (𝓡 3) ∞ P P.source := hP.contMDiffOn
  have hPiM : ContMDiffOn (𝓡 3) (𝓡 3) ∞ P.symm P.target := hPi.contMDiffOn
  obtain ⟨D⟩ := hD S.boundary_map
  obtain ⟨d, hdnorm, hdinorm, _, _, _, hdiouter, _, _⟩ :=
    D.exists_normPreserving_radialExtension hm hmMid

  let Jd := J.transHomeomorph d.symm.toHomeomorph
  have hJdP : Jd.target = P.source := by
    change d ⁻¹' J.target = P.source
    rw [hJt, hPs]
    ext z
    simp only [mem_preimage, mem_ball_zero_iff, hdnorm, R]
  let Jp := Jd.trans' P hJdP
  let K := Jp.transHomeomorph OD.toHomeomorph
  have hKs : K.source = J.source := rfl
  have hKt : K.target = ball 0 Rminus := by
    change O.symm ⁻¹' P.target = ball 0 Rminus
    rw [hPt]
    ext z
    simp only [mem_preimage, mem_ball_zero_iff, O.symm.norm_map]
  have hKf : (K : M → E3) = (fun x => O (P (d.symm (J x)))) := rfl
  have hKi : (K.symm : E3 → M) = (fun z => J.symm (d (P.symm (O.symm z)))) := rfl
  have hdP {x : M} (hx : x ∈ J.source) : d.symm (J x) ∈ P.source := by
    rw [hPs, mem_ball_zero_iff, hdinorm]
    exact mem_ball_zero_iff.mp (hJt ▸ J.map_source hx)
  have hK : ContMDiffOn (𝓡 3) (𝓡 3) ∞ K K.source := by
    change ContMDiffOn (𝓡 3) (𝓡 3) ∞ (fun x => OD (P (d.symm (J x)))) J.source
    exact OD.contMDiff.comp_contMDiffOn
      (hPM.comp (d.symm.contMDiff.comp_contMDiffOn hJ) (fun _ hx => hdP hx))
  have hOP {z : E3} (hz : z ∈ K.target) : O.symm z ∈ P.target := by
    rw [hPt, mem_ball_zero_iff, O.symm.norm_map]
    exact mem_ball_zero_iff.mp (hKt ▸ hz)
  have hdJ {z : E3} (hz : z ∈ K.target) : d (P.symm (O.symm z)) ∈ J.target := by
    rw [hJt, mem_ball_zero_iff, hdnorm]
    exact mem_ball_zero_iff.mp (hPs ▸ P.map_target (hOP hz))
  have hKiM : ContMDiffOn (𝓡 3) (𝓡 3) ∞ K.symm K.target := by
    rw [hKi]
    exact hJi.comp (d.contMDiff.comp_contMDiffOn
      (hPiM.comp OD.symm.contMDiff.contMDiffOn (fun _ hz => hOP hz)))
      (fun _ hz => hdJ hz)
  have hKray (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Ico (1 / 2 : ℝ) (3 / 4)) :
      N.coordinate_map (q, c - h * t) ∈ K.source ∧
      K (N.coordinate_map (q, c - h * t)) =
        (4 / sigma (c - h * t)) • B (A q.val) := by
    have ht' : t ∈ Ico (1 / 4 : ℝ) 1 := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hpos : 0 < S.radial t := S.radial_pos t ht'
    have hmid : mid ≤ S.radial t :=
      S.radial_strictMono.monotoneOn (by norm_num) ht' ht.1
    obtain ⟨hx, hJx⟩ := hJray q t ⟨by linarith [ht.1], ht.2⟩
    change J (N.coordinate_map (q, c - h * t)) = S.radial t • (S.boundary_map q).val at hJx
    refine ⟨hKs.symm ▸ hx, ?_⟩
    simp only [hKf, hJx, hdiouter q (S.radial t) hmid, hPf]
    have hnorm : ‖S.radial t • q.val‖ = S.radial t := by
      rw [norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp q.property,
        mul_one, abs_of_pos hpos]
    rw [hnorm, smul_smul, div_mul_cancel₀ _ hpos.ne', hmatch t ⟨ht.1, ht.2.le⟩]
    exact O.map_smul _ _
  have hcoverAmbient : I.source ∪ K.source = Y := by
    rw [hIs, hKs]
    exact hcover
  have hoverlapAmbient : I.source ∩ K.source = N.region a b := by
    rw [hIs, hKs]
    exact hoverlap
  have htransitionSource : (I.symm.trans K).source =
      {z : E3 | sigma a < ‖z‖ ∧ ‖z‖ < sigma b} := by
    have heq : (I.symm.trans K).source = I '' (I.source ∩ K.source) := by
      ext z
      change (z ∈ I.target ∧ I.symm z ∈ K.source) ↔ z ∈ I '' (I.source ∩ K.source)
      constructor
      · rintro ⟨hz, hx⟩
        exact ⟨I.symm z, ⟨I.map_target hz, hx⟩, I.right_inv hz⟩
      · rintro ⟨x, ⟨hxI, hxK⟩, rfl⟩
        exact ⟨I.map_source hxI, by simpa only [I.left_inv hxI] using hxK⟩
    rw [heq, hoverlapAmbient]
    exact hIannulus
  have htransitionFormula (z : E3) (hz : z ∈ (I.symm.trans K).source) :
      K (I.symm z) = (4 / ‖z‖ ^ 2) • B z := by
    have hzann : z ∈ I '' N.region a b := by
      rw [hIannulus]
      exact htransitionSource ▸ hz
    obtain ⟨x, hx, hIx⟩ := hzann
    let q := (N.coordinate_inverse x).1
    let s := (N.coordinate_inverse x).2
    have hs : s ∈ Ioo a b := hx.2
    have hxmap : x = N.coordinate_map (q, s) := (N.coordinate_map_inverse hx.1).symm
    have hxI : x ∈ I.source := (hoverlapAmbient.symm ▸ hx).1
    have hIz : I.symm z = x := by rw [← hIx, I.left_inv hxI]
    have hzrad : z = sigma s • A q.val := by
      rw [← hIx, hxmap]
      exact (hIray q s hs).2.1
    have hspos' : 0 < sigma s := hspos ⟨hva.trans hs.1, hs.2.trans hbL⟩
    have hnorm : ‖z‖ = sigma s := by
      rw [hzrad, norm_smul, Real.norm_eq_abs, A.norm_map,
        mem_sphere_zero_iff_norm.mp q.property, mul_one, abs_of_pos hspos']
    let t := (c - s) / h
    have ht : t ∈ Ico (1 / 2 : ℝ) (3 / 4) := by
      constructor
      · apply le_of_lt
        apply (lt_div_iff₀ hh).2
        have hsupper : s < c - h * (1 / 2) := hs.2
        linarith
      · apply (div_lt_iff₀ hh).2
        have hslower : c - h * (3 / 4) < s := hs.1
        linarith
    have hheight : c - h * t = s := by dsimp only [t]; field_simp [hh.ne']; ring
    have hKx := (hKray q t ht).2
    rw [hheight] at hKx
    rw [hIz, hxmap, hKx, hnorm, hzrad, B.map_smul, smul_smul]
    congr 1
    field_simp [hspos'.ne']

  let U : TopologicalSpace.Opens M :=
    ⟨C1.carrier ∪ C2.carrier, C1.carrier_open.union C2.carrier_open⟩
  let hU : Nonempty U := ⟨⟨(Phi.symm 0).val, Or.inl (Phi.symm 0).property⟩⟩
  have restrictChart (e' : OpenPartialHomeomorph M E3)
      (hsub : e'.source ⊆ (U : Set M))
      (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e' e'.source)
      (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e'.symm e'.target) :
      let er := e'.subtypeRestr hU
      er.source = (Subtype.val : U → M) ⁻¹' e'.source ∧
      er.target = e'.target ∧
      (er : U → E3) = (fun x => e' x.val) ∧
      (∀ z ∈ er.target, (er.symm z).val = e'.symm z) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ er er.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ er.symm er.target := by
    let er := e'.subtypeRestr hU
    have hrs : er.source = (Subtype.val : U → M) ⁻¹' e'.source :=
      e'.subtypeRestr_source hU
    have hrt : er.target = e'.target := by
      change (e'.subtypeRestr hU).target = e'.target
      rw [OpenPartialHomeomorph.subtypeRestr_def, OpenPartialHomeomorph.trans_target,
        U.openPartialHomeomorphSubtypeCoe_target]
      exact inter_eq_left.mpr (fun z hz => hsub (e'.map_target hz))
    have hri (z : E3) (hz : z ∈ er.target) : (er.symm z).val = e'.symm z :=
      e'.subtypeRestr_symm_apply hU hz
    refine ⟨hrs, hrt, rfl, hri, ?_, ?_⟩
    · exact he.comp contMDiff_subtype_val.contMDiffOn (fun x hx => hrs ▸ hx)
    · have hcomp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ er.symm) er.target :=
        (hei.mono (fun _ hz => hrt ▸ hz)).congr hri
      intro z hz
      exact (ContMDiffWithinAt.subtypeVal_comp_iff U er.symm er.target z).mp (hcomp z hz)
  let e0 := I.subtypeRestr hU
  let e1 := K.subtypeRestr hU
  obtain ⟨he0s, he0t, he0f, he0i, he0, hei0⟩ := restrictChart I
    (fun x hx => by change x ∈ Y; rw [← hcoverAmbient]; exact Or.inl hx) hI hIi
  obtain ⟨he1s, he1t, he1f, _, he1, hei1⟩ := restrictChart K
    (fun x hx => by change x ∈ Y; rw [← hcoverAmbient]; exact Or.inr hx) hK hKiM
  have hecover : e0.source ∪ e1.source = univ := by
    rw [he0s, he1s, ← preimage_union, hcoverAmbient]
    exact eq_univ_of_forall (fun x => x.property)
  have hesource : (e0.symm.trans e1).source = (I.symm.trans K).source := by
    ext z
    change (z ∈ e0.target ∧ e0.symm z ∈ e1.source) ↔
      (z ∈ I.target ∧ I.symm z ∈ K.source)
    constructor
    · rintro ⟨hz, hx⟩
      refine ⟨he0t ▸ hz, ?_⟩
      have hx' : e0.symm z ∈ (Subtype.val : U → M) ⁻¹' K.source := he1s ▸ hx
      change (e0.symm z).val ∈ K.source at hx'
      rwa [he0i z hz] at hx'
    · rintro ⟨hz, hx⟩
      have hz' : z ∈ e0.target := he0t.symm ▸ hz
      refine ⟨hz', ?_⟩
      rw [he1s]
      change (e0.symm z).val ∈ K.source
      rw [he0i z hz']
      exact hx
  have hfour : 4 / Rminus = sigma a := by
    dsimp only [Rminus]
    field_simp [hsa.ne']
  have htrans : OpenPartialHomeomorph.EqOnSource (e0.symm.trans e1) (c0.symm.trans c1) := by
    refine ⟨?_, ?_⟩
    · rw [hesource, htransitionSource, hcts, hfour]
    · intro z hz
      have hzI : z ∈ e0.target := hz.1
      change K (e0.symm z).val = c1 (c0.symm z)
      rw [he0i z hzI]
      have hz' : z ∈ (I.symm.trans K).source := hesource ▸ hz
      rw [htransitionFormula z hz']
      apply (hctf z ?_).symm
      rw [hcts, hfour]
      exact htransitionSource ▸ hz'
  obtain ⟨F, _, _, _, _⟩ :=
    OpenPartialHomeomorph.m25_exists_diffeomorph_of_chart_transition e0 e1 c0 c1
      hecover hccover (he0t.trans (hIt.trans hc0t.symm))
      (he1t.trans (hKt.trans hc1t.symm)) he0 he1 hei0 hei1 hc0 hc1 hci0 hci1 htrans
  exact ⟨F⟩

end PoincareConjecture.M25.Topology3D
