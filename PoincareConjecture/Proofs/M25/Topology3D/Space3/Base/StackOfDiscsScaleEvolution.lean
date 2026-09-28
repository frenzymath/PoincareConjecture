import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsScaleCylinder
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SouthernSphereChart











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace NNReal Topology

namespace PoincareConjecture.M25.Topology3D

variable {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}


theorem exists_stackCapScale_tracking_widths (C : SurgeryCapTag psi u)
    (lambda : ℝ) (hlambda : 0 < lambda) (hsmall : lambda < C.scale)
    (rho : ℝ × E3 → ℝ)
    (hnear : ∀ᶠ p in 𝓝ˢ ((fun p : ℝ × UnitTwoSphere =>
      (p.1, stackCapScaleCap C lambda p.1 p.2)) ''
        (Icc (-1 : ℝ) 2 ×ˢ {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0})),
      rho p = 1) :
    ∃ o w : ℝ, 0 < o ∧ o ≤ C.overlapWidth ∧ 0 < w ∧ w ≤ C.collarWidth ∧
      (∀ t ∈ Icc (-1 : ℝ) 2, ∀ q : UnitTwoSphere,
        (heightCoordinates (q : E3)).2 < o →
          rho (t, stackCapScaleCap C lambda t q) = 1) ∧
      ∀ t ∈ Icc (-1 : ℝ) 2, ∀ x : E2, ‖x‖ ≤ 1 / 8 →
        ∀ z : ℝ, |z| < w → rho (t, C.tube (x,
          C.cutHeight + C.sign * C.removal +
            (stackCapScale C.scale lambda t / C.scale) *
              (-C.sign * C.scale + C.beta * z))) = 1 := by
  obtain ⟨V, hV, hKV, hVrho⟩ := eventually_nhdsSet_iff_exists.mp hnear
  have hcap := (stackCapScaleCap_spec C lambda hlambda hsmall).1
  let T := Icc (-1 : ℝ) 2
  let : CompactSpace T := isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact T)
  let f : T × UnitTwoSphere → ℝ × E3 := fun p =>
    (p.1, stackCapScaleCap C lambda p.1 p.2)
  have hcapc : Continuous (fun p : ℝ × UnitTwoSphere =>
      stackCapScaleCap C lambda p.1 p.2) := hcap.continuous
  have htime : Continuous (fun p : T × UnitTwoSphere => (p.1 : ℝ)) :=
    (continuous_fst : Continuous (Prod.fst : T × UnitTwoSphere → T)).subtype_val
  have hparams : Continuous (fun p : T × UnitTwoSphere => ((p.1 : ℝ), p.2)) :=
    htime.prodMk (continuous_snd : Continuous (Prod.snd : T × UnitTwoSphere → UnitTwoSphere))
  have hcaprestricted : Continuous (fun p : T × UnitTwoSphere =>
      stackCapScaleCap C lambda (p.1 : ℝ) p.2) :=
    Continuous.comp
      (g := fun p : ℝ × UnitTwoSphere => stackCapScaleCap C lambda p.1 p.2)
      (f := fun p : T × UnitTwoSphere => ((p.1 : ℝ), p.2)) hcapc hparams
  have hf : Continuous f := htime.prodMk hcaprestricted
  have hh : Continuous (fun p : T × UnitTwoSphere =>
      -(heightCoordinates (p.2 : E3)).2) :=
    ((heightCoordinates.continuous.comp (continuous_subtype_val.comp continuous_snd)).snd).neg
  have hhalf : {p : T × UnitTwoSphere | 0 ≤ -(heightCoordinates (p.2 : E3)).2}
      ⊆ f ⁻¹' V := by
    intro p hp
    have hp' : (heightCoordinates (p.2 : E3)).2 ≤ 0 := by
      change 0 ≤ -(heightCoordinates (p.2 : E3)).2 at hp
      linarith only [hp]
    exact hKV ⟨((p.1 : ℝ), p.2), ⟨p.1.2, hp'⟩, rfl⟩
  obtain ⟨o0, ho0, hband⟩ := exists_uniform_upper_level_band _ hh (hV.preimage hf) hhalf
  let D := closedBall (0 : E2) (1 / 8)
  let Z := Icc (-1 : ℝ) 1
  let : CompactSpace D := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E2) (1 / 8))
  let : CompactSpace Z := isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact Z)
  let s := C.cutHeight + C.sign * C.removal
  let g : T × D × Z → ℝ × E3 := fun p =>
    (p.1, C.tube (p.2.1, s + (stackCapScale C.scale lambda p.1 / C.scale) *
      (-C.sign * C.scale + C.beta * p.2.2)))
  have hscale : ContDiff ℝ ∞ (stackCapScale C.scale lambda) :=
    (stackCapScale_spec C.scale lambda hlambda hsmall).1
  have ht : Continuous (fun p : T × D × Z => (p.1 : ℝ)) :=
    (continuous_fst : Continuous (Prod.fst : T × D × Z → T)).subtype_val
  have hx : Continuous (fun p : T × D × Z => (p.2.1 : E2)) :=
    (continuous_snd.fst : Continuous (fun p : T × D × Z => p.2.1)).subtype_val
  have hz : Continuous (fun p : T × D × Z => (p.2.2 : ℝ)) :=
    (continuous_snd.snd : Continuous (fun p : T × D × Z => p.2.2)).subtype_val
  have hcoords : Continuous (fun p : T × D × Z => ((p.2.1 : E2),
      s + (stackCapScale C.scale lambda p.1 / C.scale) *
        (-C.sign * C.scale + C.beta * p.2.2))) :=
    hx.prodMk (continuous_const.add (((hscale.continuous.comp ht).div_const C.scale).mul
      (continuous_const.add (continuous_const.mul hz))))
  have hg : Continuous g := ht.prodMk (C.tube.continuousOn.comp_continuous hcoords (by
    intro p
    apply C.tube_source
    exact ⟨mem_closedBall_zero_iff.mpr
      ((mem_closedBall_zero_iff.mp p.2.1.2).trans (by norm_num)), mem_univ _⟩))
  have hcenter : {p : T × D × Z | (p.2.2 : ℝ) = 0} ⊆ g ⁻¹' V := by
    intro p hp
    let q := southSpherePoint (p.2.1 : E2)
    have hxn : ‖(p.2.1 : E2)‖ ≤ 1 / 8 := mem_closedBall_zero_iff.mp p.2.1.2
    have hcoordsq : heightCoordinates (q : E3) =
        ((p.2.1 : E2), -Real.sqrt (1 - ‖(p.2.1 : E2)‖ ^ 2)) :=
      southSpherePoint_coordinates (p.2.1 : E2) (by linarith only [hxn])
    have hq : (heightCoordinates (q : E3)).2 ≤ 0 := by
      rw [hcoordsq]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)
    have hmodel : C.profile.model q = ((p.2.1 : E2), -1) := by
      have hh := surgeryCapModel_flat_south C.profile.horizontal C.profile.vertical
        C.profile.horizontal_smooth C.profile.vertical_smooth
        (fun z => (C.profile.horizontal_pos z).ne') (fun x => (C.profile.vertical_pos x).ne')
        C.profile.horizontal_far C.profile.vertical_near q
          (by rw [hcoordsq]; dsimp only; linarith) hq
      simpa only [SurgeryCapProfile.model, hcoordsq] using hh
    have heq : g p = ((p.1 : ℝ), stackCapScaleCap C lambda p.1 q) := by
      apply Prod.ext
      · rfl
      · change C.tube ((p.2.1 : E2), s + (stackCapScale C.scale lambda p.1 / C.scale) *
          (-C.sign * C.scale + C.beta * p.2.2)) =
          C.profile.capMap C.tube C.cutHeight C.sign C.removal
            (stackCapScale C.scale lambda p.1) q
        rw [SurgeryCapProfile.capMap_apply, hmodel]
        change (p.2.2 : ℝ) = 0 at hp
        rw [hp]
        congr 1
        apply Prod.ext
        · rfl
        · dsimp only [s]
          field_simp [C.scale_pos.ne']
          ring
    change g p ∈ V
    rw [heq]
    exact hKV ⟨((p.1 : ℝ), q), ⟨p.1.2, hq⟩, rfl⟩
  obtain ⟨w0, hw0, hflatband⟩ :=
    exists_uniform_zero_level_band _ hz (hV.preimage hg) hcenter
  refine ⟨min o0 C.overlapWidth, min w0 C.collarWidth,
    lt_min ho0 C.overlap_pos, min_le_right _ _,
    lt_min hw0 C.collar_pos, min_le_right _ _, ?_, ?_⟩
  · intro t ht q hq
    apply hVrho
    apply hband (⟨t, ht⟩, q)
    have hq' := lt_of_lt_of_le hq (min_le_left o0 C.overlapWidth)
    change -o0 < -(heightCoordinates (q : E3)).2
    linarith
  · intro t ht x hx z hz
    have hz1 : |z| < 1 :=
      hz.trans_le ((min_le_right w0 C.collarWidth).trans C.collar_le)
    have hzmem : z ∈ Z := ⟨(abs_lt.mp hz1).1.le, (abs_lt.mp hz1).2.le⟩
    apply hVrho
    exact hflatband (⟨t, ht⟩, ⟨x, mem_closedBall_zero_iff.mpr hx⟩, ⟨z, hzmem⟩)
      (hz.trans_le (min_le_left _ _))


theorem exists_stackCapScaleEvolution (C : SurgeryCapTag psi u)
    (hpsi : IsCollarEmbedding psi) (K L : Set E3) (hK : IsCompact K) (hL : IsCompact L)
    (gap lambda : ℝ) (hgap : 0 < gap) (hlambda : 0 < lambda)
    (hsmall : lambda < C.scale)
    (hcover : range (fun q => psi (q, 0)) = K ∪ C.cap ∪ L)
    (hseam : C.seam ⊆ K)
    (hKside : ∀ y ∈ K, 0 ≤ C.sign * (inner ℝ (u : E3) y -
      (C.cutHeight + C.sign * C.removal)))
    (hLside : ∀ y ∈ L, gap ≤ C.sign * (inner ℝ (u : E3) y -
      (C.cutHeight + C.sign * C.removal))) :
    let s := C.cutHeight + C.sign * C.removal
    ∃ Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      ∃ S N : Set E3, ∃ d o w : ℝ,
      ContDiff ℝ ∞ (fun p : ℝ × E3 => Phi p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E3 => (Phi p.1).symm p.2) ∧
      (∀ y, Phi 0 y = y) ∧ IsCompact S ∧ IsOpen N ∧ C.seam ⊆ N ∧
      0 < d ∧ d < lambda / 4 ∧ d < C.scale * C.overlapWidth ∧ d < gap / 4 ∧
      N ∩ K = (fun p : E2 × ℝ => C.tube (p.1, s + C.sign * p.2)) ''
        (sphere (0 : E2) 1 ×ˢ Ico 0 d) ∧
      S ⊆ (C.tube.target ∩
        {y | C.sign * (inner ℝ (u : E3) y - s) < gap / 2}) \ ((K \ N) ∪ L) ∧
      (∀ t, tsupport (fun y => Phi t y - y) ⊆ S) ∧
      (∀ t, tsupport (fun y => (Phi t).symm y - y) ⊆ S) ∧
      (∀ t y, y ∉ S → Phi t y = y ∧ (Phi t).symm y = y) ∧
      (∀ t, Phi t '' K = K ∧ (Phi t).symm '' K = K) ∧
      (∀ t y, y ∈ C.seam ∪ L → Phi t y = y ∧ (Phi t).symm y = y) ∧
      0 < o ∧ o ≤ C.overlapWidth ∧ 0 < w ∧ w ≤ C.collarWidth ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2, ∀ q : UnitTwoSphere,
        (heightCoordinates (q : E3)).2 < o →
          Phi t (C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q) =
            stackCapScaleCap C lambda t q) ∧
      (∀ t ∈ Ioo (-1 : ℝ) 2,
        Phi t '' C.cap = stackCapScaleCap C lambda t ''
          {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
        (Phi t).symm '' (stackCapScaleCap C lambda t ''
          {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}) = C.cap) ∧
      ∀ t ∈ Ioo (-1 : ℝ) 2, ∀ x : E2, ‖x‖ ≤ 1 / 8 →
        ∀ z : ℝ, |z| < w →
          Phi t (C.tube (x, s - C.sign * C.scale + C.beta * z)) =
            C.tube (x, s + (stackCapScale C.scale lambda t / C.scale) *
              (-C.sign * C.scale + C.beta * z)) := by
  let s := C.cutHeight + C.sign * C.removal
  obtain ⟨d, N, hd, hdl, hdo, hdg, hN, hseamN, hstrip, hclosed, hend⟩ :=
    exists_stackCapCoreNeighborhood C hpsi K L hK hL gap lambda hgap hlambda
      hcover hseam hKside hLside
  obtain ⟨_, _, rho, hrho, hrhoc, hrhoU, hnear, _, hV, hVc⟩ :=
    exists_stackCapScaleCutoff C lambda hlambda hsmall K L N hK hL hN hseamN
      gap hgap hKside hLside
  let e := stackCapScaleChart C lambda hlambda
  let V := fun p => rho p • chartTimeField e p
  obtain ⟨A, B, hA, hB⟩ := clockField_bounds V hV hVc
  let Phi : ℝ → Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞ :=
    fun t => clockEvolutionDiffeomorph V hA hB hV hVc 0 t
  let S := Prod.snd '' tsupport rho
  have hSc : IsCompact S := hrhoc.isCompact.image continuous_snd
  have hS : S ⊆ (C.tube.target ∩
      {y | C.sign * (inner ℝ (u : E3) y - s) < gap / 2}) \ ((K \ N) ∪ L) := by
    rintro y ⟨p, hp, rfl⟩
    exact (hrhoU hp).2
  have havoid (t : ℝ) (y : E3) (hy : y ∈ (K \ N) ∪ L) : rho (t, y) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hp
    exact (hrhoU hp).2.2 hy
  have hpres := stackCapScaleField_preserves_core C lambda hlambda hsmall
    rho hrho hrhoc K L N d hd hstrip hclosed hend havoid hA hB
  have hsupp (a b : ℝ) :
      tsupport (fun y => clockEvolution V hA hB a b y - y) ⊆ S :=
    closure_minimal ((clockEvolution_support_subset V hA hB a b).trans
      (image_mono (tsupport_smul_subset_left rho (chartTimeField e)))) hSc.isClosed
  have hfix (t : ℝ) (y : E3) (hy : y ∉ S) : Phi t y = y ∧ (Phi t).symm y = y := by
    have hz (r : ℝ) : V (r, y) = 0 := by
      have hr : rho (r, y) = 0 := by
        apply image_eq_zero_of_notMem_tsupport
        intro hp
        exact hy ⟨(r, y), hp, rfl⟩
      change rho (r, y) • _ = 0
      rw [hr, zero_smul]
    exact ⟨clockEvolution_eq_self V hA hB y hz 0 t,
      clockEvolution_eq_self V hA hB y hz t 0⟩
  obtain ⟨o, w, ho, hoOld, hw, hwOld, hcaprho, hflatrho⟩ :=
    exists_stackCapScale_tracking_widths C lambda hlambda hsmall rho hnear
  obtain ⟨_, _, hcapderiv, _, _, hcapzero, _, _, _, _, _, _⟩ :=
    stackCapScaleCap_spec C lambda hlambda hsmall
  have htrack (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) (q : UnitTwoSphere)
      (hq : (heightCoordinates (q : E3)).2 < o) :
      Phi t (C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q) =
        stackCapScaleCap C lambda t q := by
    have hh := clockEvolution_tracks V hA hB (fun r => stackCapScaleCap C lambda r q)
      (s := 0) (by norm_num : (0 : ℝ) ∈ Ioo (-1) 2) (fun r hr => by
        change HasDerivAt _ (rho _ • chartTimeField e _) r
        rw [hcaprho r (Ioo_subset_Icc_self hr) q hq, one_smul]
        exact hcapderiv r q) ht
    change clockEvolution V hA hB 0 t
      (C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q) = _
    simpa only [hcapzero q] using hh
  have himage (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) :
      Phi t '' C.cap = stackCapScaleCap C lambda t ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
    rw [C.cap_eq_image]
    ext y
    constructor
    · rintro ⟨z, ⟨q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, (htrack t ht q (hq.trans_lt ho)).symm⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q,
        ⟨q, hq, rfl⟩, htrack t ht q (hq.trans_lt ho)⟩
  have hflat (t : ℝ) (ht : t ∈ Ioo (-1 : ℝ) 2) (x : E2) (hx : ‖x‖ ≤ 1 / 8)
      (z : ℝ) (hz : |z| < w) :
      Phi t (C.tube (x, s - C.sign * C.scale + C.beta * z)) =
        C.tube (x, s + stackCapScale C.scale lambda t / C.scale *
          (-C.sign * C.scale + C.beta * z)) := by
    let X := heightCoordinates.symm (x, s - C.sign * C.scale + C.beta * z)
    let gamma := fun r => C.tube (x, s + stackCapScale C.scale lambda r / C.scale *
      (-C.sign * C.scale + C.beta * z))
    obtain ⟨hforward, _, hsource, _, he, _, htime⟩ := stackCapScaleChart_spec C lambda hlambda
    have hX (r : ℝ) : (r, X) ∈ e.source := by
      rw [hsource]
      apply C.tube_source
      refine ⟨?_, mem_univ _⟩
      dsimp only [X]
      rw [heightCoordinates.apply_symm_apply]
      exact mem_closedBall_zero_iff.mpr (hx.trans (by norm_num))
    have hformula (r : ℝ) : (e (r, X)).2 = gamma r := by
      rw [hforward]
      dsimp only [X, gamma]
      rw [heightCoordinates.apply_symm_apply]
      congr 2
      dsimp only [s]
      ring
    have hgamma (r : ℝ) (hr : r ∈ Ioo (-1 : ℝ) 2) :
        HasDerivAt gamma (V (r, gamma r)) r := by
      have hd' := chartTimeField_track e he (fun p _ => htime p) r X (hX r)
      change HasDerivAt gamma (rho (r, gamma r) • chartTimeField e (r, gamma r)) r
      rw [hflatrho r (Ioo_subset_Icc_self hr) x hx z hz, one_smul]
      simpa only [hformula] using hd'
    have hstart := (stackCapScale_spec C.scale lambda hlambda hsmall).2.2.2.1 0 le_rfl
    have hgamma0 : gamma 0 = C.tube (x, s - C.sign * C.scale + C.beta * z) := by
      dsimp only [gamma]
      rw [hstart, div_self C.scale_pos.ne', one_mul]
      congr 2
      ring
    have hh := clockEvolution_tracks V hA hB gamma
      (s := 0) (by norm_num : (0 : ℝ) ∈ Ioo (-1) 2) hgamma ht
    change clockEvolution V hA hB 0 t _ = _
    simpa only [hgamma0] using hh
  refine ⟨Phi, S, N, d, o, w, ?_, ?_, ?_, hSc, hN, hseamN,
    hd, hdl, hdo, hdg, hstrip, hS, hsupp 0, fun t => hsupp t 0, hfix,
    ?_, ?_, ho, hoOld, hw, hwOld, htrack, ?_, hflat⟩
  · exact (clockEvolution_contDiff V hA hB hV hVc).comp
      (((contDiff_const (c := (0 : ℝ))).prodMk contDiff_fst).prodMk contDiff_snd)
  · exact (clockEvolution_contDiff V hA hB hV hVc).comp
      ((contDiff_fst.prodMk (contDiff_const (c := (0 : ℝ)))).prodMk contDiff_snd)
  · exact fun y => clockEvolution_self V hA hB 0 y
  · intro t
    exact ⟨hpres.1 0 t, hpres.1 t 0⟩
  · intro t y hy
    rcases hy with hy | hy
    · exact ⟨hpres.2.2 0 t y hy, hpres.2.2 t 0 y hy⟩
    · exact ⟨hpres.2.1 0 t y (Or.inr hy), hpres.2.1 t 0 y (Or.inr hy)⟩
  · intro t ht
    refine ⟨himage t ht, ?_⟩
    rw [← himage t ht, image_image]
    simp only [Diffeomorph.symm_apply_apply, image_id']

end PoincareConjecture.M25.Topology3D
