import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndAlignedStack
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartUnion
import Mathlib.Tactic.Tauto









set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem exists_saddle_lower_end_tube
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D) (i : Fin 2) :
    let C := D.cap (W.label i)
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let L := heightPlaneCoordinates u
    let ell := C.cutHeight + C.removal
    ∃ (r gamma o w : ℝ)
      (T : OpenPartialHomeomorph (E2 × ℝ) E3)
      (phase : ℝ → Diffeomorph (𝓡 1) (𝓡 1) UnitCircle UnitCircle ∞),
      1 < r ∧ 0 < gamma ∧ gamma < (W.level - ell) / 8 ∧
      0 < o ∧ o ≤ C.overlapWidth ∧ C.scale * o < gamma / 2 ∧
      0 < w ∧ w ≤ C.collarWidth ∧ |C.beta| * w < C.scale / 2 ∧
      T.source =
        (C.tube.source ∩ (ball (0 : E2) r ×ˢ Iio (ell + gamma))) ∪
          (ball (0 : E2) r ×ˢ Ioi (ell - gamma)) ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source ∧
      ContDiffOn ℝ ∞ T T.source ∧
      ContDiffOn ℝ ∞ T.symm T.target ∧
      (∀ p ∈ T.source, H (T p) = p.2) ∧
      (∀ y ∈ T.target, (T.symm y).2 = H y) ∧
      (∀ p ∈ C.tube.source,
        ‖p.1‖ < r → p.2 < ell + gamma → T p = C.tube p) ∧
      (∀ p ∈ C.tube.source,
        ‖p.1‖ < r → p.2 < ell + gamma →
          C.tube p ∈ T.target ∧ T.symm (C.tube p) = p) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
        (fun p : ℝ × UnitCircle => phase p.1 p.2) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 1) ∞
        (fun p : ℝ × UnitCircle => (phase p.1).symm p.2) ∧
      (∀ z ∈ Icc ell (W.level + gamma), ∀ q : UnitCircle,
        (phase z q, z) ∈ (W.leg i).source ∧
        T (q.1, z) = j (W.leg i (phase z q, z))) ∧
      (∀ z ∈ Icc ell (W.level + gamma),
        T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
          range (fun q : UnitCircle => j (W.leg i (q, z)))) ∧
      T '' (ball (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)) =
        (fun x : E2 => L.symm (x, W.level)) '' (W.disc i).inside ∧
      T '' (closedBall (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)) =
        (fun x : E2 => L.symm (x, W.level)) '' (W.disc i).closedRegion ∧
      (∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 < o →
        psi (C.sourceChart q, 0) =
          C.profile.capMap T C.cutHeight C.sign C.removal C.scale q) ∧
      C.cap = C.profile.capMap T C.cutHeight C.sign C.removal C.scale ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
      (∀ x : E2, ‖x‖ ≤ 1 / 8 → ∀ s : ℝ, |s| < w →
        psi (C.flatChart x, s) =
          T (x, C.cutHeight + C.sign * (C.removal - C.scale) + C.beta * s)) := by
  classical
  let C := D.cap (W.label i)
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let L := heightPlaneCoordinates u
  let ell := C.cutHeight + C.removal
  have hsign : C.sign = 1 := W.label_lower i
  have hell : ell < W.level := by
    have hh := W.lower_seams_lt_level (W.label i) hsign
    change C.cutHeight + C.sign * C.removal < W.level at hh
    simpa only [hsign, one_mul] using hh
  obtain ⟨eta, d, c, F, G, heta, hd, hdeta, hlegband, hcEq, hbottom⟩ :=
    exists_saddle_lower_end_family hP psi hpsi u D W i
  let e := C.tube.transHomeomorph L.toHomeomorph
  have he : ContDiffOn ℝ ∞ e e.source := L.contDiff.comp_contDiffOn C.tube_smooth
  have hei : ContDiffOn ℝ ∞ e.symm e.target :=
    C.tube_inverse.comp L.symm.contDiff.contDiffOn (fun _ hp => hp)
  have heh (p : E2 × ℝ) (hp : p ∈ e.source) : (e p).2 = p.2 := by
    exact (heightPlaneCoordinates_snd u (C.tube p)).trans (C.tube_height p hp)
  obtain ⟨r, gamma, U, phase, hr, hgamma, hgap, hgeta, hUsource, hU, hUi,
      hUh, hUold, hphase, hphasei, hUboundary, hUball, hUclosed⟩ :=
    exists_saddle_end_aligned_stack e he hei heh C.tube_source
      ell W.level eta d hell heta hd hdeta c F G hbottom
  let V := U.transHomeomorph L.symm.toHomeomorph
  have hVsource : V.source = ball (0 : E2) r ×ˢ (univ : Set ℝ) := hUsource
  have hV : ContDiffOn ℝ ∞ V V.source := L.symm.contDiff.comp_contDiffOn hU
  have hVi : ContDiffOn ℝ ∞ V.symm V.target :=
    hUi.comp L.contDiff.contDiffOn (fun _ hp => hp)
  have hVh (p : E2 × ℝ) : H (V p) = p.2 := by
    change ⟪(u : E3), L.symm (U p)⟫_ℝ = p.2
    rw [← heightPlaneCoordinates_snd u, L.apply_symm_apply]
    exact hUh p
  have hVold (p : E2 × ℝ)
      (hp : p ∈ ball (0 : E2) r ×ˢ Ioo (ell - gamma) (ell + gamma)) :
      p ∈ C.tube.source ∧ V p = C.tube p := by
    obtain ⟨hps, heq⟩ := hUold p hp
    refine ⟨hps, ?_⟩
    change L.symm (U p) = C.tube p
    rw [heq]
    exact L.symm_apply_apply _
  let A := C.tube.restrOpen (ball (0 : E2) r ×ˢ Iio (ell + gamma))
    (isOpen_ball.prod isOpen_Iio)
  let B := V.restrOpen (ball (0 : E2) r ×ˢ Ioi (ell - gamma))
    (isOpen_ball.prod isOpen_Ioi)
  have hAsource : A.source = C.tube.source ∩
      (ball (0 : E2) r ×ˢ Iio (ell + gamma)) := rfl
  have hBsource : B.source = ball (0 : E2) r ×ˢ Ioi (ell - gamma) := by
    change V.source ∩ (ball (0 : E2) r ×ˢ Ioi (ell - gamma)) = _
    rw [hVsource]
    ext p
    simp only [mem_inter_iff, mem_prod, mem_univ, and_true]
    tauto
  have hagree : EqOn A B (A.source ∩ B.source) := by
    intro p hp
    have ha := hAsource ▸ hp.1
    have hb := hBsource ▸ hp.2
    exact (hVold p ⟨hb.1, hb.2, ha.2.2⟩).2.symm
  have hAh (p : E2 × ℝ) (hp : p ∈ A.source) : H (A p) = p.2 :=
    C.tube_height p hp.1
  have hBh (p : E2 × ℝ) : H (B p) = p.2 := hVh p
  have hinv : EqOn A.symm B.symm (A.target ∩ B.target) := by
    intro y hy
    have ha := A.map_target hy.1
    have hb := B.map_target hy.2
    have haz : (A.symm y).2 = H y := by
      have hh := hAh (A.symm y) ha
      rw [A.right_inv hy.1] at hh
      exact hh.symm
    have hbz : (B.symm y).2 = H y := by
      have hh := hBh (B.symm y)
      rw [B.right_inv hy.2] at hh
      exact hh.symm
    have haS := hAsource ▸ ha
    have hbS := hBsource ▸ hb
    have hbuffer : B.symm y ∈ ball (0 : E2) r ×ˢ
        Ioo (ell - gamma) (ell + gamma) := by
      refine ⟨hbS.1, hbS.2, ?_⟩
      rw [hbz, ← haz]
      exact haS.2.2
    obtain ⟨hbs, heq⟩ := hVold (B.symm y) hbuffer
    have hbA : B.symm y ∈ A.source := ⟨hbs, hbuffer.1, hbuffer.2.2⟩
    have hAy : A (B.symm y) = y := by
      change C.tube (B.symm y) = y
      rw [← heq]
      exact B.right_inv hy.2
    calc
      A.symm y = A.symm (A (B.symm y)) := congrArg A.symm hAy.symm
      _ = B.symm y := A.left_inv hbA
  let T := glueOpenCharts A B hagree hinv
  have hTsource : T.source =
      (C.tube.source ∩ (ball (0 : E2) r ×ˢ Iio (ell + gamma))) ∪
        (ball (0 : E2) r ×ˢ Ioi (ell - gamma)) := by
    rw [glueOpenCharts_source, hAsource, hBsource]
  have hTclosed : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source := by
    intro p hp
    rw [hTsource]
    have hpr : p.1 ∈ ball (0 : E2) r := closedBall_subset_ball hr hp.1
    by_cases hz : p.2 < ell + gamma
    · exact Or.inl ⟨C.tube_source hp, hpr, hz⟩
    · apply Or.inr
      refine ⟨hpr, ?_⟩
      change ell - gamma < p.2
      linarith [le_of_not_gt hz]
  have hT : ContDiffOn ℝ ∞ T T.source := glueOpenCharts_contDiffOn A B hagree hinv
    (C.tube_smooth.mono inter_subset_left) (hV.mono inter_subset_left)
  have hTi : ContDiffOn ℝ ∞ T.symm T.target :=
    glueOpenCharts_symm_contDiffOn A B hagree hinv
      (C.tube_inverse.mono inter_subset_left) (hVi.mono inter_subset_left)
  have hTA : EqOn T A A.source := glueOpenCharts_eqOn_left A B hagree hinv
  have hTB : EqOn T B B.source := glueOpenCharts_eqOn_right A B hagree hinv
  have hTh (p : E2 × ℝ) (hp : p ∈ T.source) : H (T p) = p.2 := by
    rcases hp with hp | hp
    · rw [hTA hp]
      exact hAh p hp
    · rw [hTB hp]
      exact hBh p
  have hTih (y : E3) (hy : y ∈ T.target) : (T.symm y).2 = H y := by
    have hh := hTh (T.symm y) (T.map_target hy)
    rw [T.right_inv hy] at hh
    exact hh.symm
  have hTold (p : E2 × ℝ) (hp : p ∈ C.tube.source)
      (hpr : ‖p.1‖ < r) (hpz : p.2 < ell + gamma) : T p = C.tube p :=
    hTA ⟨hp, mem_ball_zero_iff.mpr hpr, hpz⟩
  have hToldInv (p : E2 × ℝ) (hp : p ∈ C.tube.source)
      (hpr : ‖p.1‖ < r) (hpz : p.2 < ell + gamma) :
      C.tube p ∈ T.target ∧ T.symm (C.tube p) = p := by
    have hps : p ∈ T.source := Or.inl ⟨hp, mem_ball_zero_iff.mpr hpr, hpz⟩
    have heq := hTold p hp hpr hpz
    exact ⟨heq ▸ T.map_source hps, heq ▸ T.left_inv hps⟩
  have hTupper (p : E2 × ℝ) (hpr : ‖p.1‖ < r) (hpz : ell - gamma < p.2) :
      T p = L.symm (U p) := by
    have hps : p ∈ B.source := by
      rw [hBsource]
      exact ⟨mem_ball_zero_iff.mpr hpr, hpz⟩
    exact hTB hps
  have hleg (z : ℝ) (hz : z ∈ Icc ell (W.level + gamma)) (q : UnitCircle) :
      (phase z q, z) ∈ (W.leg i).source ∧
        T (q.1, z) = j (W.leg i (phase z q, z)) := by
    have hsrc : (phase z q, z) ∈ (W.leg i).source :=
      hlegband ⟨mem_univ _, by constructor <;> linarith [hz.1, hz.2]⟩
    refine ⟨hsrc, ?_⟩
    rw [hTupper (q.1, z) (by simpa only [norm_eq_of_mem_sphere q] using hr)
      (by linarith [hz.1]), hUboundary z hz q,
      hcEq z (by constructor <;> linarith [hz.1, hz.2]) (phase z q)]
    exact heightPlaneCoordinates_reconstruct u _ z (W.leg_height i _ hsrc)
  have hcircle (z : ℝ) (hz : z ∈ Icc ell (W.level + gamma)) :
      T '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) =
        range (fun q : UnitCircle => j (W.leg i (q, z))) := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have htz : t = z := ht
      subst t
      exact ⟨phase z ⟨x, hx⟩, (hleg z hz ⟨x, hx⟩).2.symm⟩
    · rintro ⟨q, rfl⟩
      refine ⟨((phase z).symm q |>.1, z),
        ⟨((phase z).symm q).2, mem_singleton _⟩, ?_⟩
      rw [(hleg z hz ((phase z).symm q)).2, (phase z).apply_symm_apply]
  have htop : W.level ∈ Icc (ell - 2 * eta) (W.level + 2 * eta) :=
    ⟨by linarith, by linarith⟩
  let lift : E2 → E3 := fun x => L.symm (x, W.level)
  have hlift : Injective lift := by
    intro x y hxy
    exact congrArg Prod.fst (L.symm.injective hxy)
  have hdiscBoundary : (W.disc i).boundary = range (c W.level) := by
    apply hlift.image_injective
    rw [W.disc_boundary i, ← range_comp]
    congr 1
    funext q
    dsimp only [Function.comp_def, lift]
    rw [hcEq W.level htop q]
    have hsrc : (q, W.level) ∈ (W.leg i).source :=
      hlegband ⟨mem_univ _, by constructor <;> linarith⟩
    exact (heightPlaneCoordinates_reconstruct u _ W.level (W.leg_height i _ hsrc)).symm
  have hfill : F.chart W.level '' ball (0 : E2) 1 = (W.disc i).inside :=
    G.fiber_inside_eq W.level htop (W.disc i) hdiscBoundary
  have hclosedFill : F.chart W.level '' closedBall (0 : E2) 1 = (W.disc i).closedRegion :=
    G.fiber_closedRegion_eq W.level htop (W.disc i) hdiscBoundary
  have hTimage (S : Set E2) (hS : S ⊆ closedBall (0 : E2) 1) :
      T '' (S ×ˢ ({W.level} : Set ℝ)) =
        L.symm '' (U '' (S ×ˢ ({W.level} : Set ℝ))) := by
    rw [← image_comp]
    apply image_congr
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hzt : z = W.level := hz
    subst z
    exact hTupper (x, W.level) ((mem_closedBall_zero_iff.mp (hS hx)).trans_lt hr)
      (by linarith)
  have hball : T '' (ball (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)) =
      lift '' (W.disc i).inside := by
    rw [hTimage (ball 0 1) ball_subset_closedBall, hUball, ← hfill]
    rw [image_image, image_image]
  have hclosed : T '' (closedBall (0 : E2) 1 ×ˢ ({W.level} : Set ℝ)) =
      lift '' (W.disc i).closedRegion := by
    rw [hTimage (closedBall 0 1) subset_rfl, hUclosed, ← hclosedFill]
    rw [image_image, image_image]
  let o := min (C.overlapWidth / 2) (gamma / (4 * C.scale))
  let w := min (C.collarWidth / 2) (C.scale / (4 * |C.beta|))
  have hbeta : 0 < |C.beta| := abs_pos.mpr C.beta_ne
  have ho : 0 < o := lt_min (div_pos C.overlap_pos (by norm_num))
    (div_pos hgamma (mul_pos (by norm_num) C.scale_pos))
  have how : o ≤ C.overlapWidth := by
    have hh := min_le_left (C.overlapWidth / 2) (gamma / (4 * C.scale))
    dsimp only [o]
    linarith [C.overlap_pos]
  have hoscale : C.scale * o < gamma / 2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) C.scale_pos)).mp
      (min_le_right (C.overlapWidth / 2) (gamma / (4 * C.scale)))
    change o * (4 * C.scale) ≤ gamma at hh
    nlinarith
  have hw : 0 < w := lt_min (div_pos C.collar_pos (by norm_num))
    (div_pos C.scale_pos (mul_pos (by norm_num) hbeta))
  have hww : w ≤ C.collarWidth := by
    have hh := min_le_left (C.collarWidth / 2) (C.scale / (4 * |C.beta|))
    dsimp only [w]
    linarith [C.collar_pos]
  have hwbeta : |C.beta| * w < C.scale / 2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) hbeta)).mp
      (min_le_right (C.collarWidth / 2) (C.scale / (4 * |C.beta|)))
    change w * (4 * |C.beta|) ≤ C.scale at hh
    nlinarith [C.scale_pos]
  have hcapSource (q : UnitTwoSphere) :
      ((C.profile.model q).1,
        C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2)) ∈
          C.tube.source := C.tube_source
    ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le q), mem_univ _⟩
  have hcapHeight (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 < o) :
      C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2) < ell + gamma := by
    rw [hsign, one_mul]
    by_cases hsouth : (heightCoordinates (q : E3)).2 ≤ 0
    · have hh : (C.profile.model q).2 ≤ 0 :=
        (surgeryCapModel_snd_nonpos_iff C.profile.horizontal C.profile.vertical
          C.profile.horizontal_smooth C.profile.vertical_smooth
          (fun z => (C.profile.horizontal_pos z).ne')
          (fun x => (C.profile.vertical_pos x).ne') C.profile.vertical_pos q).mpr hsouth
      have hmul := mul_nonpos_of_nonneg_of_nonpos C.scale_pos.le hh
      dsimp only [ell]
      linarith
    · have hp : 0 < (heightCoordinates (q : E3)).2 := lt_of_not_ge hsouth
      have hv : |(heightCoordinates (q : E3)).2| ≤ 1 / 4 := by
        rw [abs_of_pos hp]
        exact hq.le.trans (how.trans C.overlap_le)
      have hm := surgeryCapModel_cylinder C.profile.horizontal C.profile.vertical
        C.profile.horizontal_smooth C.profile.vertical_smooth
        (fun z => (C.profile.horizontal_pos z).ne')
        (fun x => (C.profile.vertical_pos x).ne') C.profile.horizontal_near
        C.profile.vertical_far q hv
      have hheight : (C.profile.model q).2 = (heightCoordinates (q : E3)).2 := by
        simpa only [SurgeryCapProfile.model] using congrArg Prod.snd hm
      rw [hheight]
      have hh := mul_lt_mul_of_pos_left hq C.scale_pos
      dsimp only [ell]
      linarith
  have hcentral (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 < o) :
      psi (C.sourceChart q, 0) = C.profile.capMap T C.cutHeight C.sign C.removal C.scale q := by
    rw [C.central_eq q (hq.trans_le how), SurgeryCapProfile.capMap_apply,
      SurgeryCapProfile.capMap_apply]
    exact (hTold _ (hcapSource q) ((C.profile.model_fst_norm_le q).trans_lt hr)
      (hcapHeight q hq)).symm
  have hcap : C.cap = C.profile.capMap T C.cutHeight C.sign C.removal C.scale ''
      {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
    change j '' (C.sourceChart '' {q : UnitTwoSphere |
      (heightCoordinates (q : E3)).2 ≤ 0}) = _
    rw [image_image]
    exact image_congr (fun q hq => hcentral q (hq.trans_lt ho))
  have hcollar (x : E2) (hx : ‖x‖ ≤ 1 / 8) (s : ℝ) (hs : |s| < w) :
      psi (C.flatChart x, s) =
        T (x, C.cutHeight + C.sign * (C.removal - C.scale) + C.beta * s) := by
    rw [C.collar_eq x hx s (hs.trans_le hww)]
    apply (hTold _ ?_ ?_ ?_).symm
    · exact C.tube_source ⟨mem_closedBall_zero_iff.mpr (by linarith), mem_univ _⟩
    · dsimp only
      linarith
    · have hb : C.beta * s < C.scale / 2 := by
        calc
          C.beta * s ≤ |C.beta * s| := le_abs_self _
          _ = |C.beta| * |s| := abs_mul _ _
          _ < |C.beta| * w := mul_lt_mul_of_pos_left hs hbeta
          _ < C.scale / 2 := hwbeta
      dsimp only
      rw [hsign, one_mul]
      dsimp only [ell]
      linarith [C.scale_pos]
  exact ⟨r, gamma, o, w, T, phase, hr, hgamma, hgap,
    ho, how, hoscale, hw, hww, hwbeta, hTsource, hTclosed, hT, hTi,
    hTh, hTih, hTold, hToldInv, hphase, hphasei, hleg, hcircle,
    hball, hclosed, hcentral, hcap, hcollar⟩

end PoincareConjecture.M25.Topology3D
