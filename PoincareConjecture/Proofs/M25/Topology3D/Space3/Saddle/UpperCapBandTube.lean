import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubeFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightReversalData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCollarReflection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HorizontalTubeChart
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 1000000 in

theorem exists_saddle_upper_cap_band_tube
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (C : SurgeryCapTag psi u) (hsign : C.sign = -1)
    (z : ℝ) (hz : z < C.cutHeight - C.removal)
    (hseam : {q : UnitTwoSphere |
      ⟪(u : E3), psi (q, 0)⟫_ℝ = C.cutHeight - C.removal} = C.sourceSeam)
    (hreg : ∀ q : UnitTwoSphere,
      ⟪(u : E3), psi (q, 0)⟫_ℝ ∈ Icc z (C.cutHeight - C.removal) →
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ)
        (fun p : UnitTwoSphere => ⟪(u : E3), psi (p, 0)⟫_ℝ) q ≠ 0) :
    let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let S : Set E3 := range j
    let ell := C.cutHeight - C.removal
    ∃ (r gamma o w : ℝ) (T : OpenPartialHomeomorph (E2 × ℝ) E3),
      1 < r ∧ 0 < gamma ∧ gamma < (ell - z) / 8 ∧
      0 < o ∧ o ≤ C.overlapWidth ∧ C.scale * o < gamma / 2 ∧
      0 < w ∧ w ≤ C.collarWidth ∧ |C.beta| * w < C.scale / 2 ∧
      T.source =
        (C.tube.source ∩ (ball (0 : E2) r ×ˢ Ioi (ell - gamma))) ∪
          (ball (0 : E2) r ×ˢ Iio (ell + gamma)) ∧
      closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source ∧
      ContDiffOn ℝ ∞ T T.source ∧ ContDiffOn ℝ ∞ T.symm T.target ∧
      (∀ p ∈ T.source, H (T p) = p.2) ∧
      (∀ y ∈ T.target, (T.symm y).2 = H y) ∧
      (∀ p ∈ C.tube.source, ‖p.1‖ < r → ell - gamma < p.2 →
        T p = C.tube p ∧ C.tube p ∈ T.target ∧ T.symm (C.tube p) = p) ∧
      (∀ q : UnitTwoSphere, (heightCoordinates (q : E3)).2 < o →
        j (C.sourceChart q) =
          C.profile.capMap T C.cutHeight C.sign C.removal C.scale q) ∧
      (∀ x : E2, ‖x‖ ≤ 1 / 8 → ∀ s : ℝ, |s| < w →
        psi (C.flatChart x, s) =
          T (x, C.cutHeight + C.sign * (C.removal - C.scale) + C.beta * s)) ∧
      C.cap =
        (fun q : UnitTwoSphere =>
          T ((C.profile.model q).1, ell - C.scale * (C.profile.model q).2)) ''
            {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
      (∀ t ∈ Icc (z - gamma) (ell + gamma),
        T '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) = S ∩ {y | H y = t}) := by
  classical
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let S : Set E3 := range j
  let f : UnitTwoSphere → ℝ := fun q => H (j q)
  let L := heightPlaneCoordinates u
  let ell := C.cutHeight - C.removal
  change z < ell at hz
  change {q : UnitTwoSphere | f q = ell} = C.sourceSeam at hseam
  have hji : Injective j := by
    intro p q hpq
    exact congrArg Prod.fst (hpsi.2.1
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hpq)
  have hLh (x : E2) (t : ℝ) : H (L.symm (x, t)) = t := by
    change ⟪(u : E3), L.symm (x, t)⟫_ℝ = t
    rw [← heightPlaneCoordinates_snd u, L.apply_symm_apply]
  have hrec (y : E3) (t : ℝ) (hy : H y = t) : L.symm ((L y).1, t) = y :=
    heightPlaneCoordinates_reconstruct u y t hy
  have hcm : C.reverseHeight.sign = 1 := by
    change -C.sign = 1
    rw [hsign]
    norm_num
  have hellm : C.reverseHeight.cutHeight + C.reverseHeight.removal = -ell := by
    change -C.cutHeight + C.removal = -(C.cutHeight - C.removal)
    ring
  obtain ⟨dm, Qm, hdm, hQms, _, _, hQmh, hQme, hQmb⟩ :=
    exists_saddle_cap_source_annulus psi hpsi (-u) C.reverseHeight hcm
  rw [hellm] at hQms hQme hQmb
  let Qo := circleTimeReflection.toHomeomorph.toOpenPartialHomeomorph.trans Qm
  have hQoh (p : UnitCircle × ℝ) (hp : p ∈ Qo.source) : f (Qo p) = p.2 := by
    have hh := hQmh (p.1, -p.2) hp.2
    change ⟪((-u : UnitTwoSphere) : E3), psi (Qo p, 0)⟫_ℝ = -p.2 at hh
    rw [coe_neg_sphere, inner_neg_left] at hh
    change ⟪(u : E3), psi (Qo p, 0)⟫_ℝ = p.2
    linarith
  have hQoe (p : UnitCircle × ℝ) (hp : p ∈ Qo.source) :
      j (Qo p) = C.tube (p.1.1, p.2) := by
    have ht : -p.2 ∈ Ioo (-ell - dm) (-ell + dm) := (hQms ▸ hp.2).2
    have hh := hQme p.1 (-p.2) ht
    rw [C.reverseHeight_tube.1 (p.1.1, -p.2)] at hh
    change psi (Qm (p.1, -p.2), 0) = C.tube (p.1.1, p.2)
    simpa only [neg_neg] using hh
  have hQos (q : UnitCircle) : (q, ell) ∈ Qo.source := by
    refine ⟨mem_univ _, ?_⟩
    rw [hQms]
    change (q, -ell) ∈ (univ : Set UnitCircle) ×ˢ Ioo (-ell - dm) (-ell + dm)
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  have hQob : range (fun q : UnitCircle => Qo (q, ell)) = C.sourceSeam := hQmb
  have hold0 : range (fun q : UnitCircle => C.tube (q.1, ell)) =
      S ∩ {y | H y = ell} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨⟨Qo (q, ell), hQoe (q, ell) (hQos q)⟩,
        C.tube_height _ (C.tube_source ⟨sphere_subset_closedBall q.2, mem_univ _⟩)⟩
    · rintro ⟨⟨q, rfl⟩, hq⟩
      have hqc : q ∈ C.sourceSeam := hseam ▸ hq
      obtain ⟨theta, htheta⟩ := hQob.symm ▸ hqc
      refine ⟨theta, ?_⟩
      rw [← htheta]
      exact (hQoe (theta, ell) (hQos theta)).symm
  obtain ⟨d0, _, hI, Phi, hPhi, hPhii, _, _, hPhiMem⟩ :=
    exists_regular_collar_horizontal_transport psi hpsi u z ell hz.le hreg
  let a0 := (z + ell) / 2 - d0
  let b0 := (z + ell) / 2 + d0
  let J0 := Ioo a0 b0
  have hzJ : z ∈ J0 := hI ⟨le_rfl, hz.le⟩
  have hellJ : ell ∈ J0 := hI ⟨hz.le, le_rfl⟩
  let Y := fun t : ℝ => (Phi ell).symm.trans (Phi t)
  have hY : ContDiff ℝ ∞ (fun p : ℝ × E2 => Y p.1 p.2) :=
    hPhi.comp (contDiff_fst.prodMk ((Phi ell).symm.contDiff.comp contDiff_snd))
  have hYi : ContDiff ℝ ∞ (fun p : ℝ × E2 => (Y p.1).symm p.2) :=
    (Phi ell).contDiff.comp hPhii
  have hYmem (t : ℝ) (ht : t ∈ J0) (x : E2) :
      L.symm (Y t x, t) ∈ S ↔ L.symm (x, ell) ∈ S := by
    have h1 := hPhiMem t ht ((Phi ell).symm x)
    have h2 := hPhiMem ell hellJ ((Phi ell).symm x)
    rw [(Phi ell).apply_symm_apply] at h2
    exact h1.trans h2.symm
  have htransport (s t : ℝ) (hs : s ∈ J0) (ht : t ∈ J0) (y : E3) :
      L.symm (Y t ((Y s).symm (L y).1), t) ∈ S ↔
        L.symm ((L y).1, s) ∈ S := by
    have h1 := hYmem t ht ((Y s).symm (L y).1)
    have h2 := hYmem s hs ((Y s).symm (L y).1)
    rw [(Y s).apply_symm_apply] at h2
    exact h1.trans h2.symm
  let e := C.tube.transHomeomorph L.toHomeomorph
  have he : ContDiffOn ℝ ∞ e e.source := L.contDiff.comp_contDiffOn C.tube_smooth
  have hei : ContDiffOn ℝ ∞ e.symm e.target :=
    C.tube_inverse.comp L.symm.contDiff.contDiffOn (fun _ hp => hp)
  have heh (p : E2 × ℝ) (hp : p ∈ e.source) : (e p).2 = p.2 :=
    (heightPlaneCoordinates_snd u (C.tube p)).trans (C.tube_height p hp)
  obtain ⟨B0, hB0, _, _, _⟩ := exists_saddle_end_fiber_chart e he hei heh ell
    (fun x hx => C.tube_source ⟨hx, mem_univ _⟩)
  let T0 := horizontalTubeChart Y hY hYi u B0
  have hT0s : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T0.source :=
    horizontalTubeChart_closedBall_subset_source Y hY hYi u B0
  have hT0 : ContDiffOn ℝ ∞ T0 T0.source :=
    horizontalTubeChart_contDiffOn Y hY hYi u B0
  have hT0i : ContDiffOn ℝ ∞ T0.symm T0.target :=
    horizontalTubeChart_symm_contDiffOn Y hY hYi u B0
  have hT0h (p : E2 × ℝ) : H (T0 p) = p.2 :=
    horizontalTubeChart_height Y hY hYi u B0 p
  have hT0p (x : E2) (t : ℝ) :
      T0 (x, t) = L.symm (Y t ((L (C.tube (x, ell))).1), t) := by
    rw [horizontalTubeChart_apply, hB0]
    rfl
  have hT0circle (t : ℝ) (ht : t ∈ J0) :
      range (fun q : UnitCircle => T0 (q.1, t)) = S ∩ {y | H y = t} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      have hq : C.tube (q.1, ell) ∈ S ∩ {y | H y = ell} :=
        hold0 ▸ (mem_range_self q)
      refine ⟨?_, hT0h _⟩
      change T0 (q.1, t) ∈ S
      rw [hT0p]
      apply (hYmem t ht _).mpr
      rw [hrec _ ell hq.2]
      exact hq.1
    · intro hy
      let x := (Y t).symm (L y).1
      have hxy : L.symm (Y t x, t) = y := by
        rw [(Y t).apply_symm_apply]
        exact hrec y t hy.2
      have hxS : L.symm (x, ell) ∈ S :=
        (hYmem t ht x).mp (hxy.symm ▸ hy.1)
      have hxo : L.symm (x, ell) ∈ range (fun q : UnitCircle => C.tube (q.1, ell)) :=
        hold0.symm ▸ ⟨hxS, hLh x ell⟩
      obtain ⟨q, hq⟩ := hxo
      refine ⟨q, ?_⟩
      change T0 (q.1, t) = y
      change C.tube (q.1, ell) = L.symm (x, ell) at hq
      rw [hT0p, hq, L.apply_symm_apply]
      exact hxy
  obtain ⟨Qr, hQrs, _, _, hQre⟩ := exists_source_tube_chart psi hpsi T0 hT0 hT0i
    isOpen_Ioo (fun p hp => hT0s ⟨sphere_subset_closedBall hp.1, mem_univ _⟩)
    (fun q t ht => ((hT0circle t ht) ▸ mem_range_self q).1)
  have hQrh (p : UnitCircle × ℝ) (hp : p ∈ Qr.source) : f (Qr p) = p.2 := by
    change H (psi (Qr p, 0)) = p.2
    rw [hQre p.1 p.2 (hQrs ▸ hp).2]
    exact hT0h _
  have hQrlevel (t : ℝ) (ht : t ∈ J0) :
      range (fun q : UnitCircle => Qr (q, t)) = {q : UnitTwoSphere | f q = t} := by
    ext q
    constructor
    · rintro ⟨theta, rfl⟩
      exact hQrh (theta, t) (hQrs.symm ▸ ⟨mem_univ _, ht⟩)
    · intro hq
      have hm : j q ∈ range (fun theta : UnitCircle => T0 (theta.1, t)) :=
        (hT0circle t ht).symm ▸ ⟨mem_range_self q, hq⟩
      obtain ⟨theta, htheta⟩ := hm
      exact ⟨theta, hji ((hQre theta t ht).trans htheta)⟩
  have hQrb : range (fun q : UnitCircle => Qr (q, ell)) = C.sourceSeam :=
    (hQrlevel ell hellJ).trans hseam
  obtain ⟨d, hd, hQoc, _, hQc⟩ := exists_saddle_end_common_circles Qo Qr f ell
    hQoh hQrh hQos (fun q => hQrs.symm ▸ ⟨mem_univ q, hellJ⟩)
    (hQob.trans hQrb.symm)
  have hold (t : ℝ) (ht : t ∈ Icc (ell - d) (ell + d)) (htJ : t ∈ J0) :
      range (fun q : UnitCircle => C.tube (q.1, t)) = S ∩ {y | H y = t} := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨⟨Qo (q, t), hQoe (q, t) (hQoc ⟨mem_univ _, ht⟩)⟩,
        C.tube_height _ (C.tube_source ⟨sphere_subset_closedBall q.2, mem_univ _⟩)⟩
    · rintro ⟨⟨q, rfl⟩, hq⟩
      have hqr : q ∈ range (fun theta : UnitCircle => Qr (theta, t)) :=
        (hQrlevel t htJ).symm ▸ hq
      obtain ⟨theta, htheta⟩ := (hQc t ht).symm ▸ hqr
      refine ⟨theta, ?_⟩
      rw [← htheta]
      exact (hQoe (theta, t) (hQoc ⟨mem_univ _, ht⟩)).symm
  let gamma := min ((ell - z) / 16)
    (min (d / 4) (min ((z - a0) / 2) ((b0 - ell) / 2)))
  have hg : 0 < gamma := lt_min (div_pos (sub_pos.mpr hz) (by norm_num))
    (lt_min (div_pos hd (by norm_num))
      (lt_min (by linarith [hzJ.1]) (by linarith [hellJ.2])))
  have hg1 : gamma ≤ (ell - z) / 16 := min_le_left _ _
  have hg2 : gamma ≤ d / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hg3 : gamma ≤ (z - a0) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hg4 : gamma ≤ (b0 - ell) / 2 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hgap : gamma < (ell - z) / 8 := by linarith
  have hband (t : ℝ) (ht : t ∈ Icc (z - gamma) (ell + gamma)) : t ∈ J0 := by
    constructor <;> linarith [ht.1, ht.2]
  let Jc := Icc (ell - 2 * gamma) (ell + gamma)
  have hJcd (t : ℝ) (ht : t ∈ Jc) : t ∈ Icc (ell - d) (ell + d) := by
    constructor <;> linarith [ht.1, ht.2]
  have hJcJ (t : ℝ) (ht : t ∈ Jc) : t ∈ J0 := by
    apply hband t
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨r, hr, hbuffer⟩ := exists_saddle_end_disc_buffer Jc isCompact_Icc
    C.tube.source C.tube.open_source
    (fun p hp => C.tube_source ⟨hp.1, mem_univ _⟩)
  let chi : ℝ → ℝ := fun t => Real.smoothTransition ((t - (ell - 2 * gamma)) / gamma)
  have hchi : ContDiff ℝ ∞ chi := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hchir (t : ℝ) : 0 ≤ chi t ∧ chi t ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hchilo (t : ℝ) (ht : t ≤ ell - 2 * gamma) : chi t = 0 :=
    Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith) hg.le)
  have hchihi (t : ℝ) (ht : ell - gamma ≤ t) : chi t = 1 := by
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ hg).mpr
    linarith
  let k : ℝ → ℝ := fun t => ell + chi t * (t - ell)
  have hk : ContDiff ℝ ∞ k :=
    contDiff_const.add (hchi.mul (contDiff_id.sub contDiff_const))
  have hklo (t : ℝ) (ht : t ≤ ell - 2 * gamma) : k t = ell := by
    simp only [k, hchilo t ht, zero_mul, add_zero]
  have hkhi (t : ℝ) (ht : ell - gamma ≤ t) : k t = t := by
    simp only [k, hchihi t ht, one_mul]
    ring
  have hkbuf (t : ℝ) (ht : t ≤ ell + gamma) : k t ∈ Jc := by
    by_cases hlo : t ≤ ell - 2 * gamma
    · rw [hklo t hlo]
      constructor <;> linarith
    · have hl : ell - 2 * gamma ≤ t := (lt_of_not_ge hlo).le
      have hc := hchir t
      have h1 := mul_nonneg hc.1 (sub_nonneg.mpr hl)
      have h2 := mul_nonneg (sub_nonneg.mpr hc.2)
        (by linarith : 0 ≤ ell - (ell - 2 * gamma))
      have h3 := mul_nonneg hc.1 (sub_nonneg.mpr ht)
      have h4 := mul_nonneg (sub_nonneg.mpr hc.2)
        (by linarith : 0 ≤ ell + gamma - ell)
      change ell - 2 * gamma ≤ ell + chi t * (t - ell) ∧
        ell + chi t * (t - ell) ≤ ell + gamma
      constructor <;> nlinarith
  let G := planarFamilyGraphDiffeomorph Y hY hYi
  let e0 := e.transHomeomorph G.symm.toHomeomorph
  have he0 : ContDiffOn ℝ ∞ e0 e0.source := G.symm.contDiff.comp_contDiffOn he
  have he0i : ContDiffOn ℝ ∞ e0.symm e0.target :=
    hei.comp G.contDiff.contDiffOn (fun _ hp => hp)
  have he0h (p : E2 × ℝ) (hp : p ∈ e0.source) : (e0 p).2 = p.2 := heh p hp
  obtain ⟨e1, he1p, _, he1s, _, he1, he1i, he1h⟩ :=
    exists_saddle_end_chart_reparam e0 he0 he0i he0h k hk
  let V := e1.transHomeomorph (G.trans L.symm.toDiffeomorph).toHomeomorph
  let T := V.restrOpen (ball (0 : E2) r ×ˢ (univ : Set ℝ))
    (isOpen_ball.prod isOpen_univ)
  have hTs0 : T.source = {p : E2 × ℝ | ‖p.1‖ < r ∧ (p.1, k p.2) ∈ C.tube.source} := by
    change e1.source ∩ (ball (0 : E2) r ×ˢ (univ : Set ℝ)) = _
    rw [he1s]
    ext p
    simp only [mem_inter_iff, mem_ofPred_eq, mem_prod, mem_univ, and_true,
      mem_ball_zero_iff]
    exact and_comm
  have hTs : T.source =
      (C.tube.source ∩ (ball (0 : E2) r ×ˢ Ioi (ell - gamma))) ∪
        (ball (0 : E2) r ×ˢ Iio (ell + gamma)) := by
    rw [hTs0]
    ext p
    constructor
    · intro hp
      by_cases ht : p.2 < ell + gamma
      · exact Or.inr ⟨mem_ball_zero_iff.mpr hp.1, ht⟩
      · have ht' : ell - gamma ≤ p.2 := by linarith [le_of_not_gt ht]
        exact Or.inl ⟨by simpa only [hkhi p.2 ht'] using hp.2,
          mem_ball_zero_iff.mpr hp.1, by
            change ell - gamma < p.2
            linarith [le_of_not_gt ht]⟩
    · rintro (hp | hp)
      · exact ⟨mem_ball_zero_iff.mp hp.2.1, by simpa only [hkhi p.2 hp.2.2.le] using hp.1⟩
      · exact ⟨mem_ball_zero_iff.mp hp.1, hbuffer ⟨hp.1, hkbuf p.2 hp.2.le⟩⟩
  have hTclosed : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source := by
    intro p hp
    rw [hTs0]
    exact ⟨(mem_closedBall_zero_iff.mp hp.1).trans_lt hr,
      C.tube_source ⟨hp.1, mem_univ _⟩⟩
  have hV : ContDiffOn ℝ ∞ V V.source :=
    (G.trans L.symm.toDiffeomorph).contDiff.comp_contDiffOn he1
  have hVi : ContDiffOn ℝ ∞ V.symm V.target :=
    he1i.comp (G.trans L.symm.toDiffeomorph).symm.contDiff.contDiffOn (fun _ hp => hp)
  have hT : ContDiffOn ℝ ∞ T T.source := hV.mono inter_subset_left
  have hTi : ContDiffOn ℝ ∞ T.symm T.target := hVi.mono inter_subset_left
  have hTh (p : E2 × ℝ) : H (T p) = p.2 := by
    change ⟪(u : E3), L.symm (G (e1 p))⟫_ℝ = p.2
    rw [← heightPlaneCoordinates_snd u, L.apply_symm_apply]
    exact he1h p
  have hTih (y : E3) (hy : y ∈ T.target) : (T.symm y).2 = H y := by
    have hh := hTh (T.symm y)
    rw [T.right_inv hy] at hh
    exact hh.symm
  have hTp (p : E2 × ℝ) (hp : p ∈ T.source) :
      T p = L.symm (Y p.2 ((Y (k p.2)).symm (L (C.tube (p.1, k p.2))).1), p.2) := by
    have hps : (p.1, k p.2) ∈ C.tube.source := (hTs0 ▸ hp).2
    have hh := (heightPlaneCoordinates_snd u (C.tube (p.1, k p.2))).trans
      (C.tube_height _ hps)
    change L.symm (G (e1 p)) = _
    rw [he1p]
    change L.symm (Y p.2 ((Y (L (C.tube (p.1, k p.2))).2).symm
      (L (C.tube (p.1, k p.2))).1), p.2) = _
    rw [hh]
  have hTold (p : E2 × ℝ) (hp : p ∈ C.tube.source)
      (hpr : ‖p.1‖ < r) (hpt : ell - gamma < p.2) :
      T p = C.tube p ∧ C.tube p ∈ T.target ∧ T.symm (C.tube p) = p := by
    have hps : p ∈ T.source := by
      rw [hTs0]
      exact ⟨hpr, by simpa only [hkhi p.2 hpt.le] using hp⟩
    have heq : T p = C.tube p := by
      rw [hTp p hps, hkhi p.2 hpt.le, (Y p.2).apply_symm_apply]
      exact hrec _ _ (C.tube_height p hp)
    exact ⟨heq, heq ▸ T.map_source hps, heq ▸ T.left_inv hps⟩
  have hTrange (t : ℝ) (ht : t ∈ Icc (z - gamma) (ell + gamma)) :
      range (fun q : UnitCircle => T (q.1, t)) = S ∩ {y | H y = t} := by
    have htJ := hband t ht
    have hkJc := hkbuf t ht.2
    have hkJ := hJcJ (k t) hkJc
    have holdk := hold (k t) (hJcd (k t) hkJc) hkJ
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      have hqs : (q.1, t) ∈ T.source :=
        hTclosed (a := (q.1, t)) ⟨sphere_subset_closedBall q.2, mem_univ t⟩
      have hqo : C.tube (q.1, k t) ∈ S ∩ {y | H y = k t} :=
        holdk ▸ (mem_range_self q)
      refine ⟨?_, hTh _⟩
      change T (q.1, t) ∈ S
      rw [hTp _ hqs]
      apply (htransport (k t) t hkJ htJ _).mpr
      rw [hrec _ _ hqo.2]
      exact hqo.1
    · intro hy
      let a := L.symm (Y (k t) ((Y t).symm (L y).1), k t)
      have haS : a ∈ S := by
        apply (htransport t (k t) htJ hkJ y).mpr
        rw [hrec y t hy.2]
        exact hy.1
      have haH : H a = k t := hLh _ _
      have hao : a ∈ range (fun q : UnitCircle => C.tube (q.1, k t)) :=
        holdk.symm ▸ ⟨haS, haH⟩
      obtain ⟨q, hq⟩ := hao
      refine ⟨q, ?_⟩
      change T (q.1, t) = y
      change C.tube (q.1, k t) = a at hq
      have hqs : (q.1, t) ∈ T.source :=
        hTclosed (a := (q.1, t)) ⟨sphere_subset_closedBall q.2, mem_univ t⟩
      rw [hTp _ hqs, hq]
      dsimp only [a]
      rw [L.apply_symm_apply, (Y (k t)).symm_apply_apply, (Y t).apply_symm_apply]
      exact hrec y t hy.2
  have hcircle (t : ℝ) (ht : t ∈ Icc (z - gamma) (ell + gamma)) :
      T '' (sphere (0 : E2) 1 ×ˢ ({t} : Set ℝ)) = S ∩ {y | H y = t} := by
    rw [← hTrange t ht]
    ext y
    constructor
    · rintro ⟨⟨x, s⟩, ⟨hx, hs⟩, rfl⟩
      have hst : s = t := hs
      subst s
      exact ⟨⟨x, hx⟩, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨(q.1, t), ⟨q.2, mem_singleton _⟩, rfl⟩
  let o := min (C.overlapWidth / 2) (gamma / (4 * C.scale))
  let w := min (C.collarWidth / 2) (C.scale / (4 * |C.beta|))
  have hbeta : 0 < |C.beta| := abs_pos.mpr C.beta_ne
  have ho : 0 < o := lt_min (div_pos C.overlap_pos (by norm_num))
    (div_pos hg (mul_pos (by norm_num) C.scale_pos))
  have how : o ≤ C.overlapWidth := by
    have hh := min_le_left (C.overlapWidth / 2) (gamma / (4 * C.scale))
    change o ≤ C.overlapWidth / 2 at hh
    linarith [C.overlap_pos]
  have hos : C.scale * o < gamma / 2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) C.scale_pos)).mp
      (min_le_right (C.overlapWidth / 2) (gamma / (4 * C.scale)))
    change o * (4 * C.scale) ≤ gamma at hh
    nlinarith
  have hw : 0 < w := lt_min (div_pos C.collar_pos (by norm_num))
    (div_pos C.scale_pos (mul_pos (by norm_num) hbeta))
  have hww : w ≤ C.collarWidth := by
    have hh := min_le_left (C.collarWidth / 2) (C.scale / (4 * |C.beta|))
    change w ≤ C.collarWidth / 2 at hh
    linarith [C.collar_pos]
  have hwb : |C.beta| * w < C.scale / 2 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num) hbeta)).mp
      (min_le_right (C.collarWidth / 2) (C.scale / (4 * |C.beta|)))
    change w * (4 * |C.beta|) ≤ C.scale at hh
    nlinarith [C.scale_pos]
  have hcapS (q : UnitTwoSphere) :
      ((C.profile.model q).1,
        C.cutHeight + C.sign * (C.removal + C.scale * (C.profile.model q).2)) ∈
          C.tube.source := C.tube_source
    ⟨mem_closedBall_zero_iff.mpr (C.profile.model_fst_norm_le q), mem_univ _⟩
  have hcapH (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 < o) :
      ell - gamma < C.cutHeight + C.sign *
        (C.removal + C.scale * (C.profile.model q).2) := by
    rw [hsign, neg_one_mul]
    by_cases hq0 : (heightCoordinates (q : E3)).2 ≤ 0
    · have hh : (C.profile.model q).2 ≤ 0 :=
        (surgeryCapModel_snd_nonpos_iff _ _ _ _ _ _ C.profile.vertical_pos q).mpr hq0
      have hmul := mul_nonpos_of_nonneg_of_nonpos C.scale_pos.le hh
      dsimp only [ell]
      linarith
    · have hqpos : 0 < (heightCoordinates (q : E3)).2 := lt_of_not_ge hq0
      have hv : |(heightCoordinates (q : E3)).2| ≤ 1 / 4 := by
        rw [abs_of_pos hqpos]
        exact hq.le.trans (how.trans C.overlap_le)
      have hm := surgeryCapModel_cylinder C.profile.horizontal C.profile.vertical
        C.profile.horizontal_smooth C.profile.vertical_smooth
        (fun t => (C.profile.horizontal_pos t).ne')
        (fun x => (C.profile.vertical_pos x).ne') C.profile.horizontal_near
        C.profile.vertical_far q hv
      have hh : (C.profile.model q).2 = (heightCoordinates (q : E3)).2 := by
        simpa only [SurgeryCapProfile.model] using congrArg Prod.snd hm
      rw [hh]
      have hmul := mul_lt_mul_of_pos_left hq C.scale_pos
      dsimp only [ell]
      linarith
  have hcentral (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 < o) :
      j (C.sourceChart q) = C.profile.capMap T C.cutHeight C.sign C.removal C.scale q := by
    change psi (C.sourceChart q, 0) = _
    rw [C.central_eq q (hq.trans_le how), SurgeryCapProfile.capMap_apply,
      SurgeryCapProfile.capMap_apply]
    exact (hTold _ (hcapS q) ((C.profile.model_fst_norm_le q).trans_lt hr)
      (hcapH q hq)).1.symm
  have hcap : C.cap = (fun q : UnitTwoSphere =>
      T ((C.profile.model q).1, ell - C.scale * (C.profile.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
    change j '' (C.sourceChart '' {q : UnitTwoSphere |
      (heightCoordinates (q : E3)).2 ≤ 0}) = _
    rw [image_image]
    apply image_congr
    intro q hq
    rw [hcentral q (hq.trans_lt ho), SurgeryCapProfile.capMap_apply, hsign]
    congr 1
    apply Prod.ext
    · rfl
    · dsimp only [ell]
      ring
  have hcollar (x : E2) (hx : ‖x‖ ≤ 1 / 8) (s : ℝ) (hs : |s| < w) :
      psi (C.flatChart x, s) =
        T (x, C.cutHeight + C.sign * (C.removal - C.scale) + C.beta * s) := by
    rw [C.collar_eq x hx s (hs.trans_le hww)]
    apply (hTold _ ?_ ?_ ?_).1.symm
    · exact C.tube_source ⟨mem_closedBall_zero_iff.mpr (by linarith), mem_univ _⟩
    · dsimp only
      linarith
    · have hb : -(C.scale / 2) < C.beta * s := by
        have hh : |C.beta * s| < C.scale / 2 := by
          rw [abs_mul]
          exact (mul_lt_mul_of_pos_left hs hbeta).trans hwb
        exact (abs_lt.mp hh).1
      dsimp only
      rw [hsign, neg_one_mul]
      dsimp only [ell]
      linarith [C.scale_pos]
  exact ⟨r, gamma, o, w, T, hr, hg, hgap, ho, how, hos, hw, hww, hwb,
    hTs, hTclosed, hT, hTi, fun p _ => hTh p, hTih, hTold,
    hcentral, hcollar, hcap, hcircle⟩

end PoincareConjecture.M25.Topology3D
