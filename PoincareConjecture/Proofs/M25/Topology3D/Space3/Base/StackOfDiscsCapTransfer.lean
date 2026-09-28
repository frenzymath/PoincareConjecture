import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCapEndCaller
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ScaledBallChart











set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

local notation "P" => (ℝ × E2)



theorem stackCanonicalCap_image_eq_of_annular_match
    (T Q : OpenPartialHomeomorph P P)
    (hT : ContDiffOn ℝ ∞ T T.source) (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hQ : ContDiffOn ℝ ∞ Q Q.source) (hQi : ContDiffOn ℝ ∞ Q.symm Q.target)
    (hTh : ∀ p ∈ T.source, (T p).1 = p.1)
    (hQh : ∀ p ∈ Q.source, (Q p).1 = p.1)
    (s sigma lambda gamma delta : ℝ)
    (hsigma : |sigma| = 1) (hlambda : 0 < lambda) (hlg : lambda < gamma)
    (hdelta : 0 < delta)
    (hTs : Icc (s - gamma) (s + gamma) ×ˢ closedBall (0 : E2) 1 ⊆ T.source)
    (hQs : Icc (s - gamma) (s + gamma) ×ˢ closedBall (0 : E2) 1 ⊆ Q.source)
    (hmatch : ∀ z ∈ Icc (s - gamma) (s + gamma), ∀ x : E2,
      |‖x‖ - 1| < delta → T (z, x) = Q (z, x))
    (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hrann : 1 - delta < rFlat)
    (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let Y := (fun q : UnitTwoSphere =>
      (s + sigma * lambda * (M (heightCoordinates (q : E3))).2,
        (M (heightCoordinates (q : E3))).1)) '' Qminus
    Y ⊆ T.source ∧ Y ⊆ Q.source ∧ T '' Y = Q '' Y := by
  have hfiber (V : OpenPartialHomeomorph P P)
      (hV : ContDiffOn ℝ ∞ V V.source) (hVi : ContDiffOn ℝ ∞ V.symm V.target)
      (hVh : ∀ p ∈ V.source, (V p).1 = p.1)
      (z : ℝ) (hz : ∀ x ∈ closedBall (0 : E2) 1, (z, x) ∈ V.source) :
      ∃ N : BallNeighborhoodChart E2 E2,
        N.chart.source = {x | (z, x) ∈ V.source} ∧
        (∀ x, N.chart x = (V (z, x)).2) ∧
        (∀ y, N.chart.symm y = (V.symm (z, y)).2) := by
    have hVih (p : P) (hp : p ∈ V.target) : (V.symm p).1 = p.1 := by
      have hh := hVh (V.symm p) (V.map_target hp)
      rw [V.right_inv hp] at hh
      exact hh.symm
    have hf : ContDiffOn ℝ ∞ (fun x : E2 => (V (z, x)).2)
        {x | (z, x) ∈ V.source} :=
      (hV.comp (contDiff_prodMk_right z).contDiffOn (fun _ hx => hx)).snd
    have hi : ContDiffOn ℝ ∞ (fun y : E2 => (V.symm (z, y)).2)
        {y | (z, y) ∈ V.target} :=
      (hVi.comp (contDiff_prodMk_right z).contDiffOn (fun _ hy => hy)).snd
    have hforward (x : E2) (hx : (z, x) ∈ V.source) :
        (z, (V (z, x)).2) = V (z, x) := Prod.ext (hVh (z, x) hx).symm rfl
    have hinverse (y : E2) (hy : (z, y) ∈ V.target) :
        (z, (V.symm (z, y)).2) = V.symm (z, y) := Prod.ext (hVih (z, y) hy).symm rfl
    let e : OpenPartialHomeomorph E2 E2 := {
      toFun := fun x => (V (z, x)).2
      invFun := fun y => (V.symm (z, y)).2
      source := {x | (z, x) ∈ V.source}
      target := {y | (z, y) ∈ V.target}
      map_source' := by
        intro x hx
        change (z, (V (z, x)).2) ∈ V.target
        rw [hforward x hx]
        exact V.map_source hx
      map_target' := by
        intro y hy
        change (z, (V.symm (z, y)).2) ∈ V.source
        rw [hinverse y hy]
        exact V.map_target hy
      left_inv' := by
        intro x hx
        rw [hforward x hx, V.left_inv hx]
      right_inv' := by
        intro y hy
        rw [hinverse y hy, V.right_inv hy]
      open_source := V.open_source.preimage (continuous_const.prodMk continuous_id)
      open_target := V.open_target.preimage (continuous_const.prodMk continuous_id)
      continuousOn_toFun := hf.continuousOn
      continuousOn_invFun := hi.continuousOn }
    exact ⟨⟨e, hz, hf, hi⟩, rfl, fun _ => rfl, fun _ => rfl⟩
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let f : UnitTwoSphere → P := fun q =>
    (s + sigma * lambda * (M (heightCoordinates (q : E3))).2,
      (M (heightCoordinates (q : E3))).1)
  let Y := f '' Qminus
  let zflat := s - sigma * lambda
  let Flat : Set P := {zflat} ×ˢ closedBall (0 : E2) rFlat
  have hr1 : rFlat < 1 := hradii.trans hrOne
  have hgeom (q : UnitTwoSphere) (hq : q ∈ Qminus) :=
    stackCanonicalModel_southern_geometry rFlat rOne v0 v1
      hrFlat hradii hrOne hv0 hv01 hv1 hgap
      (heightCoordinates (q : E3)) (sphere_height_coordinates_sq q) hq
  have hheight (v : ℝ) (hv : |v| ≤ 1) :
      s + sigma * lambda * v ∈ Icc (s - gamma) (s + gamma) := by
    have hh : |sigma * lambda * v| ≤ lambda := by
      rw [abs_mul, abs_mul, hsigma, abs_of_pos hlambda, one_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hv hlambda.le
    have h := abs_le.mp hh
    constructor <;> linarith
  have hpoint (q : UnitTwoSphere) (hq : q ∈ Qminus) :
      f q ∈ Icc (s - gamma) (s + gamma) ×ˢ closedBall (0 : E2) 1 := by
    have hg := hgeom q hq
    exact ⟨hheight _ (abs_le.mpr ⟨hg.2.2.1, hg.2.2.2.1.trans zero_le_one⟩),
      mem_closedBall_zero_iff.mpr hg.2.1⟩
  have hflatheight : zflat ∈ Icc (s - gamma) (s + gamma) := by
    simpa only [mul_neg_one, ← sub_eq_add_neg] using hheight (-1) (by norm_num)
  have hflatY : Flat ⊆ Y := by
    rintro ⟨z, x⟩ ⟨hz, hx⟩
    have hz' : z = zflat := hz
    subst z
    have hxnorm := mem_closedBall_zero_iff.mp hx
    refine ⟨southSpherePoint x, ?_, ?_⟩
    · change (heightCoordinates (southSpherePoint x : E3)).2 ≤ 0
      rw [southSpherePoint_coordinates _ (hxnorm.trans_lt hr1)]
      exact neg_nonpos.mpr (Real.sqrt_nonneg _)
    · have hflat := (stackCanonicalModel_flat_disc rFlat rOne v0 v1
        hrFlat hradii hrOne hv0 hv01 hv1 hgap).1 x hxnorm
      change M (heightCoordinates (southSpherePoint x : E3)) = (x, -1) at hflat
      change (s + sigma * lambda * (M (heightCoordinates (southSpherePoint x : E3))).2,
        (M (heightCoordinates (southSpherePoint x : E3))).1) = _
      rw [hflat]
      exact Prod.ext (by dsimp [zflat]; ring) rfl
  let R : E2 ≃L[ℝ] E2 :=
    (LinearEquiv.smulOfNeZero ℝ E2 rFlat hrFlat.ne').toContinuousLinearEquiv
  have hscaled : (fun x : E2 => R x) '' closedBall (0 : E2) 1 =
      closedBall (0 : E2) rFlat :=
    scaledBallNeighborhoodChart_closedRegion rFlat hrFlat
  have hrescale (V : OpenPartialHomeomorph P P)
      (hV : ContDiffOn ℝ ∞ V V.source) (hVi : ContDiffOn ℝ ∞ V.symm V.target)
      (hVh : ∀ p ∈ V.source, (V p).1 = p.1)
      (hVs : Icc (s - gamma) (s + gamma) ×ˢ closedBall (0 : E2) 1 ⊆ V.source) :
      ∃ N : BallNeighborhoodChart E2 E2,
        (∀ x : E2, N.chart x = (V (zflat, R x)).2) ∧
        N.closedRegion = (fun x : E2 => (V (zflat, x)).2) '' closedBall (0 : E2) rFlat := by
    obtain ⟨N0, _hNs, hNf, _hNi⟩ := hfiber V hV hVi hVh zflat
      (fun _ hx => hVs ⟨hflatheight, hx⟩)
    let n := R.toHomeomorph.transOpenPartialHomeomorph N0.chart
    have hns : closedBall (0 : E2) 1 ⊆ n.source := by
      intro x hx
      apply N0.closedBall_subset_source
      apply mem_closedBall_zero_iff.mpr
      change ‖rFlat • x‖ ≤ 1
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrFlat]
      have hx' := mem_closedBall_zero_iff.mp hx
      nlinarith only [hx', hrFlat, hr1]
    let N : BallNeighborhoodChart E2 E2 := ⟨n, hns,
      N0.smooth.comp R.contDiff.contDiffOn (fun _ hx => hx),
      R.symm.contDiff.comp_contDiffOn N0.smooth_symm⟩
    have hform (x : E2) : N.chart x = (V (zflat, R x)).2 := hNf (R x)
    refine ⟨N, hform, ?_⟩
    change N.chart '' closedBall (0 : E2) 1 = _
    calc
      N.chart '' closedBall (0 : E2) 1 =
          (fun x : E2 => (V (zflat, R x)).2) '' closedBall (0 : E2) 1 :=
        image_congr (fun x _ => hform x)
      _ = (fun x : E2 => (V (zflat, x)).2) '' (R '' closedBall (0 : E2) 1) :=
        (image_image (fun x : E2 => (V (zflat, x)).2) (fun x : E2 => R x)
          (closedBall (0 : E2) 1)).symm
      _ = _ := by rw [hscaled]
  obtain ⟨NT, hNT, hNTregion⟩ := hrescale T hT hTi hTh hTs
  obtain ⟨NQ, hNQ, hNQregion⟩ := hrescale Q hQ hQi hQh hQs
  have hbound : NT.boundary = NQ.boundary := by
    apply image_congr
    intro x hx
    rw [hNT, hNQ, hmatch zflat hflatheight]
    change |‖rFlat • x‖ - 1| < delta
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrFlat,
      mem_sphere_zero_iff_norm.mp hx, mul_one, abs_of_neg (sub_neg.mpr hr1)]
    linarith only [hrann, hdelta]
  have hregion :
      (fun x : E2 => (T (zflat, x)).2) '' closedBall (0 : E2) rFlat =
        (fun x : E2 => (Q (zflat, x)).2) '' closedBall (0 : E2) rFlat := by
    rw [← hNTregion, ← hNQregion]
    exact NT.closedRegion_eq_of_boundary_eq NQ
      (Module.one_lt_rank_of_one_lt_finrank (by simp [E2])) hbound
  have hflatImage (V : OpenPartialHomeomorph P P)
      (hVh : ∀ p ∈ V.source, (V p).1 = p.1)
      (hVs : Icc (s - gamma) (s + gamma) ×ˢ closedBall (0 : E2) 1 ⊆ V.source) :
      V '' Flat = (fun y : E2 => (zflat, y)) ''
        ((fun x : E2 => (V (zflat, x)).2) '' closedBall (0 : E2) rFlat) := by
    rw [image_image]
    apply Subset.antisymm
    · rintro _ ⟨⟨z, x⟩, ⟨hz, hx⟩, rfl⟩
      have hz' : z = zflat := hz
      subst z
      refine ⟨x, hx, Prod.ext ?_ rfl⟩
      exact (hVh (zflat, x) (hVs ⟨hflatheight, closedBall_subset_closedBall hr1.le hx⟩)).symm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨(zflat, x), ⟨rfl, hx⟩, Prod.ext ?_ rfl⟩
      exact hVh (zflat, x) (hVs ⟨hflatheight, closedBall_subset_closedBall hr1.le hx⟩)
  have hflatEqual : T '' Flat = Q '' Flat := by
    rw [hflatImage T hTh hTs, hflatImage Q hQh hQs, hregion]
  have htransfer (V W : P → P)
      (hflat : V '' Flat = W '' Flat)
      (hVW : ∀ q ∈ Qminus, rFlat < ‖(M (heightCoordinates (q : E3))).1‖ →
        V (f q) = W (f q)) : V '' Y ⊆ W '' Y := by
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    by_cases hf : ‖(M (heightCoordinates (q : E3))).1‖ ≤ rFlat
    · have hg := hgeom q hq
      have he := hg.2.2.2.2.1 hf
      change M (heightCoordinates (q : E3)) = ((heightCoordinates (q : E3)).1, -1) at he
      have hp : f q ∈ Flat := by
        refine ⟨?_, mem_closedBall_zero_iff.mpr hf⟩
        change s + sigma * lambda * (M (heightCoordinates (q : E3))).2 = zflat
        rw [he]
        dsimp [zflat]
        ring
      exact image_mono hflatY (hflat ▸ mem_image_of_mem V hp)
    · exact ⟨f q, ⟨q, hq, rfl⟩, (hVW q hq (lt_of_not_ge hf)).symm⟩
  have hpointMatch (q : UnitTwoSphere) (hq : q ∈ Qminus)
      (hr : rFlat < ‖(M (heightCoordinates (q : E3))).1‖) : T (f q) = Q (f q) := by
    apply hmatch _ (hpoint q hq).1
    have hnorm := (hgeom q hq).2.1
    exact abs_lt.mpr ⟨by linarith only [hr, hrann],
      (sub_nonpos.mpr hnorm).trans_lt hdelta⟩
  refine ⟨?_, ?_, Subset.antisymm (htransfer T Q hflatEqual hpointMatch)
    (htransfer Q T hflatEqual.symm (fun q hq hr => (hpointMatch q hq hr).symm))⟩
  · rintro _ ⟨q, hq, rfl⟩
    exact hTs (hpoint q hq)
  · rintro _ ⟨q, hq, rfl⟩
    exact hQs (hpoint q hq)



theorem exists_stackCapNormalization_in_matched_chart
    {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}
    (C : SurgeryCapTag psi u) (hpsi : IsCollarEmbedding psi)
    (K L : Set E3) (hK : IsCompact K) (hL : IsCompact L)
    (gap : ℝ) (hgap : 0 < gap)
    (hcover : range (fun q => psi (q, 0)) = K ∪ C.cap ∪ L)
    (hseam : C.seam ⊆ K)
    (hKside : ∀ y ∈ K, 0 ≤ C.sign * (⟪(u : E3), y⟫_ℝ -
      (C.cutHeight + C.sign * C.removal)))
    (hLside : ∀ y ∈ L, gap ≤ C.sign * (⟪(u : E3), y⟫_ℝ -
      (C.cutHeight + C.sign * C.removal)))
    (R : E2 ≃ₗᵢ[ℝ] E2) (Q : OpenPartialHomeomorph P P)
    (hQ : ContDiffOn ℝ ∞ Q Q.source) (hQi : ContDiffOn ℝ ∞ Q.symm Q.target)
    (hQh : ∀ p ∈ Q.source, (Q p).1 = p.1)
    (gamma delta : ℝ) (hgamma : 0 < gamma) (hdelta : 0 < delta)
    (hQs : Icc (C.cutHeight + C.sign * C.removal - gamma)
      (C.cutHeight + C.sign * C.removal + gamma) ×ˢ closedBall (0 : E2) 1 ⊆ Q.source)
    (hmatch : ∀ z ∈ Icc (C.cutHeight + C.sign * C.removal - gamma)
      (C.cutHeight + C.sign * C.removal + gamma), ∀ x : E2,
      |‖x‖ - 1| < delta → stackCapEndChart C R (z, x) = Q (z, x))
    (rFlat rOne v0 v1 : ℝ)
    (hrFlat : 0 < rFlat) (hrann : 1 - delta < rFlat)
    (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hprofileGap : v1 ^ 2 + rOne ^ 2 < 1) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    let s := C.cutHeight + C.sign * C.removal
    let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let Hinv := fun p : P => (heightPlaneCoordinates u).symm (p.2, p.1)
    ∃ lambda : ℝ, 0 < lambda ∧ lambda < C.scale ∧ lambda < gamma / 2 ∧
      ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞, ∃ Nopp : Set E3,
        let Y := (fun q : UnitTwoSphere =>
          (s + C.sign * lambda * (M (heightCoordinates (q : E3))).2,
            (M (heightCoordinates (q : E3))).1)) '' Qminus
        IsCollarEmbedding (fun p => F (psi p)) ∧
        IsOpen Nopp ∧ L ⊆ Nopp ∧
        (∀ y ∈ Nopp, F y = y ∧ F.symm y = y) ∧
        F '' K = K ∧ F.symm '' K = K ∧
        (∀ y ∈ C.seam, F y = y ∧ F.symm y = y) ∧
        (∀ q ∈ Qminus,
          F (C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q) =
            stackCapCanonicalEndpoint C rFlat rOne v0 v1 lambda q) ∧
        Y ⊆ Q.source ∧ F '' C.cap = Hinv '' (Q '' Y) ∧
        F.symm '' (Hinv '' (Q '' Y)) = C.cap ∧
        K ∩ (Hinv '' (Q '' Y)) = C.seam ∧ Disjoint (Hinv '' (Q '' Y)) L ∧
        range (fun q : UnitTwoSphere => F (psi (q, 0))) = K ∪ (Hinv '' (Q '' Y)) ∪ L := by
  obtain ⟨B, lambda, _hB, hlambda, hscale, _hlB, _hbound,
      FA, FB, SA, NB, KB, hrest⟩ :=
    exists_stackCapCanonicalNormalization C hpsi K L hK hL gap hgap hcover hseam hKside hLside
      rFlat rOne v0 v1 hrFlat hradii hrOne hv0 hv01 hv1 hprofileGap
      gamma gamma hgamma hgamma
  obtain ⟨_hSA, _hKB, _hNB, _hseamNB, _hNBtube, _hSAsub, _hKBsub,
      _hAsup, _hAisup, _hBsup, _hBisup, _hAfix, _hBfix, _hBfixNB, _hBside,
      _hAK, _hAiK, _hAtrack, _hBtrack, hcollar, _hSc, hNopp, hLN, _hSL,
      _hSsub, _hFs, _hFis, _hFout, hFopp, _hFside, hFK, hFiK, hFseam, hFtrack,
      hFcap, hFicap, hKcap, hcapL, _hcore, hcoverF, hsmall, _hsmall', _hrem, _hheight⟩ := hrest
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let s := C.cutHeight + C.sign * C.removal
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let f : UnitTwoSphere → P := fun q =>
    (s + C.sign * lambda * (M (heightCoordinates (q : E3))).2,
      (M (heightCoordinates (q : E3))).1)
  let Y := f '' Qminus
  let T := stackCapEndChart C R
  let H := (heightPlaneCoordinates u).trans (ContinuousLinearEquiv.prodComm ℝ E2 ℝ)
  let endpoint := stackCapCanonicalEndpoint C rFlat rOne v0 v1 lambda
  obtain ⟨_, _, _, _, hT, hTi, hTs, hTh, _hTih⟩ := stackCapEndChart_spec C R
  have hTsource : Icc (s - gamma) (s + gamma) ×ˢ closedBall (0 : E2) 1 ⊆ T.source :=
    fun _ hp => hTs ⟨mem_univ _, hp.2⟩
  obtain ⟨_hYT, hYQ, himage⟩ := stackCanonicalCap_image_eq_of_annular_match
    T Q hT hTi hQ hQi hTh hQh s C.sign lambda gamma delta C.sign_abs hlambda
      (by linarith only [hsmall, hgamma]) hdelta hTsource hQs hmatch
      rFlat rOne v0 v1 hrFlat hrann hradii hrOne hv0 hv01 hv1 hprofileGap
  obtain ⟨_hpoint, _hrot, hcoords, _hheights⟩ := stackCanonicalEndpoint_capEndChart
    C R rFlat rOne v0 v1 lambda hrFlat hradii hrOne hv0 hv01 hv1 hprofileGap hlambda
  have hHimage : H '' (endpoint '' Qminus) = Q '' Y := by
    calc
      H '' (endpoint '' Qminus) = (fun q : UnitTwoSphere => T (f q)) '' Qminus := hcoords
      _ = T '' Y := (image_image T f Qminus).symm
      _ = Q '' Y := himage
  have hendpoint : endpoint '' Qminus = H.symm '' (Q '' Y) := by
    rw [← hHimage, image_image]
    simp only [H.symm_apply_apply, image_id']
  refine ⟨lambda, hlambda, hscale, hsmall, FA.trans FB, (SA ∪ KB)ᶜ,
    hcollar, hNopp, hLN, hFopp, hFK, hFiK, hFseam, hFtrack, hYQ, ?_, ?_, ?_, ?_, ?_⟩
  · exact hFcap.trans hendpoint
  · change (FA.trans FB).symm '' (H.symm '' (Q '' Y)) = C.cap
    rw [← hendpoint]
    exact hFicap
  · change K ∩ (H.symm '' (Q '' Y)) = C.seam
    rw [← hendpoint]
    exact hKcap
  · change Disjoint (H.symm '' (Q '' Y)) L
    rw [← hendpoint]
    exact hcapL
  · change range (fun q : UnitTwoSphere => (FA.trans FB) (psi (q, 0))) =
      K ∪ (H.symm '' (Q '' Y)) ∪ L
    rw [← hendpoint]
    exact hcoverF

end PoincareConjecture.M25.Topology3D
