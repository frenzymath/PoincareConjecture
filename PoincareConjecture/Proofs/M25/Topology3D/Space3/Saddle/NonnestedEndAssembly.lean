import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.TargetThreeEndReplacement
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceMovedEndReplacement
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ThreeCapAlignment
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ConnectedUpperLevel
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HeightTubeTransport
import Mathlib.Tactic










set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D



theorem exists_saddle_nonnested_end_assembly
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D)
    (hnonnested : Disjoint (W.disc 0).closedRegion (W.disc 1).closedRegion)
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdNear : ∀ q : ℝ, 0 ≤ q → q ≤ sigma / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (hdDeriv : ∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (A : Diffeomorph 𝓘(ℝ, (ℝ × ℝ) × ℝ) 𝓘(ℝ, E3)
      ((ℝ × ℝ) × ℝ) E3 ∞)
    (nu delta : ℝ) (hnu : 0 < nu) (hdelta : 0 < delta)
    (hcut : W.level < ⟪(u : E3), psi (D.point, 0)⟫_ℝ - delta)
    (hA : ∀ x : (ℝ × ℝ) × ℝ,
      ⟪(u : E3), A x⟫_ℝ = ⟪(u : E3), psi (D.point, 0)⟫_ℝ + nu * x.2)
    (G : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
    (hGheight : ∀ y : E3, ⟪(u : E3), G y⟫_ℝ = ⟪(u : E3), y⟫_ℝ)
    (hGlevels : ∀ t : ℝ, |t| ≤ delta →
      G '' (range (fun q : UnitTwoSphere =>
        A (nonnestedReferenceDiffeomorph 0 d hd (q : E3))) ∩
          {y : E3 | ⟪(u : E3), y⟫_ℝ = ⟪(u : E3), psi (D.point, 0)⟫_ℝ + t}) =
        range (fun q : UnitTwoSphere => psi (q, 0)) ∩
          {y : E3 | ⟪(u : E3), y⟫_ℝ = ⟪(u : E3), psi (D.point, 0)⟫_ℝ + t}) :
    ∃ K : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞,
      K '' range (fun q : UnitTwoSphere => psi (q, 0)) =
        A '' (nonnestedReferenceBallChart 0 d hd).boundary := by
  classical
  let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
  let c := H (psi (D.point, 0))
  let S : Set E3 := range (fun q : UnitTwoSphere => psi (q, 0))
  change ∀ x, H (A x) = c + nu * x.2 at hA
  change ∀ y, H (G y) = H y at hGheight
  obtain ⟨P⟩ := exists_surgery_cap_profile
  let alpha := min delta (nu / 8) / 2
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have haDelta : alpha < delta := by
    have hh := min_le_left delta (nu / 8)
    dsimp [alpha]
    linarith only [hh, hdelta]
  have haNu : alpha ≤ nu / 16 := by
    have hh := min_le_right delta (nu / 8)
    dsimp [alpha]
    linarith only [hh]
  let m := c - alpha
  have hmc : m < c := by dsimp [m]; linarith only [halpha]
  have hm : W.level < m := by
    change W.level < c - delta at hcut
    dsimp [m]
    linarith only [hcut, haDelta]
  have hmBand : c - m < delta := by dsimp [m]; linarith only [haDelta]
  let epsilonU := min delta nu / 2
  have hepsilonU : 0 < epsilonU := by dsimp [epsilonU]; positivity
  obtain ⟨beta, hbeta, hbE, _hbW, _hcore, hseams, hconnected⟩ :=
    exists_saddle_connected_upper_level psi hpsi u D W epsilonU hepsilonU
  let v := c + beta
  have hcv : c < v := by dsimp [v]; linarith only [hbeta]
  have hvBand : v - c < delta := by
    have hh := min_le_left delta nu
    change beta < min delta nu / 2 at hbE
    dsimp [v]
    linarith only [hbE, hh, hdelta]
  have hbNu : beta < nu / 2 := by
    have hh := min_le_right delta nu
    change beta < min delta nu / 2 at hbE
    linarith only [hbE, hh]
  let mn := (m - c) / nu
  let pn := (v - c) / nu
  have hmnId : nu * mn = m - c := mul_div_cancel₀ _ hnu.ne'
  have hpnId : nu * pn = v - c := mul_div_cancel₀ _ hnu.ne'
  have hmn : mn ∈ Ioo (-1 / 4 : ℝ) 0 := by
    constructor
    · apply (lt_div_iff₀ hnu).2
      dsimp [m]
      linarith only [haNu, hnu]
    · exact div_neg_of_neg_of_pos (sub_neg.mpr hmc) hnu
  have hpn : pn ∈ Ioo (0 : ℝ) 2 := by
    refine ⟨div_pos (sub_pos.mpr hcv) hnu, (div_lt_iff₀ hnu).2 ?_⟩
    dsimp [v]
    linarith only [hbNu, hnu]
  obtain ⟨bT, TT, O, hbT, _hbTdelta, _hbTm, _hbTv, hTT,
      hO, hOdis, hTCircleL, hTCircleU, hTargetLater⟩ :=
    exists_saddle_target_three_end_replacement hP psi hpsi u D W hnonnested
      P m v delta hm hmc hcv
      (fun i hi => by
        have hh := hseams i hi
        change c + 3 * beta < _ at hh
        dsimp [v]
        linarith only [hh, hbeta])
      hconnected hdelta
  let L := heightPlaneCoordinates u
  let C : ((ℝ × ℝ) × ℝ) ≃L[ℝ] E3 :=
    (J2.symm.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)).trans L.symm
  let F0 := nonnestedReferenceDiffeomorph 0 d hd
  let Fn : E3 → E3 := fun y => C (F0 y)
  let Sn : Set E3 := range (fun q : UnitTwoSphere => Fn (q : E3))
  let Rn : Set E3 := Sn ∩ {y | mn ≤ H y ∧ H y ≤ pn}
  let R : Set E3 := S ∩ {y | m ≤ H y ∧ H y ≤ v}
  let cutN : Fin 3 → ℝ := ![mn, mn, pn]
  let cut : Fin 3 → ℝ := ![m, m, v]
  let sign : Fin 3 → ℝ := ![1, 1, -1]
  obtain ⟨_hNativeCollar, _hNativeSphere, bN, TN, hbN, _hbNOne,
      hbNCuts, _hbNOld, hTN, hNativeLater⟩ :=
    exists_nonnested_reference_moved_end_replacement sigma hsigma hsigmaSmall
      d hd hdNear hdZero hdBounds hdDeriv J2 hJ2 u P mn pn 1 hmn hpn (by norm_num)
  let Placement := C.symm.toDiffeomorph.trans A
  let J := Placement.trans G
  have hCheight (y : E3) : (C.symm y).2 = H y := by
    change (L y).2 = H y
    exact heightPlaneCoordinates_snd u y
  have hPlacementHeight (y : E3) : H (Placement y) = c + nu * H y := by
    change H (A (C.symm y)) = _
    rw [hA, hCheight]
  have hJheight (y : E3) : H (J y) = c + nu * H y := by
    change H (G (Placement y)) = _
    rw [hGheight, hPlacementHeight]
  have hPlacementPoint (q : UnitTwoSphere) : Placement (Fn q) = A (F0 q) := by
    change A (C.symm (C (F0 q))) = _
    rw [C.symm_apply_apply]
  have hPlacementSurface : Placement '' Sn =
      range (fun q : UnitTwoSphere => A (F0 q)) := by
    ext y
    constructor
    · rintro ⟨x, ⟨q, rfl⟩, rfl⟩
      exact ⟨q, (hPlacementPoint q).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨Fn q, ⟨q, rfl⟩, hPlacementPoint q⟩
  have hPlacementSlice (k : ℝ) :
      Placement '' (Sn ∩ {y | H y = k}) =
        range (fun q : UnitTwoSphere => A (F0 q)) ∩ {y | H y = c + nu * k} := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hk⟩, rfl⟩
      refine ⟨hPlacementSurface ▸ mem_image_of_mem Placement hx, ?_⟩
      change H (Placement x) = c + nu * k
      rw [hPlacementHeight, hk]
    · intro hy
      obtain ⟨x, hx, rfl⟩ := hPlacementSurface.symm ▸ hy.1
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      have hh := hy.2
      change H (Placement x) = c + nu * k at hh
      rw [hPlacementHeight] at hh
      change H x = k
      exact mul_left_cancel₀ hnu.ne' (add_left_cancel hh)
  have hJSlice (k : ℝ) (hk : |nu * k| ≤ delta) :
      J '' (Sn ∩ {y | H y = k}) = S ∩ {y | H y = c + nu * k} := by
    change (G ∘ Placement) '' _ = _
    rw [image_comp, hPlacementSlice]
    exact hGlevels (nu * k) hk
  let h : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
    toEquiv := {
      toFun := fun z => c + nu * z
      invFun := fun z => (z - c) / nu
      left_inv := by intro z; field_simp; ring
      right_inv := by intro z; field_simp; ring }
    contMDiff_toFun := (contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff
    contMDiff_invFun := ((contDiff_id.sub contDiff_const).div_const nu).contMDiff }
  have hh (z : ℝ) : h z = c + nu * z := rfl
  have hhi (z : ℝ) : h.symm z = (z - c) / nu := rfl
  have hhm : h mn = m := by rw [hh, hmnId]; ring
  have hhp : h pn = v := by rw [hh, hpnId]; ring
  let U : Fin 3 → OpenPartialHomeomorph (E2 × ℝ) E3 := fun i =>
    heightTransportTube (TN i) h J
  have hUs (i : Fin 3) : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ (U i).source :=
    heightTransportTube_closedDisc_source (TN i) h J (hTN i).1
  have hUt (i : Fin 3) : ContDiffOn ℝ ∞ (U i) (U i).source :=
    heightTransportTube_contDiffOn (TN i) h J (hTN i).2.1
  have hUi (i : Fin 3) : ContDiffOn ℝ ∞ (U i).symm (U i).target :=
    heightTransportTube_contDiffOn_symm (TN i) h J (hTN i).2.2.1
  have hUh (i : Fin 3) (x : E2 × ℝ) (hx : x ∈ (U i).source) : H (U i x) = x.2 :=
    heightTransportTube_height (TN i) h J u u (hTN i).2.2.2.1 hJheight x hx
  have hSlice (i : Fin 3) (B : Set E2) (z : ℝ) :
      U i '' (B ×ˢ ({z} : Set ℝ)) =
        J '' (TN i '' (B ×ˢ ({h.symm z} : Set ℝ))) := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      have htz : t = z := mem_singleton_iff.mp ht
      subst t
      exact ⟨TN i (x, h.symm z), ⟨(x, h.symm z), ⟨hx, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩, rfl⟩
      have htz : t = h.symm z := mem_singleton_iff.mp ht
      subst t
      exact ⟨(x, z), ⟨hx, rfl⟩, rfl⟩
  have hNativeHeight (x : E3) :
      H (Fn x) = 1 + x 2 - (x 1) ^ 2 + d ((x 0) ^ 2 + (x 1) ^ 2) := by
    change ⟪(u : E3), Fn x⟫_ℝ = _
    rw [← heightPlaneCoordinates_snd u]
    change (L (L.symm (J2.symm (F0 x).1, (F0 x).2))).2 = _
    rw [L.apply_symm_apply]
    change 0 + 1 + x 2 - (x 1) ^ 2 + d ((x 0) ^ 2 + (x 1) ^ 2) = _
    rw [zero_add]
  have hNativeHorizontal (q : UnitTwoSphere) :
      J2 (L (Fn q)).1 = ((q : E3) 0 / Real.sqrt 2, (q : E3) 1 / Real.sqrt 2) := by
    change J2 (L (L.symm (J2.symm (F0 q).1, (F0 q).2))).1 = _
    rw [L.apply_symm_apply, J2.apply_symm_apply]
    rfl
  have hAxis (x : E3) (hx : ‖x‖ = 1) (hx1 : x 1 = 0) : 0 ≤ H (Fn x) := by
    have hsq : (x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 = 1 := by
      have hn := EuclideanSpace.real_norm_sq_eq x
      rw [hx, one_pow, Fin.sum_univ_three] at hn
      exact hn.symm
    have hcircle : (x 0) ^ 2 + (x 2) ^ 2 = 1 := by
      simpa only [hx1, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] using hsq
    have hq0 : 0 ≤ (x 0) ^ 2 := sq_nonneg _
    have hq1 : (x 0) ^ 2 ≤ 1 := by nlinarith only [hcircle, sq_nonneg (x 2)]
    have hd0 := (hdBounds ((x 0) ^ 2) hq0).1
    have hprod := mul_nonneg hq0 (sub_nonneg.mpr hq1)
    rw [hNativeHeight, hx1, zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero, add_zero]
    nlinarith only [hcircle, hd0, hprod, sq_nonneg (1 + x 2)]
  have hNativeLower (z : ℝ) (hz : |z - mn| < bN) :
      (⋃ i : Fin 2, TN i.castSucc '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))) =
        Sn ∩ {y | H y = z} := by
    have hzneg : z < 0 := by
      have hb := hbNCuts.trans_le (min_le_left (-mn) pn)
      have hh := (abs_lt.mp hz).2
      linarith only [hb, hh]
    have h0 := (hTN 0).2.2.2.2.2 z hz
    have h1 := (hTN 1).2.2.2.2.2 z hz
    change TN 0 '' _ = Sn ∩ {y | H y = z} ∩ {y | 0 < (J2 (L y).1).2} at h0
    change TN 1 '' _ = Sn ∩ {y | H y = z} ∩ {y | (J2 (L y).1).2 < 0} at h1
    apply Subset.antisymm
    · intro y hy
      obtain ⟨i, hi⟩ := mem_iUnion.mp hy
      fin_cases i
      · exact (h0 ▸ hi).1
      · exact (h1 ▸ hi).1
    · rintro y ⟨⟨q, rfl⟩, hqz⟩
      have hq1 : (q : E3) 1 ≠ 0 := by
        intro heq
        have hh := hAxis q (norm_eq_of_mem_sphere q) heq
        change H (Fn q) = z at hqz
        linarith only [hh, hqz, hzneg]
      have hcoord : (J2 (L (Fn q)).1).2 ≠ 0 := by
        rw [hNativeHorizontal]
        exact div_ne_zero hq1 (Real.sqrt_pos.mpr (by norm_num)).ne'
      rcases lt_or_gt_of_ne hcoord with hneg | hpos
      · exact mem_iUnion.mpr ⟨1, h1.symm ▸ ⟨⟨mem_range_self q, hqz⟩, hneg⟩⟩
      · exact mem_iUnion.mpr ⟨0, h0.symm ▸ ⟨⟨mem_range_self q, hqz⟩, hpos⟩⟩
  have hNativeUpper (z : ℝ) (hz : |z - pn| < bN) :
      TN 2 '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) = Sn ∩ {y | H y = z} := by
    have hh := (hTN 2).2.2.2.2.2 z hz
    change TN 2 '' _ = Sn ∩ {y | H y = z} ∩ univ at hh
    simpa only [inter_univ] using hh
  let margin := min bT (min (nu * bN)
    (min (c - m) (min (v - c) (min (delta - (c - m)) (delta - (v - c))))))
  have hmargin : 0 < margin :=
    lt_min hbT (lt_min (mul_pos hnu hbN) (lt_min (sub_pos.mpr hmc)
      (lt_min (sub_pos.mpr hcv) (lt_min (sub_pos.mpr hmBand) (sub_pos.mpr hvBand)))))
  have hmargins : margin ≤ bT ∧ margin ≤ nu * bN ∧ margin ≤ c - m ∧
      margin ≤ v - c ∧ margin ≤ delta - (c - m) ∧ margin ≤ delta - (v - c) := by
    have hh : margin ≤ min bT (min (nu * bN)
        (min (c - m) (min (v - c) (min (delta - (c - m)) (delta - (v - c)))))) := le_rfl
    simpa only [le_min_iff] using hh
  let tau := margin / 8
  have htau : 0 < tau := div_pos hmargin (by norm_num)
  have htT : tau < bT := by dsimp [tau]; linarith only [hmargins.1, hmargin]
  have htN : tau < nu * bN := by dsimp [tau]; linarith only [hmargins.2.1, hmargin]
  have htLower : m + 4 * tau < c := by
    dsimp [tau]; linarith only [hmargins.2.2.1, hmargin]
  have htUpper : c + 4 * tau < v := by
    dsimp [tau]; linarith only [hmargins.2.2.2.1, hmargin]
  have htBandL : tau < delta - (c - m) := by
    dsimp [tau]; linarith only [hmargins.2.2.2.2.1, hmargin]
  have htBandU : tau < delta - (v - c) := by
    dsimp [tau]; linarith only [hmargins.2.2.2.2.2, hmargin]
  have hWindow (k : ℝ) (hk : k = m ∨ k = v) (z : ℝ)
      (hz : z ∈ Icc (k - tau) (k + tau)) :
      |z - c| < delta ∧ |h.symm z - h.symm k| < bN := by
    have hzabs : |z - k| ≤ tau :=
      abs_le.mpr ⟨by linarith only [hz.1], by linarith only [hz.2]⟩
    have hquot : |h.symm z - h.symm k| = |z - k| / nu := by
      rw [hhi, hhi, ← sub_div, abs_div, abs_of_pos hnu]
      congr 2
      ring
    refine ⟨?_, ?_⟩
    · apply abs_lt.mpr
      rcases hk with rfl | rfl
      · constructor <;> linarith only [hz.1, hz.2, htBandL, hmc]
      · constructor <;> linarith only [hz.1, hz.2, htBandU, hcv]
    · rw [hquot]
      exact (div_lt_iff₀ hnu).2 (hzabs.trans_lt (by simpa only [mul_comm] using htN))
  have hPhysicalSlice (z : ℝ) (hz : |z - c| ≤ delta) :
      J '' (Sn ∩ {y | H y = h.symm z}) = S ∩ {y | H y = z} := by
    have heq : c + nu * h.symm z = z := h.apply_symm_apply z
    have hband : |nu * h.symm z| ≤ delta := by
      have hh : nu * h.symm z = z - c := by linarith only [heq]
      rwa [hh]
    simpa only [heq] using hJSlice (h.symm z) hband
  have hLower (z : ℝ) (hz : z ∈ Icc (m - tau) (m + tau)) :
      (⋃ i : Fin 2, U i.castSucc '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))) =
        S ∩ {y | H y = z} ∧
      (⋃ i : Fin 2, TT i.castSucc '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ))) =
        S ∩ {y | H y = z} := by
    have hw := hWindow m (Or.inl rfl) z hz
    have hn : |h.symm z - mn| < bN := by
      rw [← hhm, h.symm_apply_apply] at hw
      exact hw.2
    refine ⟨?_, (hTCircleL z ⟨by linarith only [hz.1, htT, hbT],
      by linarith only [hz.2, htT, hbT]⟩).symm⟩
    simp_rw [hSlice]
    rw [← image_iUnion, hNativeLower (h.symm z) hn]
    exact hPhysicalSlice z hw.1.le
  have hUpper (z : ℝ) (hz : z ∈ Icc (v - tau) (v + tau)) :
      U 2 '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) = S ∩ {y | H y = z} ∧
      TT 2 '' (sphere (0 : E2) 1 ×ˢ ({z} : Set ℝ)) = S ∩ {y | H y = z} := by
    have hw := hWindow v (Or.inr rfl) z hz
    have hn : |h.symm z - pn| < bN := by
      rw [← hhp, h.symm_apply_apply] at hw
      exact hw.2
    refine ⟨?_, hTCircleU z ⟨by linarith only [hz.1, htT, hbT],
      by linarith only [hz.2, htT, hbT]⟩⟩
    rw [hSlice, hNativeUpper (h.symm z) hn]
    exact hPhysicalSlice z hw.1.le
  have hBuffer (i : Fin 2) :
      TT i.castSucc '' (closedBall (0 : E2) 1 ×ˢ Icc (m - tau) (m + tau)) ⊆ O i := by
    apply (image_mono ?_).trans (hO i).2
    exact prod_mono subset_rfl (fun z hz => ⟨by linarith only [hz.1, htT, hbT],
      by linarith only [hz.2, htT, hbT]⟩)
  have hCore : J '' Rn = R := by
    ext y
    constructor
    · rintro ⟨x, ⟨hx, hxlo, hxhi⟩, rfl⟩
      have hlow : m ≤ c + nu * H x := by
        linarith only [hmnId, mul_le_mul_of_nonneg_left hxlo hnu.le]
      have hupp : c + nu * H x ≤ v := by
        linarith only [hpnId, mul_le_mul_of_nonneg_left hxhi hnu.le]
      have hband : |nu * H x| ≤ delta :=
        abs_le.mpr ⟨by linarith only [hlow, hmBand], by linarith only [hupp, hvBand]⟩
      have hs := hJSlice (H x) hband ▸
        (mem_image_of_mem J (show x ∈ Sn ∩ {y | H y = H x} from ⟨hx, rfl⟩))
      refine ⟨hs.1, ?_, ?_⟩ <;> rw [hJheight]
      · exact hlow
      · exact hupp
    · rintro ⟨hy, hylo, hyhi⟩
      have hband : |H y - c| ≤ delta :=
        abs_le.mpr ⟨by linarith only [hylo, hmBand], by linarith only [hyhi, hvBand]⟩
      have hs : y ∈ J '' (Sn ∩ {x | H x = h.symm (H y)}) :=
        (hPhysicalSlice (H y) hband).symm ▸ ⟨hy, rfl⟩
      obtain ⟨x, ⟨hx, hxheight⟩, rfl⟩ := hs
      refine ⟨x, ⟨hx, ?_, ?_⟩, rfl⟩
      · refine le_of_mul_le_mul_left ?_ hnu
        linarith only [hJheight x, hylo, hmnId]
      · refine le_of_mul_le_mul_left ?_ hnu
        linarith only [hJheight x, hyhi, hpnId]
  obtain ⟨eta, bound, heta, _hetaTau, hbound, hMbound, hAlignLater⟩ :=
    exists_saddle_three_cap_alignment P u U TT hUt hUi
      (fun i => (hTT i).2.1) (fun i => (hTT i).2.2.1)
      hUs (fun i => (hTT i).1) hUh (fun i => (hTT i).2.2.2.1)
      S R m c v tau htau htLower htUpper inter_subset_left
      (fun _ hy => hy.2) O (fun i => (hO i).1) hOdis hBuffer hLower hUpper
  let aScale := min eta (min bT (nu * bN))
  have haScale : 0 < aScale := lt_min heta (lt_min hbT (mul_pos hnu hbN))
  have haEta : aScale ≤ eta := min_le_left _ _
  have haT : aScale ≤ bT := (min_le_right _ _).trans (min_le_left _ _)
  have haN : aScale ≤ nu * bN := (min_le_right _ _).trans (min_le_right _ _)
  have hbpos : 0 < bound := by linarith only [hbound]
  let lambda := aScale / (2 * bound)
  have hlambda : 0 < lambda := div_pos haScale (mul_pos (by norm_num) hbpos)
  have hlb : lambda * bound = aScale / 2 := by dsimp [lambda]; field_simp
  have hlEta : lambda * bound < eta := by rw [hlb]; linarith only [haEta, haScale]
  have hlM : lambda * P.heightBound ≤ aScale / 2 := by
    rw [← hlb]
    exact mul_le_mul_of_nonneg_left hMbound hlambda.le
  have hlT : lambda * P.heightBound < bT := by linarith only [hlM, haT, haScale]
  have hlN : (lambda / nu) * P.heightBound < bN := by
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ hnu).2
    rw [mul_comm bN nu]
    linarith only [hlM, haN, haScale]
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let capN : Fin 3 → Set E3 := fun i =>
    P.capMap (TN i) (cutN i) (sign i) 0 (lambda / nu) '' Qminus
  let capU : Fin 3 → Set E3 := fun i =>
    P.capMap (U i) (cut i) (sign i) 0 lambda '' Qminus
  let capT : Fin 3 → Set E3 := fun i =>
    P.capMap (TT i) (cut i) (sign i) 0 lambda '' Qminus
  obtain ⟨Gt, hGt, _hGti, _hGtHeight, _hGtCollar⟩ := hTargetLater lambda hlambda hlT
  obtain ⟨_N, Gn, _Cn, _hN, _hNdis, hGn, _hGni, _hGnFix, _hCn,
      _hCnAvoid, _hGnSupport, _hGniSupport, _hGnCollar⟩ :=
    hNativeLater (fun _ => lambda / nu) (fun _ => div_pos hlambda hnu) (fun _ => hlN)
  obtain ⟨Fa, _Ca, hFa, _hFai, _hFaFix, _hCa, _hFaSupport, _hFaiSupport⟩ :=
    hAlignLater lambda hlambda hlEta
  change Gt '' S = R ∪ ⋃ i : Fin 3, capT i at hGt
  change Gn '' Sn = Rn ∪ ⋃ i : Fin 3, capN i at hGn
  change Fa '' (R ∪ ⋃ i : Fin 3, capU i) = R ∪ ⋃ i : Fin 3, capT i at hFa
  have hCuts (i : Fin 3) : c + nu * cutN i = cut i := by
    fin_cases i
    · exact hhm
    · exact hhm
    · exact hhp
  have hCapPoint (i : Fin 3) (q : UnitTwoSphere) :
      J (P.capMap (TN i) (cutN i) (sign i) 0 (lambda / nu) q) =
        P.capMap (U i) (cut i) (sign i) 0 lambda q := by
    rw [SurgeryCapProfile.capMap_apply, SurgeryCapProfile.capMap_apply]
    have hz : h (cutN i + sign i * (0 + lambda / nu * (P.model q).2)) =
        cut i + sign i * (0 + lambda * (P.model q).2) := by
      rw [hh, ← hCuts i]
      field_simp
      ring
    rw [← hz]
    exact (heightTransportTube_reparametrized_apply (TN i) h J
      ((P.model q).1, cutN i + sign i * (0 + lambda / nu * (P.model q).2))).symm
  have hCapImage (i : Fin 3) : J '' capN i = capU i := by
    rw [image_image]
    exact image_congr (fun q _ => hCapPoint i q)
  have hJUnion : J '' (Rn ∪ ⋃ i : Fin 3, capN i) = R ∪ ⋃ i : Fin 3, capU i := by
    rw [image_union, hCore, image_iUnion]
    congr 1
    exact iUnion_congr hCapImage
  let FrefToTarget := (Gn.trans J).trans Fa
  have hFull : FrefToTarget '' Sn = Gt '' S := by
    change (Fa ∘ J ∘ Gn) '' Sn = _
    rw [image_comp, image_comp, hGn, hJUnion, hFa, hGt]
  refine ⟨(Gt.trans FrefToTarget.symm).trans Placement, ?_⟩
  have hBack : FrefToTarget.symm '' (Gt '' S) = Sn := by
    rw [← hFull]
    exact FrefToTarget.symm_image_image Sn
  simp only [Diffeomorph.coe_trans, image_comp]
  rw [hBack, hPlacementSurface]
  change range (fun q : UnitTwoSphere => A (F0 q)) = A '' (F0 '' sphere (0 : E3) 1)
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨F0 q, ⟨q, q.property, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨q, hq, rfl⟩, rfl⟩
    exact ⟨⟨q, hq⟩, rfl⟩

end PoincareConjecture.M25.Topology3D
