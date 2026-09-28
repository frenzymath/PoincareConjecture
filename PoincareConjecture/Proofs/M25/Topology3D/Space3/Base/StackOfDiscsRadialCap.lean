import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsCapTransfer

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem stackCanonicalCap_image_eq_of_radial_annulus
    (D : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2))
    (hD : ContDiffOn ℝ ∞ D D.source)
    (hDi : ContDiffOn ℝ ∞ D.symm D.target)
    (hDh : ∀ p ∈ D.source, (D p).1 = p.1)
    (s sigma lambda gamma delta : ℝ)
    (hsigma : |sigma| = 1) (hlambda : 0 < lambda) (hlg : lambda < gamma)
    (hdelta : 0 < delta)
    (hDs : Icc (s - gamma) (s + gamma) ×ˢ closedBall (0 : E2) 1 ⊆ D.source)
    (hDt : Icc (s - gamma) (s + gamma) ×ˢ closedBall (0 : E2) 1 ⊆ D.target)
    (hnorm : ∀ z ∈ Icc (s - gamma) (s + gamma), ∀ x : E2,
      |‖x‖ - 1| < delta →
        ‖(D (z, x)).2‖ = ‖x‖ ∧ ‖(D.symm (z, x)).2‖ = ‖x‖)
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
    Y ⊆ D.source ∧ Y ⊆ D.target ∧ D '' Y = Y ∧ D.symm '' Y = Y := by
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let coord := fun q : UnitTwoSphere => heightCoordinates (q : E3)
  let Qminus := {q : UnitTwoSphere | (coord q).2 ≤ 0}
  let f := fun q : UnitTwoSphere => (s + sigma * lambda * (M (coord q)).2, (M (coord q)).1)
  let Y := f '' Qminus
  let zflat := s - sigma * lambda
  let Flat : Set (ℝ × E2) := {zflat} ×ˢ closedBall (0 : E2) rFlat
  have hr1 : rFlat < 1 := hradii.trans hrOne
  have hgeom (q : UnitTwoSphere) (hq : q ∈ Qminus) :=
    stackCanonicalModel_southern_geometry rFlat rOne v0 v1
      hrFlat hradii hrOne hv0 hv01 hv1 hgap (coord q) (sphere_height_coordinates_sq q) hq
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
  have hYs : Y ⊆ D.source := by
    rintro _ ⟨q, hq, rfl⟩
    exact hDs (hpoint q hq)
  have hYt : Y ⊆ D.target := by
    rintro _ ⟨q, hq, rfl⟩
    exact hDt (hpoint q hq)
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
  have hDih (p : ℝ × E2) (hp : p ∈ D.target) : (D.symm p).1 = p.1 := by
    have hh := hDh (D.symm p) (D.map_target hp)
    rw [D.right_inv hp] at hh
    exact hh.symm
  have hf : ContDiffOn ℝ ∞ (fun x : E2 => (D (zflat, x)).2)
      {x | (zflat, x) ∈ D.source} :=
    (hD.comp (contDiff_prodMk_right zflat).contDiffOn (fun _ hx => hx)).snd
  have hi : ContDiffOn ℝ ∞ (fun y : E2 => (D.symm (zflat, y)).2)
      {y | (zflat, y) ∈ D.target} :=
    (hDi.comp (contDiff_prodMk_right zflat).contDiffOn (fun _ hy => hy)).snd
  have hforward (x : E2) (hx : (zflat, x) ∈ D.source) :
      (zflat, (D (zflat, x)).2) = D (zflat, x) := Prod.ext (hDh _ hx).symm rfl
  have hinverse (y : E2) (hy : (zflat, y) ∈ D.target) :
      (zflat, (D.symm (zflat, y)).2) = D.symm (zflat, y) := Prod.ext (hDih _ hy).symm rfl
  let V : OpenPartialHomeomorph E2 E2 := {
    toFun := fun x => (D (zflat, x)).2
    invFun := fun y => (D.symm (zflat, y)).2
    source := {x | (zflat, x) ∈ D.source}
    target := {y | (zflat, y) ∈ D.target}
    map_source' := by
      intro x hx
      change (zflat, (D (zflat, x)).2) ∈ D.target
      rw [hforward x hx]
      exact D.map_source hx
    map_target' := by
      intro y hy
      change (zflat, (D.symm (zflat, y)).2) ∈ D.source
      rw [hinverse y hy]
      exact D.map_target hy
    left_inv' := by
      intro x hx
      rw [hforward x hx, D.left_inv hx]
    right_inv' := by
      intro y hy
      rw [hinverse y hy, D.right_inv hy]
    open_source := D.open_source.preimage (continuous_const.prodMk continuous_id)
    open_target := D.open_target.preimage (continuous_const.prodMk continuous_id)
    continuousOn_toFun := hf.continuousOn
    continuousOn_invFun := hi.continuousOn }
  let R : E2 ≃L[ℝ] E2 :=
    (LinearEquiv.smulOfNeZero ℝ E2 rFlat hrFlat.ne').toContinuousLinearEquiv
  let n := R.toHomeomorph.transOpenPartialHomeomorph V
  have hns : closedBall (0 : E2) 1 ⊆ n.source := by
    intro x hx
    apply hDs
    refine ⟨hflatheight, mem_closedBall_zero_iff.mpr ?_⟩
    change ‖rFlat • x‖ ≤ 1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrFlat]
    have hx' := mem_closedBall_zero_iff.mp hx
    nlinarith only [hx', hrFlat, hr1]
  let N : BallNeighborhoodChart E2 E2 := ⟨n, hns,
    hf.comp R.contDiff.contDiffOn (fun _ hx => hx),
    R.symm.contDiff.comp_contDiffOn hi⟩
  have hNf (x : E2) : N.chart x = (D (zflat, R x)).2 := rfl
  have hRnorm (x : E2) : ‖R x‖ = rFlat * ‖x‖ := by
    change ‖rFlat • x‖ = _
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrFlat]
  have hflatann : |rFlat - 1| < delta := by
    rw [abs_of_neg (sub_neg.mpr hr1)]
    linarith only [hrann]
  have hboundary : N.boundary = sphere (0 : E2) rFlat := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      apply mem_sphere_zero_iff_norm.mpr
      have hxnorm : ‖R x‖ = rFlat := by
        rw [hRnorm, mem_sphere_zero_iff_norm.mp hx, mul_one]
      rw [hNf, (hnorm zflat hflatheight (R x) (hxnorm ▸ hflatann)).1, hxnorm]
    · intro y hy
      have hyNorm : ‖y‖ = rFlat := mem_sphere_zero_iff_norm.mp hy
      have hyD : (zflat, y) ∈ D.target :=
        hDt ⟨hflatheight, mem_closedBall_zero_iff.mpr (hyNorm.trans_le hr1.le)⟩
      let x := (D.symm (zflat, y)).2
      have hxNorm : ‖x‖ = rFlat :=
        ((hnorm zflat hflatheight y (hyNorm ▸ hflatann)).2).trans hyNorm
      have hxUnit : R.symm x ∈ sphere (0 : E2) 1 := by
        apply mem_sphere_zero_iff_norm.mpr
        apply (mul_left_cancel₀ hrFlat.ne')
        calc
          rFlat * ‖R.symm x‖ = ‖R (R.symm x)‖ := (hRnorm _).symm
          _ = rFlat := by rw [R.apply_symm_apply, hxNorm]
          _ = rFlat * 1 := (mul_one rFlat).symm
      refine ⟨R.symm x, hxUnit, ?_⟩
      rw [hNf, R.apply_symm_apply]
      change (D (zflat, (D.symm (zflat, y)).2)).2 = y
      rw [hinverse y hyD, D.right_inv hyD]
  have hscaled : R '' closedBall (0 : E2) 1 = closedBall (0 : E2) rFlat :=
    scaledBallNeighborhoodChart_closedRegion rFlat hrFlat
  have hregion : N.closedRegion = closedBall (0 : E2) rFlat := by
    calc
      N.closedRegion = (scaledBallNeighborhoodChart rFlat hrFlat).closedRegion :=
        N.closedRegion_eq_of_boundary_eq (scaledBallNeighborhoodChart rFlat hrFlat)
          (Module.one_lt_rank_of_one_lt_finrank (by simp [E2]))
          (hboundary.trans (scaledBallNeighborhoodChart_boundary rFlat hrFlat).symm)
      _ = _ := scaledBallNeighborhoodChart_closedRegion rFlat hrFlat
  have hclosed : (fun x : E2 => (D (zflat, x)).2) '' closedBall (0 : E2) rFlat =
      closedBall (0 : E2) rFlat := by
    conv_lhs => rw [← hscaled, image_image]
    exact hregion
  have hflatD : D '' Flat = Flat := by
    apply Subset.antisymm
    · rintro _ ⟨⟨z, x⟩, ⟨hz, hx⟩, rfl⟩
      have hz' : z = zflat := hz
      subst z
      refine ⟨hDh _ (hDs ⟨hflatheight, closedBall_subset_closedBall hr1.le hx⟩), ?_⟩
      exact hclosed ▸ mem_image_of_mem (fun x : E2 => (D (zflat, x)).2) hx
    · rintro ⟨z, y⟩ ⟨hz, hy⟩
      have hz' : z = zflat := hz
      subst z
      obtain ⟨x, hx, hxy⟩ := hclosed.symm ▸ hy
      refine ⟨(zflat, x), ⟨rfl, hx⟩, Prod.ext ?_ hxy⟩
      exact hDh _ (hDs ⟨hflatheight, closedBall_subset_closedBall hr1.le hx⟩)
  have hflatDi : D.symm '' Flat = Flat := by
    calc
      D.symm '' Flat = D.symm '' (D '' Flat) := congrArg (image D.symm) hflatD.symm
      _ = (D.symm ∘ D) '' Flat := image_image D.symm D Flat
      _ = id '' Flat := image_congr (fun p hp => D.left_inv (hYs (hflatY hp)))
      _ = Flat := image_id Flat
  have hM (p : E2 × ℝ) : M p = (a p.2 • p.1, b (a p.2 • p.1) * p.2) := by
    simp only [M, stackCapProfilePath, stackProfileBlend_of_nonpos a a 0 le_rfl,
      stackProfileBlend_of_nonpos b b 0 le_rfl]
  have hapos : ∀ v, 0 < a v := (stackCanonicalHorizontal_spec v0 v1 hv0 hv01 hv1).2.1
  have hbradial : ∀ x y, ‖x‖ = ‖y‖ → b x = b y :=
    (stackCanonicalVertical_spec rFlat rOne hrFlat hradii hrOne).2.2.2.2.2
  have hsameRadius (q : UnitTwoSphere) (hq : q ∈ Qminus) (y : E2)
      (hy : ‖y‖ = ‖(M (coord q)).1‖) : ((f q).1, y) ∈ Y := by
    let v := (coord q).2
    let x := (a v)⁻¹ • y
    have hy' : ‖y‖ = a v * ‖(coord q).1‖ := by
      rw [hy, hM]
      change ‖a v • (coord q).1‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hapos v)]
    have hxnorm : ‖x‖ = ‖(coord q).1‖ := by
      change ‖(a v)⁻¹ • y‖ = _
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hapos v)),
        hy', ← mul_assoc, inv_mul_cancel₀ (hapos v).ne', one_mul]
    let q' : UnitTwoSphere := ⟨heightCoordinates.symm (x, v), by
      apply mem_sphere_zero_iff_norm.mpr
      have hn := heightCoordinates_symm_norm_sq (x, v)
      have hqnorm := sphere_height_coordinates_sq q
      rw [hxnorm] at hn
      change ‖heightCoordinates.symm (x, v)‖ ^ 2 = ‖(coord q).1‖ ^ 2 + (coord q).2 ^ 2 at hn
      nlinarith [norm_nonneg (heightCoordinates.symm (x, v))]⟩
    have hcoord : coord q' = (x, v) := heightCoordinates.apply_symm_apply _
    have hq' : q' ∈ Qminus := by
      change (coord q').2 ≤ 0
      rw [hcoord]
      exact hq
    have hhor : a v • x = y := by
      change a v • ((a v)⁻¹ • y) = y
      rw [smul_smul, mul_inv_cancel₀ (hapos v).ne', one_smul]
    have hb : b y = b (a v • (coord q).1) := by
      apply hbradial
      rw [hy, hM]
    have hmodel : M (coord q') = (y, (M (coord q)).2) := by
      rw [hcoord, hM]
      change (a v • x, b (a v • x) * v) = _
      rw [hhor, hb, hM]
    refine ⟨q', hq', ?_⟩
    change (s + sigma * lambda * (M (coord q')).2, (M (coord q')).1) = ((f q).1, y)
    rw [hmodel]
  have hmaps (V : (ℝ × E2) → ℝ × E2)
      (hVh : ∀ p ∈ Y, (V p).1 = p.1) (hVflat : V '' Flat = Flat)
      (hVn : ∀ z ∈ Icc (s - gamma) (s + gamma), ∀ x : E2,
        |‖x‖ - 1| < delta → ‖(V (z, x)).2‖ = ‖x‖) : MapsTo V Y Y := by
    rintro _ ⟨q, hq, rfl⟩
    by_cases hsmall : ‖(M (coord q)).1‖ ≤ rFlat
    · have he := (hgeom q hq).2.2.2.2.1 hsmall
      change M (coord q) = ((coord q).1, -1) at he
      have hpFlat : f q ∈ Flat := by
        refine ⟨?_, mem_closedBall_zero_iff.mpr hsmall⟩
        change s + sigma * lambda * (M (coord q)).2 = zflat
        rw [he]
        dsimp [zflat]
        ring
      exact hflatY (hVflat ▸ mem_image_of_mem V hpFlat)
    · have hr : rFlat < ‖(M (coord q)).1‖ := lt_of_not_ge hsmall
      have hann : |‖(M (coord q)).1‖ - 1| < delta := abs_lt.mpr
        ⟨by linarith only [hr, hrann],
          (sub_nonpos.mpr (hgeom q hq).2.1).trans_lt hdelta⟩
      have hn := hVn (f q).1 (hpoint q hq).1 (f q).2 hann
      have hp := hsameRadius q hq (V (f q)).2 hn
      have he : ((f q).1, (V (f q)).2) = V (f q) :=
        Prod.ext (hVh (f q) ⟨q, hq, rfl⟩).symm rfl
      exact he ▸ hp
  have hDY : MapsTo D Y Y := hmaps D (fun p hp => hDh p (hYs hp)) hflatD
    (fun z hz x hx => (hnorm z hz x hx).1)
  have hDiY : MapsTo D.symm Y Y := hmaps D.symm (fun p hp => hDih p (hYt hp)) hflatDi
    (fun z hz x hx => (hnorm z hz x hx).2)
  refine ⟨hYs, hYt, Subset.antisymm hDY.image_subset ?_,
    Subset.antisymm hDiY.image_subset ?_⟩
  · intro p hp
    exact ⟨D.symm p, hDiY hp, D.right_inv (hYt hp)⟩
  · intro p hp
    exact ⟨D p, hDY hp, D.left_inv (hYs hp)⟩

end PoincareConjecture.M25.Topology3D
