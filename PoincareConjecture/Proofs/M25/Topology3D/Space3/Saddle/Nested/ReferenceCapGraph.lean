import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceCapProjection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FieldLocalization

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem exists_outer_cap_graph
    (F : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (hF : ContDiff ℝ ∞ (fun z : E2 × ℝ => F z.2 z.1))
    (hfix : ∀ (a : ℝ) (x : E2), ‖x‖ ≤ 1 / 8 → F a x = x)
    (hray : ∀ e : E2, ‖e‖ = 1 → ∃ p : ℝ × ℝ → ℝ,
      ContDiff ℝ ∞ p ∧ (∀ a : ℝ, p (a, 0) = 0) ∧
      (∀ a r : ℝ, 0 < r → F a (r • e) = p (a, r) • e) ∧
      (∀ a r : ℝ, 0 < deriv (fun s : ℝ => p (a, s)) r) ∧
      (∀ a ∈ Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384),
        ∀ r : ℝ, 0 < r → deriv (fun s : ℝ => p (s, r)) a ≤ 0) ∧
      ∀ a ∈ Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384),
        deriv (fun s : ℝ => p (s, 1)) a < 0)
    (hroot : ∀ a ∈ Ioo (17 / 16 - 1 / 16384 : ℝ) (17 / 16 + 1 / 16384),
      ∀ x : E2, ‖x‖ = 1 →
        ‖F a x‖ < Real.sqrt 4095 / 64 ∧
        ‖F a x‖ ^ 2 + Real.sqrt (1 - ‖F a x‖ ^ 2) + (F a x) 0 / 32 = a)
    (h lambda : ℝ) (hh : |h - 17 / 16| ≤ 1 / 32768)
    (hlambda : 0 < lambda) (hsmall : lambda < 1 / 131072) :
    let a := stackCanonicalHorizontal (1 / 4) (1 / 2)
    let b := stackCanonicalVertical (1 / 4) (1 / 2)
    let M := stackCapProfilePath a a b b 0
    let q : E2 → UnitTwoSphere := fun x => -northSpherePoint (-x)
    let C : E2 → E2 × ℝ := fun x => M (heightCoordinates (q x : E3))
    let H : E2 → ℝ := fun x => h - lambda * (C x).2
    let f : E2 → E2 := fun x => F (H x) (C x).1
    let U : E2 → ℝ := fun y =>
      ‖y‖ ^ 2 + Real.sqrt (1 - ‖y‖ ^ 2) + y 0 / 32
    let N : UnitTwoSphere → E2 × ℝ := fun p =>
      let m := M (heightCoordinates (p : E3))
      (F (h + lambda * m.2) m.1, h + lambda * m.2)
    let Qplus : Set UnitTwoSphere :=
      {p | 0 ≤ (heightCoordinates (p : E3)).2}
    let B : Set E2 := F h '' closedBall (0 : E2) 1
    ∃ e : OpenPartialHomeomorph E2 E2,
      (e : E2 → E2) = f ∧ closedBall (0 : E2) 1 ⊆ e.source ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      B ⊆ e.target ∧ B ⊆ ball (0 : E2) (Real.sqrt 4095 / 64) ∧
      let g : E2 → ℝ := fun y => H (e.symm y)
      ContDiffOn ℝ ∞ g e.target ∧
        (∀ x ∈ e.source, g (f x) = H x) ∧
        N '' Qplus = (fun y : E2 => (y, g y)) '' B ∧
        (∀ y ∈ B, h ≤ g y ∧ g y ≤ h + lambda) ∧
        (∀ y ∈ F h '' ball (0 : E2) 1, h < g y) ∧
        (∃ Gamma : Set E2, IsOpen Gamma ∧ F h '' sphere (0 : E2) 1 ⊆ Gamma ∧
          Gamma ⊆ e.target ∧ ∀ y ∈ Gamma, g y = U y) ∧
        ∃ D : E2 → ℝ, ContDiff ℝ ∞ D ∧ HasCompactSupport D ∧
          tsupport D ⊆ F h '' ball (0 : E2) 1 ∧ ∀ y ∈ B, D y = g y - U y := by
  classical
  let a := stackCanonicalHorizontal (1 / 4) (1 / 2)
  let b := stackCanonicalVertical (1 / 4) (1 / 2)
  let M := stackCapProfilePath a a b b 0
  let q : E2 → UnitTwoSphere := fun x => -northSpherePoint (-x)
  let C : E2 → E2 × ℝ := fun x => M (heightCoordinates (q x : E3))
  let H : E2 → ℝ := fun x => h - lambda * (C x).2
  let f : E2 → E2 := fun x => F (H x) (C x).1
  let U : E2 → ℝ := fun y =>
    ‖y‖ ^ 2 + Real.sqrt (1 - ‖y‖ ^ 2) + y 0 / 32
  let N : UnitTwoSphere → E2 × ℝ := fun p =>
    let m := M (heightCoordinates (p : E3))
    (F (h + lambda * m.2) m.1, h + lambda * m.2)
  let Qplus : Set UnitTwoSphere := {p | 0 ≤ (heightCoordinates (p : E3)).2}
  let B : Set E2 := F h '' closedBall (0 : E2) 1
  let v : E2 → ℝ := fun x => (‖x‖ ^ 2 - 1) / (1 + ‖x‖ ^ 2)
  let J : Set ℝ := Ioo (17 / 16 - 1 / 16384) (17 / 16 + 1 / 16384)
  have hhJ : h ∈ J := by
    obtain ⟨hlo, hhi⟩ := abs_le.mp hh
    constructor <;> linarith only [hlo, hhi]
  obtain ⟨_, _, hseam, hboundary, himage, e, he, hKe, hes, heis⟩ :=
    exists_outer_cap_projection_chart F hF hfix hray h lambda hh hlambda hsmall
  change (e : E2 → E2) = f at he
  change f '' closedBall (0 : E2) 1 = B at himage
  change ∀ x ∈ sphere (0 : E2) 1, f x = F h x at hboundary
  change ∀ x : E2, |v x| < 1 / 4 → (C x).2 = v x ∧ ‖(C x).1‖ = 1 at hseam
  have hfe (x : E2) : e x = f x := congrFun he x
  have htarget : B ⊆ e.target := by
    intro y hy
    rw [← himage] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [← hfe]
    exact e.map_source (hKe hx)
  obtain ⟨_, hCs, _, _, _, hcoords, _, hcanonical, _, _, _, _⟩ :=
    stackMorseProjection_geometry (1 / 4) (1 / 2) (1 / 4) (1 / 2) 1 (1 / 4)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change ContDiff ℝ ∞ C at hCs
  have hHs : ContDiff ℝ ∞ H := contDiff_const.sub (contDiff_const.mul hCs.snd)
  let g : E2 → ℝ := fun y => H (e.symm y)
  have hgs : ContDiffOn ℝ ∞ g e.target := hHs.comp_contDiffOn heis
  have hgf (x : E2) (hx : x ∈ e.source) : g (f x) = H x := by
    change H (e.symm (f x)) = H x
    rw [← hfe, e.left_inv hx]
  obtain ⟨hreflection, _⟩ := stackCanonicalModel_reflection_height
    (1 / 4) (1 / 2) (1 / 4) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  change ∀ p : E2 × ℝ, M (p.1, -p.2) = ((M p).1, -(M p).2) at hreflection
  have hpoint (x : E2) : heightCoordinates (northSpherePoint x : E3) =
      ((heightCoordinates (q x : E3)).1, -(heightCoordinates (q x : E3)).2) := by
    rw [northSpherePoint_coordinates, (hcoords x).2.2.1]
    apply Prod.ext
    · rfl
    · change (1 - ‖x‖ ^ 2) / (1 + ‖x‖ ^ 2) = -v x
      dsimp only [v]
      ring
  have hN (x : E2) : N (northSpherePoint x) = (f x, H x) := by
    dsimp only [N]
    rw [hpoint, hreflection]
    change (F (h + lambda * -(C x).2) (C x).1,
      h + lambda * -(C x).2) = (f x, H x)
    have ht : h + lambda * -(C x).2 = H x := by dsimp only [H]; ring
    rw [ht]
  have hgraph : N '' Qplus = (fun y : E2 => (y, g y)) '' B := by
    have hqi : northSpherePoint '' closedBall (0 : E2) 1 = Qplus :=
      northSpherePoint_image_closedBall
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hqi] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      refine ⟨f x, himage ▸ (show f x ∈ f '' closedBall (0 : E2) 1 from
        ⟨x, hx, rfl⟩), ?_⟩
      change (f x, g (f x)) = N (northSpherePoint x)
      rw [hN, hgf x (hKe hx)]
    · rintro ⟨y, hy, rfl⟩
      rw [← himage] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨northSpherePoint x, hqi ▸ (show northSpherePoint x ∈
        northSpherePoint '' closedBall (0 : E2) 1 from ⟨x, hx, rfl⟩), ?_⟩
      change N (northSpherePoint x) = (f x, g (f x))
      rw [hN, hgf x (hKe hx)]
  have hCbound (x : E2) (hx : x ∈ closedBall (0 : E2) 1) :
      -1 ≤ (C x).2 ∧ (C x).2 ≤ 0 := by
    have hlo := (hcanonical x hx).2.1
    have hhi := (hcanonical x hx).2.2.1
    change (1 : ℝ) ^ 2 - 1 / 4 ≤ 1 ^ 2 + (1 / 4) * (C x).2 at hlo
    change (1 : ℝ) ^ 2 + (1 / 4) * (C x).2 ≤ 1 ^ 2 at hhi
    constructor <;> linarith only [hlo, hhi]
  have hgbound (y : E2) (hy : y ∈ B) : h ≤ g y ∧ g y ≤ h + lambda := by
    rw [← himage] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hgf x (hKe hx)]
    obtain ⟨hlo, hhi⟩ := hCbound x hx
    change h ≤ h - lambda * (C x).2 ∧ h - lambda * (C x).2 ≤ h + lambda
    constructor <;> nlinarith only [hlo, hhi, hlambda]
  have hM (p : E2 × ℝ) : M p = (a p.2 • p.1, b (a p.2 • p.1) * p.2) := by
    simp only [M, stackCapProfilePath, stackProfileBlend_of_nonpos _ _ 0 le_rfl]
  have hCform (x : E2) : C x =
      (a (v x) • ((2 / (1 + ‖x‖ ^ 2)) • x),
        b (a (v x) • ((2 / (1 + ‖x‖ ^ 2)) • x)) * v x) := by
    dsimp only [C]
    rw [(hcoords x).2.2.1, hM]
  obtain ⟨_, hbpos, _, _, _, _⟩ := stackCanonicalVertical_spec (1 / 4) (1 / 2)
    (by norm_num) (by norm_num) (by norm_num)
  have hgstrict (y : E2) (hy : y ∈ F h '' ball (0 : E2) 1) : h < g y := by
    have hyB : y ∈ B := image_mono ball_subset_closedBall hy
    rw [← himage] at hyB
    obtain ⟨x, hx, hxy⟩ := hyB
    have hxlt : ‖x‖ < 1 := by
      have hxle := mem_closedBall_zero_iff.mp hx
      by_contra hn
      have hxn : ‖x‖ = 1 := le_antisymm hxle (le_of_not_gt hn)
      obtain ⟨z, hz, hzxy⟩ := hy
      have hxeq : F h x = F h z :=
        (hboundary x (mem_sphere_zero_iff_norm.mpr hxn)).symm.trans (hxy.trans hzxy.symm)
      have hzx : x = z := (F h).injective hxeq
      have hzlt := mem_ball_zero_iff.mp hz
      rw [← hzx, hxn] at hzlt
      exact lt_irrefl _ hzlt
    have hvneg : v x < 0 := by
      apply div_neg_of_neg_of_pos _ (by positivity : 0 < 1 + ‖x‖ ^ 2)
      nlinarith only [hxlt, norm_nonneg x]
    have hCneg : (C x).2 < 0 := by
      rw [hCform]
      exact mul_neg_of_pos_of_neg (hbpos _) hvneg
    rw [← hxy, hgf x (hKe hx)]
    change h < h - lambda * (C x).2
    nlinarith only [mul_neg_of_pos_of_neg hlambda hCneg]
  have hrpos : (0 : ℝ) < Real.sqrt 4095 / 64 := by positivity
  have hrlt : Real.sqrt (4095 : ℝ) / 64 < 1 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 4095)
    have hn := Real.sqrt_nonneg (4095 : ℝ)
    nlinarith only [hs, hn]
  have hBrad : B ⊆ ball (0 : E2) (Real.sqrt 4095 / 64) := by
    rintro y ⟨x, hx, rfl⟩
    apply mem_ball_zero_iff.mpr
    by_cases hx0 : x = 0
    · subst x
      rw [hfix h 0 (by norm_num), norm_zero]
      exact hrpos
    let w : E2 := ‖x‖⁻¹ • x
    have hxn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    have hw : ‖w‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hxn),
        inv_mul_cancel₀ hxn.ne']
    have hxw : ‖x‖ • w = x := by
      dsimp only [w]
      rw [smul_smul, mul_inv_cancel₀ hxn.ne', one_smul]
    obtain ⟨p, _, hpzero, hpray, hpr, _, _⟩ := hray w hw
    have hpmono := strictMono_of_deriv_pos (hpr h)
    have hppos : 0 < p (h, ‖x‖) := by simpa only [hpzero] using hpmono hxn
    have hpone : 0 < p (h, 1) := by
      simpa only [hpzero] using hpmono (by norm_num : (0 : ℝ) < 1)
    have hFxn : ‖F h x‖ = p (h, ‖x‖) := by
      have heq := hpray h ‖x‖ hxn
      rw [hxw] at heq
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hppos, hw, mul_one]
    have hFwn : ‖F h w‖ = p (h, 1) := by
      have heq := hpray h 1 (by norm_num)
      rw [one_smul] at heq
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hpone, hw, mul_one]
    rw [hFxn]
    exact (hpmono.monotone (mem_closedBall_zero_iff.mp hx)).trans_lt
      (hFwn ▸ (hroot h hhJ w hw).1)
  have hvc : Continuous v :=
    ((continuous_norm.pow 2).sub continuous_const).div
      (continuous_const.add (continuous_norm.pow 2)) (fun x => by positivity)
  let Omega := (e.source ∩ {x : E2 | |v x| < 1 / 4}) ∩ H ⁻¹' J
  let Gamma := e '' Omega
  have hOmega : IsOpen Omega :=
    (e.open_source.inter (isOpen_lt hvc.abs continuous_const)).inter
      (isOpen_Ioo.preimage hHs.continuous)
  have hOmegaE : Omega ⊆ e.source := fun _ hx => hx.1.1
  have hGamma : IsOpen Gamma := e.isOpen_image_of_subset_source hOmega hOmegaE
  have hGammaT : Gamma ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source hx.1.1
  have hGammaG (y : E2) (hy : y ∈ Gamma) : g y = U y := by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hfe, hgf x hx.1.1]
    exact ((hroot (H x) hx.2 (C x).1 (hseam x hx.1.2).2).2).symm
  have hSGamma : F h '' sphere (0 : E2) 1 ⊆ Gamma := by
    rintro y ⟨x, hx, rfl⟩
    have hvzero : v x = 0 := by
      simp only [v, mem_sphere_zero_iff_norm.mp hx, one_pow, sub_self, zero_div]
    have hxseam : |v x| < 1 / 4 := by rw [hvzero]; norm_num
    have hHzero : H x = h := by
      change h - lambda * (C x).2 = h
      rw [(hseam x hxseam).1, hvzero, mul_zero, sub_zero]
    refine ⟨x, ⟨⟨hKe (sphere_subset_closedBall hx), hxseam⟩, ?_⟩,
      (hfe x).trans (hboundary x hx)⟩
    change H x ∈ J
    rw [hHzero]
    exact hhJ
  have hUs : ContDiffOn ℝ ∞ U (ball (0 : E2) 1) := by
    have hs : ContDiffOn ℝ ∞ (fun y : E2 => Real.sqrt (1 - ‖y‖ ^ 2))
        (ball (0 : E2) 1) :=
      (contDiff_const.sub (contDiff_norm_sq ℝ)).contDiffOn.sqrt (by
        intro y hy
        have hn := mem_ball_zero_iff.mp hy
        have hp : 0 < 1 - ‖y‖ ^ 2 := by nlinarith only [hn, norm_nonneg y]
        exact hp.ne')
    exact ((contDiff_norm_sq ℝ).contDiffOn.add hs).add
      ((EuclideanSpace.proj 0 : E2 →L[ℝ] ℝ).contDiff.div_const (32 : ℝ)).contDiffOn
  let K := B \ Gamma
  let V := (e.target ∩ ball (0 : E2) 1) ∩ (F h '' ball (0 : E2) 1)
  have hB : IsCompact B := (isCompact_closedBall (0 : E2) 1).image
    (F h).toHomeomorph.continuous
  have hK : IsCompact K := hB.diff hGamma
  have hV : IsOpen V := (e.open_target.inter isOpen_ball).inter
    ((F h).toHomeomorph.isOpenMap _ isOpen_ball)
  have hKV : K ⊆ V := by
    intro y hy
    refine ⟨⟨htarget hy.1, mem_ball_zero_iff.mpr
      ((mem_ball_zero_iff.mp (hBrad hy.1)).trans hrlt)⟩, ?_⟩
    obtain ⟨x, hx, hxy⟩ := hy.1
    refine ⟨x, mem_ball_zero_iff.mpr ?_, hxy⟩
    have hxle := mem_closedBall_zero_iff.mp hx
    by_contra hn
    have hxn : ‖x‖ = 1 := le_antisymm hxle (le_of_not_gt hn)
    exact hy.2 (hSGamma ⟨x, mem_sphere_zero_iff_norm.mpr hxn, hxy⟩)
  obtain ⟨chi, hchi, hchic, hchis, hchinear, _⟩ := exists_compact_smooth_cutoff hK hV hKV
  let D : E2 → ℝ := fun y => chi y • (g y - U y)
  have hDs : ContDiff ℝ ∞ D := contDiff_cutoff_smul hV chi hchi hchis
    (fun y => g y - U y) ((hgs.mono (fun _ hx => hx.1.1)).sub
      (hUs.mono (fun _ hx => hx.1.2)))
  refine ⟨e, he, hKe, hes, heis, htarget, hBrad, hgs, hgf, hgraph, hgbound,
    hgstrict, ⟨Gamma, hGamma, hSGamma, hGammaT, hGammaG⟩, D, hDs,
    hchic.smul_right, (tsupport_smul_subset_left chi (fun y => g y - U y)).trans
      (hchis.trans (fun _ hx => hx.2)), ?_⟩
  intro y hy
  by_cases hyG : y ∈ Gamma
  · change chi y • (g y - U y) = g y - U y
    rw [hGammaG y hyG, sub_self, smul_zero]
  · have hchiOne : chi y = 1 := subset_of_mem_nhdsSet hchinear ⟨hy, hyG⟩
    change chi y • (g y - U y) = g y - U y
    rw [hchiOne, one_smul]

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
