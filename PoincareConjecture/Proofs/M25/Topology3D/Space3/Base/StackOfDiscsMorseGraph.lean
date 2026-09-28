import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsMorseProjectionRegular
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactSmoothChart
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_stackMorseCap_graph
    (rFlat rOne v0 v1 rho lambda : ℝ)
    (hrFlat : 0 < rFlat) (hradii : rFlat < rOne) (hrOne : rOne < 1)
    (hv0 : 0 < v0) (hv01 : v0 < v1) (hv1 : v1 < 1)
    (hgap : v1 ^ 2 + rOne ^ 2 < 1)
    (hrho : 0 < rho) (hlambda : 0 < lambda) (hsmall : lambda < rho ^ 2 / 2) :
    let a := stackCanonicalHorizontal v0 v1
    let b := stackCanonicalVertical rFlat rOne
    let M := stackCapProfilePath a a b b 0
    let q : E2 → UnitTwoSphere := fun x => -northSpherePoint (-x)
    let C : E2 → E2 × ℝ := fun x => M (heightCoordinates (q x : E3))
    let h : E2 → ℝ := fun x => rho ^ 2 + lambda * (C x).2
    let f : E2 → E2 := fun x => Real.sqrt (h x) • (C x).1
    let U : Set E2 := {x | 0 < h x}
    let N : UnitTwoSphere → E2 × ℝ := fun p =>
      let m := M (heightCoordinates (p : E3))
      let t := rho ^ 2 + lambda * m.2
      (Real.sqrt t • m.1, t)
    let Qminus : Set UnitTwoSphere :=
      {p | (heightCoordinates (p : E3)).2 ≤ 0}
    ∃ e : OpenPartialHomeomorph E2 E2,
      (e : E2 → E2) = f ∧ closedBall (0 : E2) 1 ⊆ e.source ∧
      e.source ⊆ U ∧ ContDiffOn ℝ ∞ e e.source ∧
      ContDiffOn ℝ ∞ e.symm e.target ∧
      closedBall (0 : E2) rho ⊆ e.target ∧
      e '' closedBall (0 : E2) 1 = closedBall (0 : E2) rho ∧
      let g : E2 → ℝ := fun y => h (e.symm y)
      ContDiffOn ℝ ∞ g e.target ∧
        (∀ y ∈ e.target, 0 < g y) ∧
        (∀ x ∈ e.source, g (f x) = h x) ∧
        N '' Qminus = (fun y : E2 => (y, g y)) '' closedBall (0 : E2) rho ∧
        (∀ y ∈ closedBall (0 : E2) rho,
          rho ^ 2 - lambda ≤ g y ∧ g y ≤ rho ^ 2 ∧ ‖y‖ ^ 2 ≤ g y) ∧
        (∃ delta : ℝ, 0 < delta ∧ delta < rho ∧
          closedBall (0 : E2) delta ⊆ e.target ∧
          ∀ y ∈ closedBall (0 : E2) delta, g y = rho ^ 2 - lambda) ∧
        ∃ eps : ℝ, 0 < eps ∧ eps < rho ∧
          {y : E2 | |‖y‖ - rho| < eps} ⊆ e.target ∧
          ∀ y : E2, |‖y‖ - rho| < eps → g y = ‖y‖ ^ 2 := by
  let a := stackCanonicalHorizontal v0 v1
  let b := stackCanonicalVertical rFlat rOne
  let M := stackCapProfilePath a a b b 0
  let q : E2 → UnitTwoSphere := fun x => -northSpherePoint (-x)
  let C : E2 → E2 × ℝ := fun x => M (heightCoordinates (q x : E3))
  let h : E2 → ℝ := fun x => rho ^ 2 + lambda * (C x).2
  let f : E2 → E2 := fun x => Real.sqrt (h x) • (C x).1
  let U : Set E2 := {x | 0 < h x}
  let N : UnitTwoSphere → E2 × ℝ := fun p =>
    let m := M (heightCoordinates (p : E3))
    let t := rho ^ 2 + lambda * m.2
    (Real.sqrt t • m.1, t)
  let Qminus : Set UnitTwoSphere := {p | (heightCoordinates (p : E3)).2 ≤ 0}
  let v : E2 → ℝ := fun x => (‖x‖ ^ 2 - 1) / (1 + ‖x‖ ^ 2)
  obtain ⟨_, hCs, hU, hKU, hfs, _, hqi, hbounds, hinj, hfi, hzero, hseam⟩ :=
    stackMorseProjection_geometry rFlat rOne v0 v1 rho lambda
      hrFlat hradii hrOne hv0 hv01 hv1 hgap hrho hlambda hsmall
  change ContDiff ℝ ∞ C at hCs
  change IsOpen U at hU
  change closedBall (0 : E2) 1 ⊆ U at hKU
  change ContDiffOn ℝ ∞ f U at hfs
  change q '' closedBall (0 : E2) 1 = Qminus at hqi
  change InjOn f (closedBall (0 : E2) 1) at hinj
  change f '' closedBall (0 : E2) 1 = closedBall (0 : E2) rho at hfi
  change f 0 = 0 at hzero
  change ∀ x ∈ sphere (0 : E2) 1, f x = rho • x at hseam
  obtain ⟨⟨poleWidth, hpoleWidth, hpole⟩, hseamband, _, hderiv⟩ :=
    stackMorseProjection_regular rFlat rOne v0 v1 rho lambda
      hrFlat hradii hrOne hv0 hv01 hv1 hgap hrho hlambda hsmall
  obtain ⟨e, he, hKe, heU, hes, heis⟩ := exists_smoothChart_near_compact f
    (isCompact_closedBall (0 : E2) 1) hU hKU hfs hinj hderiv
  have hfe (x : E2) : e x = f x := congrFun he x
  have hei : e '' closedBall (0 : E2) 1 = closedBall (0 : E2) rho := by rw [he]; exact hfi
  have htarget : closedBall (0 : E2) rho ⊆ e.target := by
    intro y hy
    rw [← hei] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact e.map_source (hKe hx)
  let g : E2 → ℝ := fun y => h (e.symm y)
  have hhs : ContDiff ℝ ∞ h := contDiff_const.add (contDiff_const.mul hCs.snd)
  have hgs : ContDiffOn ℝ ∞ g e.target := hhs.comp_contDiffOn heis
  have hgpos (y : E2) (hy : y ∈ e.target) : 0 < g y := heU (e.map_target hy)
  have hgf (x : E2) (hx : x ∈ e.source) : g (f x) = h x := by
    change h (e.symm (f x)) = h x
    rw [← hfe, e.left_inv hx]
  have hgraph : N '' Qminus =
      (fun y : E2 => (y, g y)) '' closedBall (0 : E2) rho := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [← hqi] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      refine ⟨f x, ?_, ?_⟩
      · rw [← hfi]
        exact ⟨x, hx, rfl⟩
      · change (f x, g (f x)) = (f x, h x)
        rw [hgf x (hKe hx)]
    · rintro ⟨y, hy, rfl⟩
      rw [← hfi] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨q x, ?_, ?_⟩
      · rw [← hqi]
        exact ⟨x, hx, rfl⟩
      · change (f x, h x) = (f x, g (f x))
        rw [hgf x (hKe hx)]
  have hgbounds (y : E2) (hy : y ∈ closedBall (0 : E2) rho) :
      rho ^ 2 - lambda ≤ g y ∧ g y ≤ rho ^ 2 ∧ ‖y‖ ^ 2 ≤ g y := by
    rw [← hfi] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hgf x (hKe hx)]
    exact (hbounds x hx).2
  have hflat : ∃ delta : ℝ, 0 < delta ∧ delta < rho ∧
      closedBall (0 : E2) delta ⊆ e.target ∧
      ∀ y ∈ closedBall (0 : E2) delta, g y = rho ^ 2 - lambda := by
    let V := e.source ∩ ball (0 : E2) poleWidth
    have hV : IsOpen V := e.open_source.inter isOpen_ball
    have h0V : (0 : E2) ∈ V :=
      ⟨hKe (mem_closedBall_zero_iff.mpr (by norm_num)), mem_ball_self hpoleWidth⟩
    have hVi : IsOpen (e '' V) := e.isOpen_image_of_subset_source hV inter_subset_left
    have h0i : (0 : E2) ∈ e '' V := ⟨0, h0V, (hfe 0).trans hzero⟩
    obtain ⟨eta, heta, hball⟩ := Metric.isOpen_iff.mp hVi 0 h0i
    obtain ⟨delta, hdelta, hd⟩ := exists_between (lt_min heta hrho)
    have hsub : closedBall (0 : E2) delta ⊆ e '' V := by
      intro y hy
      apply hball
      exact mem_ball_zero_iff.mpr
        ((mem_closedBall_zero_iff.mp hy).trans_lt (hd.trans_le (min_le_left _ _)))
    refine ⟨delta, hdelta, hd.trans_le (min_le_right _ _), ?_, ?_⟩
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hsub hy
      exact e.map_source hx.1
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := hsub hy
      rw [hfe, hgf x hx.1]
      exact (hpole x hx.2).1
  have hvc : Continuous v :=
    ((continuous_norm.pow 2).sub continuous_const).div
      (continuous_const.add (continuous_norm.pow 2)) (fun x => by positivity)
  let Omega := e.source ∩ {x : E2 | |v x| < v0}
  let Gamma := e '' Omega
  have hOmega : IsOpen Omega := e.open_source.inter (isOpen_lt hvc.abs continuous_const)
  have hGamma : IsOpen Gamma := e.isOpen_image_of_subset_source hOmega inter_subset_left
  have hGammaT : Gamma ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.map_source hx.1
  have hGammaG (y : E2) (hy : y ∈ Gamma) : g y = ‖y‖ ^ 2 := by
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hfe, hgf x hx.1]
    exact (hseamband x hx.2).2.symm
  have hSGamma : sphere (0 : E2) rho ⊆ Gamma := by
    intro y hy
    have hyn : ‖y‖ = rho := mem_sphere_zero_iff_norm.mp hy
    let x : E2 := rho⁻¹ • y
    have hxn : ‖x‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hrho), hyn,
        inv_mul_cancel₀ hrho.ne']
    have hxs : x ∈ sphere (0 : E2) 1 := mem_sphere_zero_iff_norm.mpr hxn
    refine ⟨x, ⟨hKe (sphere_subset_closedBall hxs), ?_⟩, ?_⟩
    · change |v x| < v0
      simpa only [v, hxn, one_pow, sub_self, zero_div, abs_zero] using hv0
    · rw [hfe, hseam x hxs]
      change rho • (rho⁻¹ • y) = y
      rw [smul_smul, mul_inv_cancel₀ hrho.ne', one_smul]
  obtain ⟨eta, heta, hthick⟩ :=
    (isCompact_sphere (0 : E2) rho).exists_thickening_subset_open hGamma hSGamma
  let eps := min (eta / 2) (rho / 2)
  have heps : 0 < eps := lt_min (half_pos heta) (half_pos hrho)
  have hepsrho : eps < rho := (min_le_right _ _).trans_lt (half_lt_self hrho)
  have hepseta : eps < eta := (min_le_left _ _).trans_lt (half_lt_self heta)
  have hband (y : E2) (hy : |‖y‖ - rho| < eps) : y ∈ Gamma := by
    have hny : 0 < ‖y‖ := by
      have hh := (abs_lt.mp hy).1
      linarith only [hh, hepsrho]
    let z : E2 := (rho / ‖y‖) • y
    have hzs : z ∈ sphere (0 : E2) rho := by
      apply mem_sphere_zero_iff_norm.mpr
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hrho hny),
        div_mul_cancel₀ rho hny.ne']
    have hdist : dist y z = |‖y‖ - rho| := by
      rw [dist_eq_norm]
      have hz : y - z = (1 - rho / ‖y‖) • y := by
        dsimp only [z]
        rw [sub_smul, one_smul]
      rw [hz, norm_smul, Real.norm_eq_abs]
      calc
        |1 - rho / ‖y‖| * ‖y‖ = |(1 - rho / ‖y‖) * ‖y‖| := by
          rw [abs_mul, abs_of_pos hny]
        _ = |‖y‖ - rho| := by
          congr 1
          field_simp [hny.ne']
    apply hthick
    apply Metric.mem_thickening_iff.mpr
    exact ⟨z, hzs, hdist ▸ hy.trans hepseta⟩
  refine ⟨e, he, hKe, heU, hes, heis, htarget, hei, hgs, hgpos, hgf,
    hgraph, hgbounds, hflat, eps, heps, hepsrho, ?_, ?_⟩
  · intro y hy
    exact hGammaT (hband y hy)
  · intro y hy
    exact hGammaG y (hband y hy)

end PoincareConjecture.M25.Topology3D
