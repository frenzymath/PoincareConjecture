import PoincareConjecture.Proofs.M25.Topology3D.Space3.PlanarBoundaryDisc
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CircleRadialChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartDerivative
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereNormalSign
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SphereCollarCorrection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.FixedSphereBallPreservation
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RelativeCapCompression
import PoincareConjecture.Proofs.M25.Topology3D.Space3.ChartIsotopyTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PlanarFamilyHeightLift
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Connected.Basic
import Mathlib.Tactic










set_option autoImplicit false
open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace
namespace PoincareConjecture.M25.Topology3D


set_option linter.unusedVariables false in



theorem exists_relative_exterior_arc_isotopy
    (hP : PlanarSchoenfliesService)
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 1 ⊆ kappa.source)
    (hkappa : ContDiffOn ℝ ∞ kappa kappa.source)
    (hkappaInv : ContDiffOn ℝ ∞ kappa.symm kappa.target)
    (alpha : Fin 2 → ℝ → E2) (l r eta : ℝ)
    (F : Set E2) (v : E2)
    (c : Fin 2 → UnitCircle → E2) (q : ℝ → UnitCircle)
    (W : Fin 2 → Set E2) (Uc : Set UnitCircle) (w : ℝ)
    (N : OpenPartialHomeomorph (UnitCircle × ℝ) E2) :
    let K : Set E2 := kappa '' closedBall (0 : E2) 1
    let Kboundary : Set E2 := kappa '' sphere (0 : E2) 1
    let Uarc : Set ℝ := Ioo (-eta) (1 + eta)
    let Gpar : Set ℝ := Ioo (-eta) (l + eta) ∪ Ioo (r - eta) (1 + eta)
    let Tailpar : Set ℝ := Icc 0 l ∪ Icc r 1
    let Umid : Set ℝ := Ioo (l - eta) (r + eta)
    let Dc : Set UnitCircle := {p | (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
    let Jc : Set UnitCircle := {p | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
    let Ac : Set UnitCircle := {p | (2 / 3 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
    let Delta : Set E2 := c 0 '' Dc
    ∀ (hl : 0 < l) (hlr : l < r) (hr : r < 1)
      (heta : 0 < eta) (hetal : eta < l)
      (hetar : r + eta < 1) (hgap : l + eta < r - eta)
      (hF : IsClosed F) (hKF : K ⊆ F)
      (hAlpha : ∀ i, ContDiffOn ℝ ∞ (alpha i) Uarc)
      (hAlphaInj : ∀ i, Set.InjOn (alpha i) Uarc)
      (hAlphaReg : ∀ i, ∀ t ∈ Uarc, deriv (alpha i) t ≠ 0)
      (hEnds : ∀ i, alpha i 0 ∈ Kboundary ∧ alpha i 1 ∈ Kboundary)
      (hProper : ∀ i, alpha i '' Ioo (0 : ℝ) 1 ⊆ Kᶜ)
      (hGerms : Set.EqOn (alpha 0) (alpha 1) Gpar)
      (hTails : alpha 0 '' Tailpar ⊆ F)
      (hv : ‖v‖ = 1)
      (hc : ∀ i, IsPlanarEmbedding (c i))
      (hcCommon : Set.EqOn (c 0) (c 1) Jc)
      (hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ q Umid)
      (hqInj : Set.InjOn q Umid)
      (hqReg : ∀ t ∈ Umid,
        Function.Injective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) q t))
      (hqImage : q '' Icc l r =
        {p : UnitCircle | ⟪v, (p : E2)⟫_ℝ ≤ (3 / 4 : ℝ)})
      (hqEnds : ({q l, q r} : Set UnitCircle) =
        {p : UnitCircle | ⟪v, (p : E2)⟫_ℝ = (3 / 4 : ℝ)})
      (hTracks : ∀ i, ∀ t ∈ Umid, c i (q t) = alpha i t)
      (hcK : ∀ i, Disjoint (range (c i)) K)
      (hcF : ∀ i, range (c i) ∩ F ⊆ Delta)
      (hWopen : ∀ i, IsOpen (W i))
      (hWconn : ∀ i, IsConnected (W i))
      (hWunbounded : ∀ i, ¬ Bornology.IsBounded (W i))
      (hWcurve : ∀ i, Disjoint (W i) (range (c i)))
      (hFW : ∀ i, F \ Delta ⊆ W i)
      (hUc : IsOpen Uc) (hAc : Ac ⊆ Uc) (hUcJ : Uc ⊆ Jc)
      (hw : 0 < w)
      (hNsource : Uc ×ˢ Icc (-w) w ⊆ N.source)
      (hN : ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E2) ∞ N N.source)
      (hNinv : ContMDiffOn 𝓘(ℝ, E2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞
        N.symm N.target)
      (hNzero : ∀ p ∈ Uc, N (p, 0) = c 0 p)
      (hNpositive : ∀ i, N '' (Uc ×ˢ Ioo (0 : ℝ) w) ⊆ W i),
      ∃ (C : Set E2)
        (J : ℝ → Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
        (rho : ℝ),
        IsCompact C ∧ C ⊆ Fᶜ \ Delta ∧
        ContDiff ℝ ∞ (fun p : ℝ × E2 => J p.1 p.2) ∧
        ContDiff ℝ ∞ (fun p : ℝ × E2 => (J p.1).symm p.2) ∧
        (∀ s : ℝ, s ≤ 0 → ∀ y : E2, J s y = y ∧ (J s).symm y = y) ∧
        (∀ s : ℝ, 1 ≤ s → ∀ y : E2,
          J s y = J 1 y ∧ (J s).symm y = (J 1).symm y) ∧
        (∀ s : ℝ,
          tsupport (fun y : E2 => J s y - y) ⊆ C ∧
          tsupport (fun y : E2 => (J s).symm y - y) ⊆ C) ∧
        (∀ s : ℝ, ∀ y : E2, y ∉ C → J s y = y ∧ (J s).symm y = y) ∧
        IsOpen Cᶜ ∧ F ∪ Delta ⊆ Cᶜ ∧
        0 < rho ∧ rho < eta ∧
        (∀ i : Fin 2,
          alpha i '' (Ioo (-rho) (l + rho) ∪ Ioo (r - rho) (1 + rho)) ⊆ Cᶜ) ∧
        (∀ t ∈ Icc (0 : ℝ) 1,
          J 1 (alpha 0 t) = alpha 1 t ∧
          (J 1).symm (alpha 1 t) = alpha 0 t) ∧
        (J 1) '' (alpha 0 '' Icc (0 : ℝ) 1) = alpha 1 '' Icc (0 : ℝ) 1 ∧
        (J 1).symm '' (alpha 1 '' Icc (0 : ℝ) 1) = alpha 0 '' Icc (0 : ℝ) 1 := by
  classical
  dsimp only
  intro hl hlr hr heta hetal hetar hgap hF hKF hAlpha hAlphaInj hAlphaReg
    hEnds hProper hGerms hTails hv hc hcCommon hq hqInj hqReg hqImage hqEnds
    hTracks hcK hcF hWopen hWconn hWunbounded hWcurve hFW hUc hAc hUcJ
    hw hNsource hN hNinv hNzero hNpositive
  let Uarc : Set ℝ := Ioo (-eta) (1 + eta)
  let Gpar : Set ℝ := Ioo (-eta) (l + eta) ∪ Ioo (r - eta) (1 + eta)
  let Tailpar : Set ℝ := Icc 0 l ∪ Icc r 1
  let Umid : Set ℝ := Ioo (l - eta) (r + eta)
  let Dc : Set UnitCircle := {p | (3 / 4 : ℝ) ≤ ⟪v, (p : E2)⟫_ℝ}
  let Jc : Set UnitCircle := {p | (1 / 2 : ℝ) < ⟪v, (p : E2)⟫_ℝ}
  let Delta : Set E2 := c 0 '' Dc
  let Dsrc : Set E2 := {x | ‖x‖ = 1 ∧ (3 / 4 : ℝ) ≤ ⟪v, x⟫_ℝ}
  let D (i : Fin 2) : PlanarSchoenfliesData (c i) := Classical.choice (hP.1 (c i) (hc i))
  let B (i : Fin 2) : BallNeighborhoodChart E2 E2 := (D i).ballNeighborhoodChart
  have hboundary (i : Fin 2) : (B i).boundary = range (c i) :=
    (D i).discChart_image_sphere
  have hparam (i : Fin 2) (p : UnitCircle) : (B i).chart (p : E2) = c i p :=
    (D i).chart_boundary p
  have hWexterior (i : Fin 2) : W i ⊆ (B i).closedRegionᶜ := by
    have hin : (B i).inside ⊆ (B i).closedRegion := image_mono ball_subset_closedBall
    have hdis : Disjoint (B i).inside (B i).closedRegionᶜ :=
      Set.disjoint_left.mpr (fun _ hx hn => hn (hin hx))
    have hcover : W i ⊆ (B i).inside ∪ (B i).closedRegionᶜ := by
      intro y hy
      by_cases hb : y ∈ (B i).closedRegion
      · rw [← (B i).inside_union_boundary] at hb
        rcases hb with hi | hb
        · exact Or.inl hi
        · exact ((Set.disjoint_left.mp (hWcurve i)) hy ((hboundary i) ▸ hb)).elim
      · exact Or.inr hb
    rcases IsPreconnected.subset_or_subset (B i).inside_open
        (B i).closedRegion_compact.isClosed.isOpen_compl hdis hcover
        (hWconn i).isPreconnected with hi | he
    · exact (hWunbounded i ((B i).inside_bounded.subset hi)).elim
    · exact he
  have hBfree (i : Fin 2) : (B i).closedRegion \ Delta ⊆ Fᶜ := by
    rintro y ⟨hy, hyd⟩ hyF
    exact hWexterior i (hFW i ⟨hyF, hyd⟩) hy
  have hDcJ : Dc ⊆ Jc := by intro p hp; dsimp [Dc, Jc] at *; linarith
  have hcommonParam (i : Fin 2) (p : UnitCircle) (hp : p ∈ Jc) : c i p = c 0 p := by
    fin_cases i
    · rfl
    · exact (hcCommon hp).symm
  have hcapImage (i : Fin 2) (e : E2 → E2)
      (he : ∀ p : UnitCircle, e (p : E2) = c i p) : e '' Dsrc = Delta := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      let p : UnitCircle := ⟨x, mem_sphere_zero_iff_norm.mpr hx.1⟩
      have hp : p ∈ Dc := hx.2
      exact ⟨p, hp, ((he p).trans (hcommonParam i p (hDcJ hp))).symm⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨(p : E2), ⟨norm_eq_of_mem_sphere p, hp⟩,
        (he p).trans (hcommonParam i p (hDcJ hp))⟩
  have hDball : Dsrc ⊆ closedBall (0 : E2) 1 :=
    fun _ hx => mem_closedBall_zero_iff.mpr hx.1.le
  have hDsphere : Dsrc ⊆ sphere (0 : E2) 1 :=
    fun _ hx => mem_sphere_zero_iff_norm.mpr hx.1
  have hDcompact : IsCompact Dsrc :=
    (isCompact_sphere (0 : E2) 1).of_isClosed_subset
      ((isClosed_eq continuous_norm continuous_const).inter
        (isClosed_le continuous_const (innerSL ℝ v).continuous)) hDsphere
  let T := (B 0).chart.trans (B 1).chart.symm
  have hT : ContDiffOn ℝ ∞ T T.source :=
    (B 1).smooth_symm.comp ((B 0).smooth.mono inter_subset_left) (fun _ hx => hx.2)
  have hTi : ContDiffOn ℝ ∞ T.symm T.target :=
    (B 0).smooth_symm.comp ((B 1).smooth.mono inter_subset_left) (fun _ hx => hx.2)
  have hTunit (x : E2) (hx : ‖x‖ = 1) (ha : (1 / 2 : ℝ) < ⟪v, x⟫_ℝ) :
      x ∈ T.source ∧ T x = x := by
    let p : UnitCircle := ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩
    have heq : (B 0).chart x = (B 1).chart x :=
      (hparam 0 p).trans ((hcCommon ha).trans (hparam 1 p).symm)
    have hb : x ∈ closedBall (0 : E2) 1 := mem_closedBall_zero_iff.mpr hx.le
    refine ⟨⟨(B 0).closedBall_subset_source hb, ?_⟩, ?_⟩
    · change (B 0).chart x ∈ (B 1).chart.target
      rw [heq]
      exact (B 1).chart.map_source ((B 1).closedBall_subset_source hb)
    · change (B 1).chart.symm ((B 0).chart x) = x
      rw [heq]
      exact (B 1).chart.left_inv ((B 1).closedBall_subset_source hb)
  have hDT : Dsrc ⊆ T.source :=
    fun x hx => (hTunit x hx.1 (by linarith [hx.2])).1
  have hpositive : ∀ (x : E2), ‖x‖ = 1 → (2 / 3 : ℝ) < ⟪v, x⟫_ℝ →
      0 < ⟪x, fderiv ℝ T x x⟫_ℝ := by
    intro x hx ha
    let H : (UnitCircle × ℝ) ≃ₜ (UnitCircle × ℝ) := {
      toEquiv := {
        toFun := fun p => (p.1, p.2 - 1)
        invFun := fun p => (p.1, p.2 + 1)
        left_inv := by rintro ⟨p, s⟩; simp
        right_inv := by rintro ⟨p, s⟩; simp }
      continuous_toFun := continuous_fst.prodMk (continuous_snd.sub continuous_const)
      continuous_invFun := continuous_fst.prodMk (continuous_snd.add continuous_const) }
    have hH : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ H :=
      contMDiff_fst.prodMk
        ((contDiff_id.sub (contDiff_const (c := (1 : ℝ)))).contMDiff.comp contMDiff_snd)
    have hHi : ContMDiff ((𝓡 1).prod 𝓘(ℝ, ℝ)) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ H.symm :=
      contMDiff_fst.prodMk
        ((contDiff_id.add (contDiff_const (c := (1 : ℝ)))).contMDiff.comp contMDiff_snd)
    let P := (circleRadialChart.symm.trans H.toOpenPartialHomeomorph).trans N
    have hPsm : ContDiffOn ℝ ∞ P P.source :=
      (hN.comp (hH.comp_contMDiffOn
        (circleRadialChart_symm_contMDiffOn.mono (fun _ hy => hy.1.1)))
        (fun _ hy => hy.2)).contDiffOn
    have hPim : ContDiffOn ℝ ∞ P.symm P.target :=
      (circleRadialChart_contMDiffOn.comp
        (hHi.comp_contMDiffOn (hNinv.mono (fun _ hy => hy.1)))
        (fun _ hy => hy.2.2)).contDiffOn
    let S (i : Fin 2) := P.trans (B i).chart.symm
    have hS (i : Fin 2) : ContDiffOn ℝ ∞ (S i) (S i).source :=
      (B i).smooth_symm.comp (hPsm.mono inter_subset_left) (fun _ hy => hy.2)
    have hSi (i : Fin 2) : ContDiffOn ℝ ∞ (S i).symm (S i).target :=
      hPim.comp ((B i).smooth.mono inter_subset_left) (fun _ hy => hy.2)
    have hSunit (i : Fin 2) (y : E2) (hy : ‖y‖ = 1) (hyUc : circleDirection y ∈ Uc) :
        y ∈ (S i).source ∧ S i y = y := by
      let py : UnitCircle := ⟨y, mem_sphere_zero_iff_norm.mpr hy⟩
      have hdir : circleDirection y = py := circleDirection_coe_unit py
      have hpy : py ∈ Uc := hdir ▸ hyUc
      have hPy : y ∈ P.source := by
        refine ⟨⟨ne_zero_of_mem_unit_sphere py, mem_univ _⟩, ?_⟩
        change (circleDirection y, ‖y‖ - 1) ∈ N.source
        rw [hdir, hy, sub_self]
        exact hNsource ⟨hpy, ⟨by linarith, by linarith⟩⟩
      have hval : P y = (B i).chart y := by
        change N (circleDirection y, ‖y‖ - 1) = (B i).chart y
        rw [hdir, hy, sub_self, hNzero py hpy]
        exact ((hparam i py).trans (hcommonParam i py (hUcJ hpy))).symm
      have hb : y ∈ closedBall (0 : E2) 1 := mem_closedBall_zero_iff.mpr hy.le
      refine ⟨⟨hPy, ?_⟩, ?_⟩
      · change P y ∈ (B i).chart.target
        rw [hval]
        exact (B i).chart.map_source ((B i).closedBall_subset_source hb)
      · change (B i).chart.symm (P y) = y
        rw [hval]
        exact (B i).chart.left_inv ((B i).closedBall_subset_source hb)
    let px : UnitCircle := ⟨x, mem_sphere_zero_iff_norm.mpr hx⟩
    have hpx : px ∈ Uc := hAc (show (2 / 3 : ℝ) ≤ ⟪v, (px : E2)⟫_ℝ from ha.le)
    have hxdir : circleDirection x ∈ Uc := by
      rw [show circleDirection x = px from circleDirection_coe_unit px]
      exact hpx
    have hdir : ∀ᶠ y in 𝓝 x, circleDirection y ∈ Uc :=
      (circleDirection_contMDiffOn.continuousOn.continuousAt
        (isClosed_singleton.isOpen_compl.mem_nhds
          (ne_zero_of_mem_unit_sphere px))).preimage_mem_nhds
          (hUc.mem_nhds hxdir)
    have hheight : ∀ᶠ y in 𝓝 x, ‖y‖ - 1 ∈ Ioo (-w) w :=
      (continuous_norm.sub continuous_const).continuousAt.preimage_mem_nhds
        (isOpen_Ioo.mem_nhds (show ‖x‖ - 1 ∈ Ioo (-w) w by rw [hx]; constructor <;> linarith))
    have hSx (i : Fin 2) : x ∈ (S i).source ∧ S i x = x := hSunit i x hx hxdir
    have hSd (i : Fin 2) : DifferentiableAt ℝ (S i) x :=
      ((hS i).contDiffAt ((S i).open_source.mem_nhds (hSx i).1)).differentiableAt (by simp)
    have hnS (i : Fin 2) : 0 < ⟪x, fderiv ℝ (S i) x x⟫_ℝ := by
      obtain ⟨L, hL⟩ := exists_smoothChart_derivative (S i) (hS i) (hSi i) (hSx i).1
      apply fderiv_normal_pos_of_local_exterior (S i) hx (hSd i)
      · filter_upwards [hdir] with y hy hyn
        exact (hSunit i y hyn hy).2
      · rw [hL.fderiv]
        exact L.injective
      · filter_upwards [hdir, hheight, (S i).open_source.mem_nhds (hSx i).1]
          with y hyUc hyheight hyS hynorm
        rcases eq_or_lt_of_le hynorm with heq | hlt
        · rw [(hSunit i y heq.symm hyUc).2]
          exact hynorm
        · by_contra hn
          have hyW : P y ∈ W i := hNpositive i
            ⟨(circleDirection y, ‖y‖ - 1), ⟨hyUc, ⟨by linarith, hyheight.2⟩⟩, rfl⟩
          have hyB : P y ∈ (B i).closedRegion :=
            ⟨S i y, mem_closedBall_zero_iff.mpr (lt_of_not_ge hn).le,
              (B i).chart.right_inv hyS.2⟩
          exact hWexterior i hyW hyB
    have hxT : x ∈ T.source := (hTunit x hx (by linarith)).1
    have hTd : DifferentiableAt ℝ T x :=
      (hT.contDiffAt (T.open_source.mem_nhds hxT)).differentiableAt (by simp)
    have hTf : ∀ᶠ y in 𝓝 x, ‖y‖ = 1 → T y = y := by
      have hinner : ∀ᶠ y in 𝓝 x, (1 / 2 : ℝ) < ⟪v, y⟫_ℝ :=
        (innerSL ℝ v).continuous.continuousAt.preimage_mem_nhds
          (isOpen_Ioi.mem_nhds (show (1 / 2 : ℝ) < ⟪v, x⟫_ℝ by linarith))
      filter_upwards [hinner] with y hy hyn
      exact (hTunit y hyn hy).2
    have hcomp : (fun y => T (S 0 y)) =ᶠ[𝓝 x] (fun y => S 1 y) := by
      filter_upwards [(S 0).open_source.mem_nhds (hSx 0).1] with y hy
      change (B 1).chart.symm ((B 0).chart ((B 0).chart.symm (P y))) = (B 1).chart.symm (P y)
      have hyB : P y ∈ (B 0).chart.target := hy.2
      rw [(B 0).chart.right_inv hyB]
    have hTd0 : HasFDerivAt T (fderiv ℝ T x) (S 0 x) := by
      rw [(hSx 0).2]
      exact hTd.hasFDerivAt
    have hchain : (fderiv ℝ T x).comp (fderiv ℝ (S 0) x) = fderiv ℝ (S 1) x :=
      ((hTd0.comp x (hSd 0).hasFDerivAt).congr_of_eventuallyEq hcomp.symm).unique
        (hSd 1).hasFDerivAt
    let A0 := fderiv ℝ (S 0) x
    let AT := fderiv ℝ T x
    let n0 := ⟪x, A0 x⟫_ℝ
    let z := A0 x - n0 • x
    have hz : ⟪x, z⟫_ℝ = 0 := by
      dsimp [z, n0]
      rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, hx, one_pow,
        mul_one, sub_self]
    have htz : AT z = z := fderiv_eq_of_local_fixed_sphere T x z hx hTd hTf hz
    have hsum : A0 x = n0 • x + z := by dsimp [z]; abel
    have hnormal : n0 * ⟪x, AT x⟫_ℝ = ⟪x, fderiv ℝ (S 1) x x⟫_ℝ := by
      have heq := congrArg (fun L : E2 →L[ℝ] E2 => ⟪x, L x⟫_ℝ) hchain
      change ⟪x, AT (A0 x)⟫_ℝ = ⟪x, fderiv ℝ (S 1) x x⟫_ℝ at heq
      rw [hsum, map_add, map_smul, htz, inner_add_right, inner_smul_right, hz, add_zero] at heq
      exact heq
    have hprod : 0 < n0 * ⟪x, AT x⟫_ℝ := by rw [hnormal]; exact hnS 1
    exact pos_of_mul_pos_right hprod (hnS 0).le
  let Z : Set E2 := {x | ‖x‖ = 1 ∧ ⟪v, x⟫_ℝ ≤ (2 / 3 : ℝ)}
  let U : Set E2 := T.source \ ({0} ∪ Z)
  have hZ : IsClosed Z := (isClosed_eq continuous_norm continuous_const).inter
    (isClosed_le (innerSL ℝ v).continuous continuous_const)
  have hU : IsOpen U := T.open_source.sdiff (isClosed_singleton.union hZ)
  have hDU : Dsrc ⊆ U := by
    intro x hx
    refine ⟨hDT hx, ?_⟩
    rintro (hz | hz)
    · have hx0 : x = 0 := hz
      have hnorm := hx.1
      rw [hx0, norm_zero] at hnorm
      exact zero_ne_one hnorm
    · exact (not_le_of_gt (by linarith [hx.2] : (2 / 3 : ℝ) < ⟪v, x⟫_ℝ)) hz.2
  have hUunit (x : E2) (hxU : x ∈ U) (hx : ‖x‖ = 1) :
      (2 / 3 : ℝ) < ⟪v, x⟫_ℝ := by
    by_contra h
    exact hxU.2 (Or.inr ⟨hx, le_of_not_gt h⟩)
  obtain ⟨chi, hchi, _, hsChi, hone, hrange⟩ :=
    exists_compact_smooth_cutoff hDcompact hU hDU
  let f : E2 → E2 := fun x => x + chi x • (T x - x)
  have hf : ContDiff ℝ ∞ f := contDiff_id.add
    (contDiff_cutoff_smul hU chi hchi hsChi (fun x => T x - x)
      ((hT.mono (fun _ hx => hx.1)).sub contDiff_id.contDiffOn))
  have hfixSphere (x : E2) (hx : x ∈ sphere (0 : E2) 1) : f x = x := by
    by_cases hxU : x ∈ U
    · have hTx := (hTunit x (mem_sphere_zero_iff_norm.mp hx)
        (by linarith [hUunit x hxU (mem_sphere_zero_iff_norm.mp hx)])).2
      simp only [f, hTx, sub_self, smul_zero, add_zero]
    · have hzero : chi x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxU (hsChi h))
      simp only [f, hzero, zero_smul, add_zero]
  have hn (x : E2) (hx : x ∈ sphere (0 : E2) 1) :
      0 < ⟪x, fderiv ℝ f x x⟫_ℝ := by
    have hnorm : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    by_cases hxU : x ∈ U
    · have ha := hUunit x hxU hnorm
      have hTx := (hTunit x hnorm (by linarith)).2
      have hTd := (hT.contDiffAt (T.open_source.mem_nhds hxU.1)).differentiableAt (by simp)
      have hd := (hasFDerivAt_id x).add
        (((hchi.differentiable (by simp)) x).hasFDerivAt.smul
          (hTd.hasFDerivAt.sub (hasFDerivAt_id x)))
      have heval : fderiv ℝ f x x = x + chi x • (fderiv ℝ T x x - x) := by
        change fderiv ℝ (id + chi • ((T : E2 → E2) - id)) x x = _
        rw [hd.fderiv]
        simp only [add_apply, smul_apply, sub_apply, ContinuousLinearMap.id_apply,
          ContinuousLinearMap.smulRight_apply, Pi.sub_apply, id_eq, hTx,
          sub_self, smul_zero, add_zero]
      rw [heval, inner_add_right, inner_smul_right, inner_sub_right,
        real_inner_self_eq_norm_sq, hnorm, one_pow]
      have hp := hpositive x hnorm ha
      by_cases hz : chi x = 0
      · simp only [hz, zero_mul, add_zero]; norm_num
      · have hcp : 0 < chi x := lt_of_le_of_ne (hrange x).1 (Ne.symm hz)
        nlinarith [(hrange x).2, mul_pos hcp hp]
    · have hnear : f =ᶠ[𝓝 x] (fun y => y) := by
        filter_upwards [(isClosed_tsupport chi).isOpen_compl.mem_nhds
          (fun h => hxU (hsChi h))] with y hy
        simp only [f, image_eq_zero_of_notMem_tsupport hy, zero_smul, add_zero]
      rw [((hasFDerivAt_id x).congr_of_eventuallyEq hnear).fderiv,
        ContinuousLinearMap.id_apply, real_inner_self_eq_norm_sq, hnorm, one_pow]
      norm_num
  obtain ⟨Xi, hXi, hXi0, hXiFixed, hXiNear, _, _, _⟩ :=
    exists_sphere_collar_correction f isOpen_univ (subset_univ _) hf.contDiffOn hfixSphere hn
  let R := Xi 1
  have hRfixed (x : E2) (hx : x ∈ sphere (0 : E2) 1) : R x = x :=
    hXiFixed 1 (by norm_num) x hx
  have hRimages := fixedSphere_isotopy_image_balls (fun t => (Xi t).toHomeomorph)
    (fun x => (hXi.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn)
    hXi0 (fun t ht x hx => hXiFixed t ht x (mem_sphere_zero_iff_norm.mpr hx))
    (t := 1) (by norm_num)
  have hRnear : ∀ᶠ x in 𝓝ˢ Dsrc, R x = T x := by
    filter_upwards [hXiNear.filter_mono (nhdsSet_mono hDsphere), hone] with x hx hc
    change Xi 1 x = T x
    rw [hx]
    simp only [f, hc, one_smul]
    abel
  let A : BallNeighborhoodChart E2 E2 := {
    chart := R.toHomeomorph.toOpenPartialHomeomorph.trans (B 1).chart
    closedBall_subset_source := by
      intro x hx
      exact ⟨mem_univ _, (B 1).closedBall_subset_source
        (hRimages.2 ▸ mem_image_of_mem R hx)⟩
    smooth := (B 1).smooth.comp R.contDiff.contDiffOn (fun _ hx => hx.2)
    smooth_symm := R.symm.contDiff.comp_contDiffOn ((B 1).smooth_symm.mono inter_subset_left) }
  have hAinside : A.inside = (B 1).inside := by
    change ((B 1).chart ∘ R) '' ball 0 1 = (B 1).chart '' ball 0 1
    rw [image_comp]
    exact congrArg (fun s : Set E2 => (B 1).chart '' s) hRimages.1
  have hAclosed : A.closedRegion = (B 1).closedRegion := by
    change ((B 1).chart ∘ R) '' closedBall 0 1 = (B 1).chart '' closedBall 0 1
    rw [image_comp]
    exact congrArg (fun s : Set E2 => (B 1).chart '' s) hRimages.2
  have hAparam (p : UnitCircle) : A.chart (p : E2) = c 1 p := by
    change (B 1).chart (R (p : E2)) = c 1 p
    rw [hRfixed (p : E2) p.property, hparam]
  have hcommon : ∀ᶠ x in 𝓝ˢ Dsrc, (B 0).chart x = A.chart x := by
    filter_upwards [hRnear, T.open_source.mem_nhdsSet.mpr hDT] with x hx hxs
    change (B 0).chart x = (B 1).chart (R x)
    rw [hx]
    exact ((B 1).chart.right_inv hxs.2).symm
  have hAfree : A.closedRegion \ Delta ⊆ Fᶜ := by rw [hAclosed]; exact hBfree 1
  have hcap0 : (B 0).chart '' Dsrc = Delta := hcapImage 0 (B 0).chart (hparam 0)
  have hcap1 : A.chart '' Dsrc = Delta := hcapImage 1 A.chart hAparam
  obtain ⟨V, hV, hDV, hVeq⟩ := eventually_nhdsSet_iff_exists.mp hcommon
  let V0 := (V ∩ (B 0).chart.source) ∩ A.chart.source
  have hV0 : IsOpen V0 := (hV.inter (B 0).chart.open_source).inter A.chart.open_source
  have hDV0 : Dsrc ⊆ V0 := fun _ hx =>
    ⟨⟨hDV hx, (B 0).closedBall_subset_source (hDball hx)⟩,
      A.closedBall_subset_source (hDball hx)⟩
  let Wsrc := ((B 0).chart.source ∩ (B 0).chart ⁻¹' Fᶜ) ∩
    (A.chart.source ∩ A.chart ⁻¹' Fᶜ)
  have hWsrc : IsOpen Wsrc :=
    ((B 0).chart.isOpen_inter_preimage hF.isOpen_compl).inter
      (A.chart.isOpen_inter_preimage hF.isOpen_compl)
  have hballW : closedBall (0 : E2) 1 \ Dsrc ⊆ Wsrc := by
    intro x hx
    refine ⟨⟨(B 0).closedBall_subset_source hx.1, hBfree 0 ⟨⟨x, hx.1, rfl⟩, ?_⟩⟩,
      ⟨A.closedBall_subset_source hx.1, hAfree ⟨⟨x, hx.1, rfl⟩, ?_⟩⟩⟩
    · rw [← hcap0]
      rintro ⟨z, hz, heq⟩
      have hzx := (B 0).chart.injOn ((B 0).closedBall_subset_source (hDball hz))
        ((B 0).closedBall_subset_source hx.1) heq
      exact hx.2 (hzx ▸ hz)
    · rw [← hcap1]
      rintro ⟨z, hz, heq⟩
      have hzx := A.chart.injOn (A.closedBall_subset_source (hDball hz))
        (A.closedBall_subset_source hx.1) heq
      exact hx.2 (hzx ▸ hz)
  obtain ⟨T0, hT0, Phi, hPhi, hPhi0, _, hfinal, _, Csrc, hCsrc, hCs, hfixSrc⟩ :=
    exists_relative_cap_compression v hv (3 / 4) (by norm_num) hV0 hDV0 hWsrc hballW
  have hC0 : Csrc ⊆ (B 0).chart.source := fun _ hx => (hCs hx).1.1.1
  have hC1 : Csrc ⊆ A.chart.source := fun _ hx => (hCs hx).1.2.1
  obtain ⟨beta0, hb0, hb00, htrack0, hfix0, hcomp0, _⟩ :=
    exists_chart_transport_isotopy (B 0).chart (B 0).smooth (B 0).smooth_symm
      Phi hPhi hPhi0 hCsrc hC0 hfixSrc
  obtain ⟨beta1, hb1, hb10, htrack1, hfix1, hcomp1, _⟩ :=
    exists_chart_transport_isotopy A.chart A.smooth A.smooth_symm
      Phi hPhi hPhi0 hCsrc hC1 hfixSrc
  let C : Set E2 := (B 0).chart '' Csrc ∪ A.chart '' Csrc
  have hC : IsCompact C := hcomp0.union hcomp1
  have hCfree : C ⊆ Fᶜ \ Delta := by
    rintro y (hy | hy)
    · rcases hy with ⟨x, hx, rfl⟩
      refine ⟨(hCs hx).1.1.2, ?_⟩
      rw [← hcap0]
      rintro ⟨z, hz, heq⟩
      have hzx := (B 0).chart.injOn ((B 0).closedBall_subset_source (hDball hz)) (hC0 hx) heq
      exact (hCs hx).2 (hzx ▸ hz)
    · rcases hy with ⟨x, hx, rfl⟩
      refine ⟨(hCs hx).1.2.2, ?_⟩
      rw [← hcap1]
      rintro ⟨z, hz, heq⟩
      have hzx := A.chart.injOn (A.closedBall_subset_source (hDball hz)) (hC1 hx) heq
      exact (hCs hx).2 (hzx ▸ hz)
  have hprotected : F ∪ Delta ⊆ Cᶜ := by
    intro y hy hyC
    exact hy.elim (hCfree hyC).1 (hCfree hyC).2
  have hbi0 := planarDiffeomorphFamily_contDiff_symm beta0 hb0
  have hbi1 := planarDiffeomorphFamily_contDiff_symm beta1 hb1
  let clock : ℝ → ℝ := fun s => T0 * Real.smoothTransition s
  have hclock : ContDiff ℝ ∞ clock := contDiff_const.mul Real.smoothTransition.contDiff
  let J := fun s => (beta0 (clock s)).trans (beta1 (clock s)).symm
  have hJ : ContDiff ℝ ∞ (fun p : ℝ × E2 => J p.1 p.2) :=
    hbi1.comp ((hclock.comp contDiff_fst).prodMk
      (hb0.comp ((hclock.comp contDiff_fst).prodMk contDiff_snd)))
  have hJi : ContDiff ℝ ∞ (fun p : ℝ × E2 => (J p.1).symm p.2) :=
    hbi0.comp ((hclock.comp contDiff_fst).prodMk
      (hb1.comp ((hclock.comp contDiff_fst).prodMk contDiff_snd)))
  have hJfix (s : ℝ) (y : E2) (hy : y ∉ C) : J s y = y ∧ (J s).symm y = y := by
    have hy0 : y ∉ (B 0).chart '' Csrc := fun h => hy (Or.inl h)
    have hy1 : y ∉ A.chart '' Csrc := fun h => hy (Or.inr h)
    constructor
    · change (beta1 (clock s)).symm (beta0 (clock s) y) = y
      rw [hfix0 (clock s) y hy0]
      exact equiv_symm_fixed_of_fixed (beta1 (clock s)).toEquiv (hfix1 (clock s) y hy1)
    · change (beta0 (clock s)).symm (beta1 (clock s) y) = y
      rw [hfix1 (clock s) y hy1]
      exact equiv_symm_fixed_of_fixed (beta0 (clock s)).toEquiv (hfix0 (clock s) y hy0)
  have hJzero (s : ℝ) (hs : s ≤ 0) (y : E2) : J s y = y ∧ (J s).symm y = y := by
    have hc0 : clock s = 0 := by
      simp only [clock, Real.smoothTransition.zero_of_nonpos hs, mul_zero]
    constructor
    · change (beta1 (clock s)).symm (beta0 (clock s) y) = y
      rw [hc0, hb00]
      exact equiv_symm_fixed_of_fixed (beta1 0).toEquiv (hb10 y)
    · change (beta0 (clock s)).symm (beta1 (clock s) y) = y
      rw [hc0, hb10]
      exact equiv_symm_fixed_of_fixed (beta0 0).toEquiv (hb00 y)
  have hJone (s : ℝ) (hs : 1 ≤ s) (y : E2) :
      J s y = J 1 y ∧ (J s).symm y = (J 1).symm y := by
    have hc1 : clock s = clock 1 := by
      simp only [clock, Real.smoothTransition.one_of_one_le hs, Real.smoothTransition.one]
    constructor <;> simp only [J, hc1]
  have hsupport (s : ℝ) : tsupport (fun y : E2 => J s y - y) ⊆ C ∧
      tsupport (fun y : E2 => (J s).symm y - y) ⊆ C := by
    constructor
    · apply closure_minimal ?_ hC.isClosed
      intro y hy
      by_contra h
      exact hy (sub_eq_zero.mpr (hJfix s y h).1)
    · apply closure_minimal ?_ hC.isClosed
      intro y hy
      by_contra h
      exact hy (sub_eq_zero.mpr (hJfix s y h).2)
  have hpoint (x : E2) (hx : x ∈ closedBall (0 : E2) 1) :
      J 1 ((B 0).chart x) = A.chart x := by
    change (beta1 (T0 * Real.smoothTransition 1)).symm
      (beta0 (T0 * Real.smoothTransition 1) ((B 0).chart x)) = A.chart x
    rw [Real.smoothTransition.one, mul_one,
      htrack0 T0 x ((B 0).closedBall_subset_source hx),
      hVeq (Phi T0 x) (hfinal hx).1.1,
      ← htrack1 T0 x (A.closedBall_subset_source hx), (beta1 T0).symm_apply_apply]
  have hTailG : Tailpar ⊆ Gpar := by
    rintro t (ht | ht)
    · exact Or.inl ⟨by linarith [ht.1], by linarith [ht.2]⟩
    · exact Or.inr ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hTailU : Tailpar ⊆ Uarc := by
    rintro t (ht | ht) <;> exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hTailsBoth (i : Fin 2) : alpha i '' Tailpar ⊆ F := by
    rintro y ⟨t, ht, rfl⟩
    have h0 : alpha 0 t ∈ F := hTails ⟨t, ht, rfl⟩
    fin_cases i
    · exact h0
    · exact (hGerms (hTailG ht)) ▸ h0
  have hTailFixed (i : Fin 2) (t : ℝ) (ht : t ∈ Tailpar) : alpha i t ∈ Cᶜ :=
    hprotected (Or.inl (hTailsBoth i ⟨t, ht, rfl⟩))
  have hArc (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : J 1 (alpha 0 t) = alpha 1 t := by
    by_cases htl : t ≤ l
    · have htail : t ∈ Tailpar := Or.inl ⟨ht.1, htl⟩
      rw [(hJfix 1 (alpha 0 t) (hTailFixed 0 t htail)).1]
      exact hGerms (hTailG htail)
    · by_cases hrt : r ≤ t
      · have htail : t ∈ Tailpar := Or.inr ⟨hrt, ht.2⟩
        rw [(hJfix 1 (alpha 0 t) (hTailFixed 0 t htail)).1]
        exact hGerms (hTailG htail)
      · have hlt : l < t := lt_of_not_ge htl
        have htr : t < r := lt_of_not_ge hrt
        have hmid : t ∈ Umid := ⟨by linarith, by linarith⟩
        rw [← hTracks 0 t hmid, ← hparam 0 (q t),
          hpoint (q t : E2) (sphere_subset_closedBall (q t).property), hAparam,
          hTracks 1 t hmid]
  have hArcInv (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (J 1).symm (alpha 1 t) = alpha 0 t := by
    rw [← hArc t ht, (J 1).symm_apply_apply]
  let Vpar := (Uarc ∩ (alpha 0) ⁻¹' Cᶜ) ∩ (Uarc ∩ (alpha 1) ⁻¹' Cᶜ)
  have hVpar : IsOpen Vpar :=
    ((hAlpha 0).continuousOn.isOpen_inter_preimage isOpen_Ioo hC.isClosed.isOpen_compl).inter
      ((hAlpha 1).continuousOn.isOpen_inter_preimage isOpen_Ioo hC.isClosed.isOpen_compl)
  have hTailV : Tailpar ⊆ Vpar := fun t ht =>
    ⟨⟨hTailU ht, hTailFixed 0 t ht⟩, ⟨hTailU ht, hTailFixed 1 t ht⟩⟩
  have hTailCompact : IsCompact Tailpar :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) l)).union
      (isCompact_Icc : IsCompact (Icc r (1 : ℝ)))
  obtain ⟨d, hd, hdV⟩ := hTailCompact.exists_thickening_subset_open hVpar hTailV
  let rho : ℝ := min eta d / 2
  have hrho : 0 < rho := div_pos (lt_min heta hd) (by norm_num)
  have hrhoEta : rho < eta := by dsimp [rho]; linarith [min_le_left eta d]
  have hrhoD : rho < d := by dsimp [rho]; linarith [min_le_right eta d]
  have hwindow (t : ℝ)
      (ht : t ∈ Ioo (-rho) (l + rho) ∪ Ioo (r - rho) (1 + rho)) :
      t ∈ thickening d Tailpar := by
    rcases ht with ht | ht
    · by_cases ht0 : t < 0
      · apply mem_thickening_iff.mpr
        refine ⟨0, Or.inl ⟨le_rfl, hl.le⟩, ?_⟩
        rw [Real.dist_eq, sub_zero, abs_of_neg ht0]
        linarith [ht.1]
      · by_cases htl : t ≤ l
        · exact mem_thickening_iff.mpr ⟨t, Or.inl ⟨le_of_not_gt ht0, htl⟩, by simpa using hd⟩
        · apply mem_thickening_iff.mpr
          refine ⟨l, Or.inl ⟨hl.le, le_rfl⟩, ?_⟩
          rw [Real.dist_eq, abs_of_pos (sub_pos.mpr (lt_of_not_ge htl))]
          linarith [ht.2]
    · by_cases ht1 : 1 < t
      · apply mem_thickening_iff.mpr
        refine ⟨1, Or.inr ⟨hr.le, le_rfl⟩, ?_⟩
        rw [Real.dist_eq, abs_of_pos (sub_pos.mpr ht1)]
        linarith [ht.2]
      · by_cases hrt : r ≤ t
        · exact mem_thickening_iff.mpr ⟨t, Or.inr ⟨hrt, le_of_not_gt ht1⟩, by simpa using hd⟩
        · apply mem_thickening_iff.mpr
          refine ⟨r, Or.inr ⟨le_rfl, hr.le⟩, ?_⟩
          rw [Real.dist_eq, abs_of_neg (sub_neg.mpr (lt_of_not_ge hrt))]
          linarith [ht.1]
  have hbuffer (i : Fin 2) :
      alpha i '' (Ioo (-rho) (l + rho) ∪ Ioo (r - rho) (1 + rho)) ⊆ Cᶜ := by
    rintro y ⟨t, ht, rfl⟩
    have hvp := hdV (hwindow t ht)
    fin_cases i
    · exact hvp.1.2
    · exact hvp.2.2
  refine ⟨C, J, rho, hC, hCfree, hJ, hJi, hJzero, hJone, hsupport, hJfix,
    hC.isClosed.isOpen_compl, hprotected, hrho, hrhoEta, hbuffer,
    (fun t ht => ⟨hArc t ht, hArcInv t ht⟩), ?_, ?_⟩
  · rw [← image_comp]
    exact image_congr (fun t ht => hArc t ht)
  · rw [← image_comp]
    exact image_congr (fun t ht => hArcInv t ht)

end PoincareConjecture.M25.Topology3D
