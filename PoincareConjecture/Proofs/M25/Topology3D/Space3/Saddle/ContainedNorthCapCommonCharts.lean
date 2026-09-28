import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NorthBoundaryPatchPullback
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallDiscExtension
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallCapGermCorrection
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallNativeCapCoordinates
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallChartReparametrization
import Mathlib.Topology.NhdsSet
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum









set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem exists_contained_north_cap_common_charts
    (A N : BallNeighborhoodChart E3 E3) (o : ℝ)
    (ho : 0 < o) (ho1 : o < 1)
    (hpatch : ∀ q : UnitTwoSphere, -o < (heightCoordinates (q : E3)).2 →
      N.chart (q : E3) ∈ A.boundary)
    (hcontain : N.closedRegion ⊆ A.closedRegion) :
    let Da := {y : E3 | ‖y‖ = 1 ∧ (3 / 4 : ℝ) ≤ (heightCoordinates y).2}
    let Delta := N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
    ∃ (G0 G1 F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞)
      (Ahat Nhat : BallNeighborhoodChart E3 E3) (V : Set E3),
      (∀ y : E3, ‖G0 y‖ = ‖y‖ ∧ ‖G1 y‖ = ‖y‖) ∧
      (∀ y ∈ sphere (0 : E3) 1, F y = y) ∧
      F '' ball (0 : E3) 1 = ball 0 1 ∧
      F '' closedBall (0 : E3) 1 = closedBall 0 1 ∧
      Ahat.chart = (F.trans G0).toHomeomorph.toOpenPartialHomeomorph.trans A.chart ∧
      Nhat.chart = G1.toHomeomorph.toOpenPartialHomeomorph.trans N.chart ∧
      Ahat.chart.source = {y : E3 | G0 (F y) ∈ A.chart.source} ∧
      Nhat.chart.source = G1 ⁻¹' N.chart.source ∧
      Ahat.chart.target = A.chart.target ∧ Nhat.chart.target = N.chart.target ∧
      (∀ y : E3, Ahat.chart y = A.chart (G0 (F y)) ∧
        Nhat.chart y = N.chart (G1 y)) ∧
      (∀ y : E3, Ahat.chart.symm y = F.symm (G0.symm (A.chart.symm y)) ∧
        Nhat.chart.symm y = G1.symm (N.chart.symm y)) ∧
      Ahat.inside = A.inside ∧ Ahat.closedRegion = A.closedRegion ∧
      Ahat.boundary = A.boundary ∧ Nhat.inside = N.inside ∧
      Nhat.closedRegion = N.closedRegion ∧ Nhat.boundary = N.boundary ∧
      Ahat.chart '' Da = Delta ∧ Nhat.chart '' Da = Delta ∧
      IsOpen V ∧ Da ⊆ V ∧ V ⊆ Ahat.chart.source ∩ Nhat.chart.source ∧
      EqOn Ahat.chart Nhat.chart V := by
  classical
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  let Da : Set E3 :=
    {y : E3 | ‖y‖ = 1 ∧ (3 / 4 : ℝ) ≤ (heightCoordinates y).2}
  let Delta : Set E3 :=
    N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
  let R : ℝ := Real.sqrt ((1 + o) / (1 - o))
  obtain ⟨e, hR, hesource, hetarget, he, hei, heclosed, hepoint, heinv, hecap⟩ :=
    exists_north_boundary_patch_pullback A N o ho ho1 hpatch
  change 1 < R at hR
  change e.source = ball (0 : E2) R at hesource
  have ha : (3 / 4 : ℝ) ∈ Ioo (1 / 2 : ℝ) 1 := by norm_num
  let P := referenceCapSphereChart (3 / 4 : ℝ) ha
  obtain ⟨hPs, hPt, hPpoint, hPi, hP, hPiSmooth, hPcap⟩ :=
    referenceCapSphereChart_spec (3 / 4 : ℝ) ha
  have hPclosed : closedBall (0 : E2) 1 ⊆ P.source := by
    rw [hPs]
    exact subset_univ _
  have hnorthclosed : closedBall (0 : E2) 1 ⊆ northSphereChart.symm.source :=
    subset_univ _
  obtain ⟨r0, hr0, hdomains0, G0, hG0, hpoint0⟩ :=
    exists_sphere_disc_pointwise_extension P e hPclosed heclosed
      hP hPiSmooth he hei
  obtain ⟨r1, hr1, hdomains1, G1, hG1, hpoint1⟩ :=
    exists_sphere_disc_pointwise_extension P northSphereChart.symm hPclosed hnorthclosed
      hP hPiSmooth northSphereChart_symm_contMDiff.contMDiffOn
      northSphereChart_contMDiffOn
  let r : ℝ := min r0 r1
  have hr : 1 < r := lt_min hr0 hr1
  have hrr0 : r ≤ r0 := min_le_left _ _
  have hrr1 : r ≤ r1 := min_le_right _ _
  have hG0i (y : E3) : ‖G0.symm y‖ = ‖y‖ := by
    have hh := hG0 (G0.symm y)
    rw [G0.apply_symm_apply] at hh
    exact hh.symm
  have hG1i (y : E3) : ‖G1.symm y‖ = ‖y‖ := by
    have hh := hG1 (G1.symm y)
    rw [G1.apply_symm_apply] at hh
    exact hh.symm
  let A0 := A.normReparametrize G0.symm hG0i
  let N0 := N.normReparametrize G1.symm hG1i
  have hA0point (y : E3) : A0.chart y = A.chart (G0 y) := rfl
  have hN0point (y : E3) : N0.chart y = N.chart (G1 y) := rfl
  have hA0inv (y : E3) : A0.chart.symm y = G0.symm (A.chart.symm y) := rfl
  have hN0inv (y : E3) : N0.chart.symm y = G1.symm (N.chart.symm y) := rfl
  have hA0source : A0.chart.source = G0 ⁻¹' A.chart.source := by
    ext y
    change (y ∈ (univ : Set E3) ∧ G0 y ∈ A.chart.source) ↔ G0 y ∈ A.chart.source
    simp only [mem_univ, true_and]
  have hN0source : N0.chart.source = G1 ⁻¹' N.chart.source := by
    ext y
    change (y ∈ (univ : Set E3) ∧ G1 y ∈ N.chart.source) ↔ G1 y ∈ N.chart.source
    simp only [mem_univ, true_and]
  have hA0target : A0.chart.target = A.chart.target := by
    ext y
    change (y ∈ A.chart.target ∧ A.chart.symm y ∈ (univ : Set E3)) ↔ y ∈ A.chart.target
    simp only [mem_univ, and_true]
  have hN0target : N0.chart.target = N.chart.target := by
    ext y
    change (y ∈ N.chart.target ∧ N.chart.symm y ∈ (univ : Set E3)) ↔ y ∈ N.chart.target
    simp only [mem_univ, and_true]
  have hA0inside : A0.inside = A.inside := A.normReparametrize_inside G0.symm hG0i
  have hA0closed : A0.closedRegion = A.closedRegion :=
    A.normReparametrize_closedRegion G0.symm hG0i
  have hA0boundary : A0.boundary = A.boundary :=
    A.normReparametrize_boundary G0.symm hG0i
  have hN0inside : N0.inside = N.inside := N.normReparametrize_inside G1.symm hG1i
  have hN0closed : N0.closedRegion = N.closedRegion :=
    N.normReparametrize_closedRegion G1.symm hG1i
  have hN0boundary : N0.boundary = N.boundary :=
    N.normReparametrize_boundary G1.symm hG1i
  have hmatch (X : E2) (hX : X ∈ e.source) :
      A.chart (e X : E3) = N.chart (northSpherePoint X : E3) := by
    have hx : ‖X‖ < R := mem_ball_zero_iff.mp (hesource ▸ hX)
    have hden : 0 < 1 - o := sub_pos.mpr ho1
    have hRsq : R ^ 2 = (1 + o) / (1 - o) := Real.sq_sqrt (by positivity)
    have hRpos : 0 < R := lt_trans zero_lt_one hR
    have hxs : ‖X‖ ^ 2 < (1 + o) / (1 - o) := by
      rw [← hRsq]
      nlinarith [norm_nonneg X]
    have hcross := (lt_div_iff₀ hden).mp hxs
    have hheight : -o < (heightCoordinates (northSpherePoint X : E3)).2 := by
      rw [northSpherePoint_coordinates]
      change -o < (1 - ‖X‖ ^ 2) / (1 + ‖X‖ ^ 2)
      apply (lt_div_iff₀ (by positivity : 0 < 1 + ‖X‖ ^ 2)).mpr
      nlinarith
    have ht : N.chart (northSpherePoint X : E3) ∈ A.chart.target := by
      obtain ⟨y, hy, heq⟩ := hpatch (northSpherePoint X) hheight
      rw [← heq]
      exact A.chart.map_source (A.closedBall_subset_source (sphere_subset_closedBall hy))
    rw [hepoint X hX]
    exact A.chart.right_inv ht
  have hparameter (X : E2) (hX : ‖X‖ ≤ r) :
      A0.chart (P X : E3) = N0.chart (P X : E3) := by
    have hx0 : ‖X‖ ≤ r0 := hX.trans hrr0
    have hx1 : ‖X‖ ≤ r1 := hX.trans hrr1
    have hXe : X ∈ e.source := (hdomains0 (mem_closedBall_zero_iff.mpr hx0)).2
    have hg1 : G1 (P X : E3) = (northSpherePoint X : E3) := hpoint1 X hx1
    rw [hA0point, hN0point, hpoint0 X hx0, hg1]
    exact hmatch X hXe
  have hDaP : ((↑) : UnitTwoSphere → E3) '' (P '' closedBall (0 : E2) 1) = Da := by
    rw [hPcap]
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨norm_eq_of_mem_sphere q, hq⟩
    · intro hy
      exact ⟨⟨y, mem_sphere_zero_iff_norm.mpr hy.1⟩, hy.2, rfl⟩
  have hA0cap : A0.chart '' Da = Delta := by
    have heq : A0.chart '' Da =
        A.chart '' (((↑) : UnitTwoSphere → E3) '' (e '' closedBall (0 : E2) 1)) := by
      rw [← hDaP]
      simp only [image_image]
      apply image_congr
      intro X hX
      change A.chart (G0 (P X : E3)) = A.chart (e X : E3)
      rw [hpoint0 X ((mem_closedBall_zero_iff.mp hX).trans hr0.le)]
    exact heq.trans hecap
  have hnorthimage : ((↑) : UnitTwoSphere → E3) ''
      (northSpherePoint '' closedBall (0 : E2) 1) =
        {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    rw [northSpherePoint_image_closedBall]
    ext y
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨norm_eq_of_mem_sphere q, hq⟩
    · intro hy
      exact ⟨⟨y, mem_sphere_zero_iff_norm.mpr hy.1⟩, hy.2, rfl⟩
  have hN0cap : N0.chart '' Da = Delta := by
    change N0.chart '' Da = N.chart '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
    rw [← hDaP, ← hnorthimage]
    simp only [image_image]
    apply image_congr
    intro X hX
    change N.chart (G1 (P X : E3)) = N.chart (northSpherePoint X : E3)
    have hh : G1 (P X : E3) = (northSpherePoint X : E3) :=
      hpoint1 X ((mem_closedBall_zero_iff.mp hX).trans hr1.le)
    rw [hh]
  have hSopen : IsOpen (P '' ball (0 : E2) r) :=
    P.isOpen_image_of_subset_source isOpen_ball (by rw [hPs]; exact subset_univ _)
  obtain ⟨U, hU, hUS⟩ :=
    (isOpen_induced_iff (f := ((↑) : UnitTwoSphere → E3))).mp hSopen
  have hDaU : Da ⊆ U := by
    intro y hy
    have hyP : y ∈ ((↑) : UnitTwoSphere → E3) '' (P '' closedBall (0 : E2) 1) :=
      hDaP.symm ▸ hy
    obtain ⟨q, ⟨X, hX, rfl⟩, rfl⟩ := hyP
    have hPX : P X ∈ P '' ball (0 : E2) r :=
      ⟨X, mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hX).trans_lt hr), rfl⟩
    have hh : P X ∈ ((↑) : UnitTwoSphere → E3) ⁻¹' U := hUS.symm ▸ hPX
    exact hh
  have hUmatch (y : E3) (hy : y ∈ U) (hyn : ‖y‖ = 1) :
      A0.chart y = N0.chart y := by
    let q : UnitTwoSphere := ⟨y, mem_sphere_zero_iff_norm.mpr hyn⟩
    have hq : q ∈ P '' ball (0 : E2) r := by
      rw [← hUS]
      exact hy
    obtain ⟨X, hX, hXq⟩ := hq
    change A0.chart (q : E3) = N0.chart (q : E3)
    rw [← hXq]
    exact hparameter X (mem_ball_zero_iff.mp hX).le
  have hDaEq : Da = sphere (0 : E3) 1 ∩
      {y : E3 | (3 / 4 : ℝ) ≤ (heightCoordinates y).2} := by
    ext y
    simp only [Da, mem_inter_iff, mem_ofPred_eq, mem_sphere_zero_iff_norm]
  have hDa : IsCompact Da := by
    rw [hDaEq]
    exact (isCompact_sphere (0 : E3) 1).inter_right
      (isClosed_le continuous_const heightCoordinates.continuous.snd)
  have hDaSphere : Da ⊆ sphere (0 : E3) 1 :=
    fun y hy => mem_sphere_zero_iff_norm.mpr hy.1
  have hcontain0 : N0.closedRegion ⊆ A0.closedRegion := by
    rw [hN0closed, hA0closed]
    exact hcontain
  obtain ⟨F, hFfixed, hFball, hFclosed, hFnear, Ahat,
      hAchart, hAsource0, hAtarget0, hApoint0, hAinv0,
      hAinside0, hAclosed0, hAboundary0, hAsphere, hnear⟩ :=
    exists_ball_chart_common_germ_of_sphere_patch A0 N0 hDa hDaSphere
      hU hDaU hUmatch hcontain0
  have hApoint (y : E3) : Ahat.chart y = A.chart (G0 (F y)) :=
    (hApoint0 y).trans (hA0point (F y))
  have hAinv (y : E3) : Ahat.chart.symm y = F.symm (G0.symm (A.chart.symm y)) :=
    (hAinv0 y).trans (congrArg F.symm (hA0inv y))
  have hAsource : Ahat.chart.source = {y : E3 | G0 (F y) ∈ A.chart.source} := by
    change Ahat.chart.source = F ⁻¹' (G0 ⁻¹' A.chart.source)
    rw [hAsource0, hA0source]
  have hAchartFinal : Ahat.chart =
      (F.trans G0).toHomeomorph.toOpenPartialHomeomorph.trans A.chart := by
    apply OpenPartialHomeomorph.ext
    · intro y
      change Ahat.chart y = A.chart (G0 (F y))
      exact hApoint y
    · intro y
      change Ahat.chart.symm y = F.symm (G0.symm (A.chart.symm y))
      exact hAinv y
    · rw [hAsource]
      ext y
      change (G0 (F y) ∈ A.chart.source) ↔
        (y ∈ (univ : Set E3) ∧ G0 (F y) ∈ A.chart.source)
      simp only [mem_univ, true_and]
  have hAcap : Ahat.chart '' Da = Delta := by
    calc
      Ahat.chart '' Da = A0.chart '' Da :=
        image_congr (fun y hy => hAsphere y (hDaSphere hy))
      _ = Delta := hA0cap
  obtain ⟨V, hV, hDaV, hVall⟩ := mem_nhdsSet_iff_exists.mp hnear
  refine ⟨G0, G1, F, Ahat, N0, V, fun y => ⟨hG0 y, hG1 y⟩,
    hFfixed, hFball, hFclosed, hAchartFinal, rfl, hAsource, hN0source,
    hAtarget0.trans hA0target, hN0target, fun y => ⟨hApoint y, hN0point y⟩,
    fun y => ⟨hAinv y, hN0inv y⟩,
    hAinside0.trans hA0inside, hAclosed0.trans hA0closed,
    hAboundary0.trans hA0boundary, hN0inside, hN0closed, hN0boundary,
    hAcap, hN0cap, hV, hDaV, ?_, ?_⟩
  · intro y hy
    exact ⟨(hVall hy).1, (hVall hy).2.1⟩
  · intro y hy
    exact (hVall hy).2.2

end PoincareConjecture.M25.Topology3D
