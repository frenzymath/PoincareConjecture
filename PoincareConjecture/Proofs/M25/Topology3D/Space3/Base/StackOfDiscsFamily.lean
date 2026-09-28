import PoincareConjecture.Proofs.M25.Topology3D.Space3.CompactSmoothChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallRegionUniqueness
import PoincareConjecture.Proofs.M25.Topology3D.Space3.HeightPlaneProjection
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

namespace PlanarSchoenfliesFamilyData

variable {c : ℝ → UnitCircle → E2} {a b : ℝ}

def graph (D : PlanarSchoenfliesFamilyData c a b) (p : ℝ × E2) : ℝ × E2 :=
  (p.1, D.chart p.1 p.2)

theorem graph_contDiffOn (D : PlanarSchoenfliesFamilyData c a b) :
    ContDiffOn ℝ ∞ D.graph
      (Ioo (a - D.margin) (b + D.margin) ×ˢ ball 0 D.radius) :=
  contDiff_fst.contDiffOn.prodMk D.chart_smooth

theorem graph_invertible_derivative (D : PlanarSchoenfliesFamilyData c a b)
    {z : ℝ} (hz : z ∈ Icc a b) {x : E2} (hx : x ∈ ball 0 D.radius) :
    ∃ A : (ℝ × E2) ≃L[ℝ] (ℝ × E2),
      HasFDerivAt D.graph (A : (ℝ × E2) →L[ℝ] (ℝ × E2)) (z, x) := by
  have hzU : z ∈ Ioo (a - D.margin) (b + D.margin) := by
    constructor <;> linarith [hz.1, hz.2, D.margin_pos]
  let f : (ℝ × E2) → E2 := fun p => D.chart p.1 p.2
  let L := fderiv ℝ f (z, x)
  have hopen : IsOpen (Ioo (a - D.margin) (b + D.margin) ×ˢ
      ball (0 : E2) D.radius) := isOpen_Ioo.prod isOpen_ball
  have hcont : ContDiffAt ℝ ∞ f (z, x) :=
    D.chart_smooth.contDiffAt (hopen.mem_nhds ⟨hzU, hx⟩)
  have hf : HasFDerivAt f L (z, x) :=
    (hcont.differentiableAt (by simp)).hasFDerivAt
  let A := (ContinuousLinearMap.fst ℝ ℝ E2).prod L
  have hF : HasFDerivAt D.graph A (z, x) := hasFDerivAt_fst.prodMk hf
  have hspatial : HasFDerivAt (D.chart z)
      (L.comp (ContinuousLinearMap.inr ℝ ℝ E2)) x :=
    hf.comp x (hasFDerivAt_prodMk_right z x)
  have hi : Injective A := by
    apply (injective_iff_map_eq_zero A).mpr
    intro v hv
    have hv1 : v.1 = 0 := by
      exact congrArg Prod.fst hv
    have hzero : fderiv ℝ (D.chart z) x v.2 = 0 := by
      rw [hspatial.fderiv]
      change L (0, v.2) = 0
      rw [← hv1]
      exact congrArg Prod.snd hv
    have hv2 : v.2 = 0 := D.chart_immersion z hz x hx
      (hzero.trans (map_zero _).symm)
    exact Prod.ext hv1 hv2
  have hunit : IsUnit A := ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hi, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := A.toLinearMap) rfl).mp hi⟩
  obtain ⟨B, hB⟩ := hunit
  refine ⟨ContinuousLinearEquiv.ofUnit B, ?_⟩
  change HasFDerivAt D.graph (B : (ℝ × E2) →L[ℝ] (ℝ × E2)) (z, x)
  rw [hB]
  exact hF

theorem exists_graphChart_near_compact (D : PlanarSchoenfliesFamilyData c a b)
    {R : ℝ} (hR : R < D.radius) :
    ∃ e : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2),
      (e : (ℝ × E2) → ℝ × E2) = D.graph ∧
      Icc a b ×ˢ closedBall 0 R ⊆ e.source ∧
      e.source ⊆ Ioo (a - D.margin) (b + D.margin) ×ˢ ball 0 D.radius ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  have hball : closedBall (0 : E2) R ⊆ ball 0 D.radius := by
    intro x hx
    exact mem_ball_zero_iff.mpr ((mem_closedBall_zero_iff.mp hx).trans_lt hR)
  have hKU : Icc a b ×ˢ closedBall (0 : E2) R ⊆
      Ioo (a - D.margin) (b + D.margin) ×ˢ ball 0 D.radius := by
    intro p hp
    refine ⟨?_, hball hp.2⟩
    constructor <;> linarith [hp.1.1, hp.1.2, D.margin_pos]
  apply exists_smoothChart_near_compact D.graph
    (isCompact_Icc.prod (isCompact_closedBall _ _))
    (isOpen_Ioo.prod isOpen_ball) hKU D.graph_contDiffOn
  · intro p hp q hq hpq
    have hz := congrArg Prod.fst hpq
    change p.1 = q.1 at hz
    apply Prod.ext hz
    have hxy := congrArg Prod.snd hpq
    change D.chart p.1 p.2 = D.chart q.1 q.2 at hxy
    rw [← hz] at hxy
    exact D.chart_injOn p.1 hp.1 (hball hp.2) (hball hq.2) hxy
  · intro p hp
    exact D.graph_invertible_derivative hp.1 (hball hp.2)

end PlanarSchoenfliesFamilyData

structure PlanarFamilyGraphChart {c : ℝ → UnitCircle → E2} {a b : ℝ}
    (D : PlanarSchoenfliesFamilyData c a b) where
  margin : ℝ
  margin_pos : 0 < margin
  radius : ℝ
  one_lt_radius : 1 < radius
  radius_lt : radius < D.radius
  chart : OpenPartialHomeomorph (ℝ × E2) (ℝ × E2)
  chart_eq : (chart : (ℝ × E2) → ℝ × E2) = D.graph
  source_eq : chart.source = Ioo (a - margin) (b + margin) ×ˢ ball 0 radius
  smooth : ContDiffOn ℝ ∞ chart chart.source
  smooth_symm : ContDiffOn ℝ ∞ chart.symm chart.target

namespace PlanarSchoenfliesFamilyData

variable {c : ℝ → UnitCircle → E2} {a b : ℝ}

theorem nonempty_graphChart (D : PlanarSchoenfliesFamilyData c a b) (hab : a < b) :
    Nonempty (PlanarFamilyGraphChart D) := by
  let R := (1 + D.radius) / 2
  have hR1 : 1 < R := by dsimp [R]; linarith [D.one_lt_radius]
  have hRD : R < D.radius := by dsimp [R]; linarith [D.one_lt_radius]
  obtain ⟨e, he, hKe, _, hes, hei⟩ := D.exists_graphChart_near_compact hRD
  have hK : IsCompact (Icc a b ×ˢ closedBall (0 : E2) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨d, hd, hde⟩ := hK.exists_thickening_subset_open e.open_source hKe
  let r := (1 + R) / 2
  have hr1 : 1 < r := by dsimp [r]; linarith
  have hrR : r < R := by dsimp [r]; linarith
  let V := Ioo (a - d / 2) (b + d / 2) ×ˢ ball (0 : E2) r
  have hVe : V ⊆ e.source := by
    rintro ⟨z, x⟩ ⟨hz, hx⟩
    have hxR : x ∈ closedBall (0 : E2) R :=
      mem_closedBall_zero_iff.mpr ((mem_ball_zero_iff.mp hx).trans hrR).le
    apply hde
    apply mem_thickening_iff.mpr
    by_cases hza : z < a
    · refine ⟨(a, x), ⟨⟨le_rfl, hab.le⟩, hxR⟩, ?_⟩
      rw [dist_prod_same_right, Real.dist_eq, abs_of_neg (sub_neg.mpr hza)]
      linarith [hz.1]
    · by_cases hbz : b < z
      · refine ⟨(b, x), ⟨⟨hab.le, le_rfl⟩, hxR⟩, ?_⟩
        rw [dist_prod_same_right, Real.dist_eq, abs_of_pos (sub_pos.mpr hbz)]
        linarith [hz.2]
      · exact ⟨(z, x), ⟨⟨le_of_not_gt hza, le_of_not_gt hbz⟩, hxR⟩,
          by simpa only [dist_self] using hd⟩
  have hV : IsOpen V := isOpen_Ioo.prod isOpen_ball
  refine ⟨{
    margin := d / 2
    margin_pos := by positivity
    radius := r
    one_lt_radius := hr1
    radius_lt := hrR.trans hRD
    chart := e.restrOpen V hV
    chart_eq := he
    source_eq := ?_
    smooth := hes.mono inter_subset_left
    smooth_symm := hei.mono inter_subset_left
  }⟩
  exact inter_eq_right.mpr hVe

end PlanarSchoenfliesFamilyData

namespace PlanarFamilyGraphChart

variable {c : ℝ → UnitCircle → E2} {a b : ℝ}
variable {D : PlanarSchoenfliesFamilyData c a b} (G : PlanarFamilyGraphChart D)

@[simp] theorem chart_apply (p : ℝ × E2) :
    G.chart p = (p.1, D.chart p.1 p.2) := congrFun G.chart_eq p

theorem height_mem_interval {z : ℝ} (hz : z ∈ Icc a b) :
    z ∈ Ioo (a - G.margin) (b + G.margin) := by
  constructor <;> linarith [hz.1, hz.2, G.margin_pos]

theorem mem_source {z : ℝ} (hz : z ∈ Icc a b) {x : E2}
    (hx : x ∈ ball 0 G.radius) : (z, x) ∈ G.chart.source := by
  rw [G.source_eq]
  exact ⟨G.height_mem_interval hz, hx⟩

theorem inverse_fst {p : ℝ × E2} (hp : p ∈ G.chart.target) :
    (G.chart.symm p).1 = p.1 := by
  have h := congrArg Prod.fst (G.chart.right_inv hp)
  simpa only [G.chart_apply] using h

theorem fiber_contDiffOn {z : ℝ} (hz : z ∈ Icc a b) :
    ContDiffOn ℝ ∞ (D.chart z) (ball 0 G.radius) := by
  have h := (G.smooth.comp (contDiff_prodMk_right z).contDiffOn
    (fun _ hx => G.mem_source hz hx)).snd
  simpa only [Function.comp_def, G.chart_apply] using h

theorem fiberInverse_contDiffOn (z : ℝ) :
    ContDiffOn ℝ ∞ (fun y => (G.chart.symm (z, y)).2)
      ((fun y => (z, y)) ⁻¹' G.chart.target) :=
  (G.smooth_symm.comp (contDiff_prodMk_right z).contDiffOn (fun _ hy => hy)).snd

def fiberChart (z : ℝ) (hz : z ∈ Icc a b) : OpenPartialHomeomorph E2 E2 where
  toFun := D.chart z
  invFun := fun y => (G.chart.symm (z, y)).2
  source := ball 0 G.radius
  target := (fun y => (z, y)) ⁻¹' G.chart.target
  map_source' x hx := by
    change (z, D.chart z x) ∈ G.chart.target
    simpa only [G.chart_apply] using G.chart.map_source (G.mem_source hz hx)
  map_target' y hy := by
    have h := G.chart.map_target hy
    rw [G.source_eq] at h
    exact h.2
  left_inv' x hx := by
    have h := congrArg Prod.snd (G.chart.left_inv (G.mem_source hz hx))
    simpa only [G.chart_apply] using h
  right_inv' y hy := by
    have h := congrArg Prod.snd (G.chart.right_inv hy)
    simpa only [G.chart_apply, G.inverse_fst hy] using h
  open_source := isOpen_ball
  open_target := G.chart.open_target.preimage (continuous_const.prodMk continuous_id)
  continuousOn_toFun := (G.fiber_contDiffOn hz).continuousOn
  continuousOn_invFun := (G.fiberInverse_contDiffOn z).continuousOn

@[simp] theorem fiberChart_apply (z : ℝ) (hz : z ∈ Icc a b) (x : E2) :
    G.fiberChart z hz x = D.chart z x := rfl

@[simp] theorem fiberChart_symm_apply (z : ℝ) (hz : z ∈ Icc a b) (y : E2) :
    (G.fiberChart z hz).symm y = (G.chart.symm (z, y)).2 := rfl

@[simp] theorem fiberChart_source (z : ℝ) (hz : z ∈ Icc a b) :
    (G.fiberChart z hz).source = ball 0 G.radius := rfl

@[simp] theorem fiberChart_target (z : ℝ) (hz : z ∈ Icc a b) :
    (G.fiberChart z hz).target = (fun y => (z, y)) ⁻¹' G.chart.target := rfl

def fiberBallNeighborhood (z : ℝ) (hz : z ∈ Icc a b) : BallNeighborhoodChart E2 E2 where
  chart := G.fiberChart z hz
  closedBall_subset_source := closedBall_subset_ball G.one_lt_radius
  smooth := G.fiber_contDiffOn hz
  smooth_symm := G.fiberInverse_contDiffOn z

theorem fiberChart_boundary (z : ℝ) (hz : z ∈ Icc a b) (q : UnitCircle) :
    G.fiberChart z hz q.1 = c z q := D.chart_boundary z hz q

theorem fiberBallNeighborhood_boundary (z : ℝ) (hz : z ∈ Icc a b) :
    (G.fiberBallNeighborhood z hz).boundary = range (c z) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (D.chart_boundary z hz ⟨x, hx⟩).symm⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q.1, q.2, D.chart_boundary z hz q⟩

theorem fiber_inside_eq (z : ℝ) (hz : z ∈ Icc a b)
    (B : BallNeighborhoodChart E2 E2) (hB : B.boundary = range (c z)) :
    (G.fiberBallNeighborhood z hz).inside = B.inside :=
  (G.fiberBallNeighborhood z hz).inside_eq_of_boundary_eq B
    (Module.one_lt_rank_of_one_lt_finrank (by simp [E2]))
    ((G.fiberBallNeighborhood_boundary z hz).trans hB.symm)

theorem fiber_closedRegion_eq (z : ℝ) (hz : z ∈ Icc a b)
    (B : BallNeighborhoodChart E2 E2) (hB : B.boundary = range (c z)) :
    (G.fiberBallNeighborhood z hz).closedRegion = B.closedRegion :=
  (G.fiberBallNeighborhood z hz).closedRegion_eq_of_boundary_eq B
    (Module.one_lt_rank_of_one_lt_finrank (by simp [E2]))
    ((G.fiberBallNeighborhood_boundary z hz).trans hB.symm)

noncomputable def ambientChart (u : UnitTwoSphere) : OpenPartialHomeomorph (E2 × ℝ) E3 :=
  let P := ContinuousLinearEquiv.prodComm ℝ E2 ℝ
  let Q := (ContinuousLinearEquiv.prodComm ℝ ℝ E2).trans (heightPlaneCoordinates u).symm
  (P.toHomeomorph.transOpenPartialHomeomorph G.chart).transHomeomorph Q.toHomeomorph

@[simp] theorem ambientChart_apply (u : UnitTwoSphere) (p : E2 × ℝ) :
    G.ambientChart u p = (heightPlaneCoordinates u).symm (D.chart p.2 p.1, p.2) := by
  change (heightPlaneCoordinates u).symm ((G.chart (p.2, p.1)).2,
    (G.chart (p.2, p.1)).1) = _
  rw [G.chart_apply]

theorem ambientChart_source (u : UnitTwoSphere) :
    (G.ambientChart u).source = ball 0 G.radius ×ˢ Ioo (a - G.margin) (b + G.margin) := by
  ext p
  change (p.2, p.1) ∈ G.chart.source ↔ _
  rw [G.source_eq]
  exact and_comm

theorem closedDiscStack_subset_source (u : UnitTwoSphere) :
    closedBall 0 1 ×ˢ Icc a b ⊆ (G.ambientChart u).source := by
  intro p hp
  rw [G.ambientChart_source]
  exact ⟨closedBall_subset_ball G.one_lt_radius hp.1, G.height_mem_interval hp.2⟩

theorem ambientChart_contDiffOn (u : UnitTwoSphere) :
    ContDiffOn ℝ ∞ (G.ambientChart u) (G.ambientChart u).source := by
  let P := ContinuousLinearEquiv.prodComm ℝ E2 ℝ
  let Q := (ContinuousLinearEquiv.prodComm ℝ ℝ E2).trans (heightPlaneCoordinates u).symm
  exact Q.contDiff.comp_contDiffOn
    (G.smooth.comp P.contDiff.contDiffOn (fun _ hp => hp))

theorem ambientChart_symm_contDiffOn (u : UnitTwoSphere) :
    ContDiffOn ℝ ∞ (G.ambientChart u).symm (G.ambientChart u).target := by
  let P := ContinuousLinearEquiv.prodComm ℝ E2 ℝ
  let Q := (ContinuousLinearEquiv.prodComm ℝ ℝ E2).trans (heightPlaneCoordinates u).symm
  exact P.symm.contDiff.comp_contDiffOn
    (G.smooth_symm.comp Q.symm.contDiff.contDiffOn (fun _ hp => hp))

theorem ambientChart_height (u : UnitTwoSphere) (p : E2 × ℝ) :
    ⟪(u : E3), G.ambientChart u p⟫_ℝ = p.2 := by
  rw [G.ambientChart_apply, ← heightPlaneCoordinates_snd u,
    ContinuousLinearEquiv.apply_symm_apply]

theorem ambientChart_inverse_height (u : UnitTwoSphere) {y : E3}
    (hy : y ∈ (G.ambientChart u).target) :
    ((G.ambientChart u).symm y).2 = ⟪(u : E3), y⟫_ℝ := by
  change (G.chart.symm ((heightPlaneCoordinates u y).2,
    (heightPlaneCoordinates u y).1)).1 = _
  change ((heightPlaneCoordinates u y).2, (heightPlaneCoordinates u y).1) ∈
    G.chart.target at hy
  rw [G.inverse_fst hy, heightPlaneCoordinates_snd]

theorem ambientChart_boundary (u : UnitTwoSphere) (z : ℝ) (hz : z ∈ Icc a b)
    (q : UnitCircle) :
    G.ambientChart u (q.1, z) = (heightPlaneCoordinates u).symm (c z q, z) := by
  rw [G.ambientChart_apply, D.chart_boundary z hz q]

end PlanarFamilyGraphChart

end PoincareConjecture.M25.Topology3D
