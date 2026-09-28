import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.BallTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsFamily
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhoodNesting
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceUpperTube
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.Nested.ReferenceHighRegularity
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedReferenceCollar
import PoincareConjecture.Proofs.M25.Topology3D.Space3.RegularHorizontalTransport
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.HyperbolaDiscArcs
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.NativeLevelGeometry

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold Topology InnerProductSpace Matrix

namespace PoincareConjecture.M25.Topology3D

private theorem saddle_nested_selected_comparison_fillings
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (u : UnitTwoSphere)
    (D : SaddlePieceData psi u) (W : SaddleLowerLevelData D)
    (i o : Fin 2) (hio : i ≠ o)
    (hnested : (W.disc i).closedRegion ⊆ (W.disc o).inside)
    (T : Diffeomorph 𝓘(ℝ, E2) 𝓘(ℝ, E2) E2 E2 ∞)
    (C : ℝ → Fin 2 → UnitCircle → E2)
    (hC : ∀ k : Fin 2,
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
        (fun p : ℝ × UnitCircle => C p.1 k p.2))
    (hEmbedding : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k : Fin 2,
      IsPlanarEmbedding (C t k))
    (hDisjoint : ∀ t ∈ Icc (0 : ℝ) 1, ∀ k l : Fin 2, k ≠ l →
      Disjoint (range (C t k)) (range (C t l)))
    (hStart : ∀ (k : Fin 2) (theta : UnitCircle),
      C 0 k theta = T ((heightPlaneCoordinates u
        (psi (W.leg k (theta, W.level), 0))).1)) :
    ∃ (P : (k : Fin 2) → PlanarSchoenfliesFamilyData (fun t => C t k) 0 1)
      (G : (k : Fin 2) → PlanarFamilyGraphChart (P k)),
      (∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (k : Fin 2),
        ((G k).fiberBallNeighborhood t ht).boundary = range (C t k)) ∧
      (∀ k : Fin 2,
        ((G k).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).inside =
          T '' (W.disc k).inside ∧
        ((G k).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).closedRegion =
          T '' (W.disc k).closedRegion) ∧
      (∀ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
        ((G i).fiberBallNeighborhood t ht).closedRegion ⊆
          ((G o).fiberBallNeighborhood t ht).inside) := by
  classical
  have hfamily (i : Fin 2) :
      Nonempty (PlanarSchoenfliesFamilyData (fun t => C t i) 0 1) :=
    hP.2 0 1 (fun t => C t i) zero_lt_one (hC i)
      (fun t ht => hEmbedding t ht i)
  let P : (i : Fin 2) → PlanarSchoenfliesFamilyData (fun t => C t i) 0 1 :=
    fun i => Classical.choice (hfamily i)
  let G : (i : Fin 2) → PlanarFamilyGraphChart (P i) :=
    fun i => Classical.choice ((P i).nonempty_graphChart zero_lt_one)
  have hproject (x : E2) :
      (heightPlaneCoordinates u ((heightPlaneCoordinates u).symm (x, W.level))).1 = x := by
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have hboundary (i : Fin 2) :
      ((W.disc i).mapDiffeomorph T).boundary = range (C 0 i) := by
    rw [BallNeighborhoodChart.mapDiffeomorph_boundary]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxlevel : (heightPlaneCoordinates u).symm (x, W.level) ∈
          range (fun theta => psi (W.leg i (theta, W.level), 0)) := by
        rw [← W.disc_boundary i]
        exact ⟨x, hx, rfl⟩
      obtain ⟨theta, htheta⟩ := hxlevel
      dsimp only at htheta
      refine ⟨theta, ?_⟩
      rw [hStart, htheta, hproject]
    · rintro ⟨theta, rfl⟩
      have hlevel : psi (W.leg i (theta, W.level), 0) ∈
          (fun x => (heightPlaneCoordinates u).symm (x, W.level)) ''
            (W.disc i).boundary := by
        rw [W.disc_boundary i]
        exact mem_range_self theta
      obtain ⟨x, hx, hxtheta⟩ := hlevel
      refine ⟨x, hx, ?_⟩
      rw [hStart, ← hxtheta, hproject]
  have hInitial (i : Fin 2) :
      ((G i).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).inside =
        T '' (W.disc i).inside ∧
      ((G i).fiberBallNeighborhood 0 ⟨le_rfl, zero_le_one⟩).closedRegion =
        T '' (W.disc i).closedRegion := by
    constructor
    · exact ((G i).fiber_inside_eq 0 ⟨le_rfl, zero_le_one⟩
        ((W.disc i).mapDiffeomorph T) (hboundary i)).trans
          ((W.disc i).mapDiffeomorph_inside T)
    · exact ((G i).fiber_closedRegion_eq 0 ⟨le_rfl, zero_le_one⟩
        ((W.disc i).mapDiffeomorph T) (hboundary i)).trans
          ((W.disc i).mapDiffeomorph_closedRegion T)
  let I := {t : ℝ // t ∈ Icc (0 : ℝ) 1}
  let K := {x : E2 // x ∈ closedBall (0 : E2) 1}
  let : ConnectedSpace I := isConnected_iff_connectedSpace.mp (isConnected_Icc zero_le_one)
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E2) 1)
  let B : Fin 2 → I → BallNeighborhoodChart E2 E2 :=
    fun k t => (G k).fiberBallNeighborhood (t : ℝ) t.property
  have hdim : 1 < Module.rank ℝ E2 := by
    rw [← Module.finrank_eq_rank]
    norm_num [E2]
  obtain ⟨x0, hx0⟩ :=
    (isConnected_sphere hdim (0 : E2) (by norm_num : (0 : ℝ) ≤ 1)).nonempty
  let x0K : K := ⟨x0, sphere_subset_closedBall hx0⟩
  have hFamily (k : Fin 2) :
      Continuous (fun p : I × K => (P k).chart (p.1 : ℝ) (p.2 : E2)) := by
    have harg : Continuous (fun p : I × K => ((p.1 : ℝ), (p.2 : E2))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    have hc := (G k).chart.continuousOn.comp_continuous harg (fun p =>
      (G k).mem_source p.1.property
        ((closedBall_subset_ball (G k).one_lt_radius) p.2.property))
    simpa only [Function.comp_def, (G k).chart_apply] using hc.snd
  let w : I → E2 := fun t => (P i).chart (t : ℝ) x0
  have hw : Continuous w :=
    (hFamily i).comp (continuous_id.prodMk (continuous_const (y := x0K)))
  have hwBoundary (t : I) : w t ∈ (B i t).boundary := ⟨x0, hx0, rfl⟩
  have hBoundary (t : I) : Disjoint (B i t).boundary (B o t).boundary := by
    simpa only [B, PlanarFamilyGraphChart.fiberBallNeighborhood_boundary] using
      hDisjoint (t : ℝ) t.property i o hio
  have hwNotBoundary (t : I) : w t ∉ (B o t).boundary :=
    disjoint_left.mp (hBoundary t) (hwBoundary t)
  let Good : Set I := {t | w t ∈ (B o t).inside}
  let Z : Set (I × K) := {p | w p.1 = (P o).chart (p.1 : ℝ) (p.2 : E2)}
  have hZ : IsClosed Z := isClosed_eq (hw.comp continuous_fst) (hFamily o)
  have hGoodEq : Good = Prod.fst '' Z := by
    ext t
    constructor
    · rintro ⟨x, hx, hxt⟩
      exact ⟨(t, ⟨x, ball_subset_closedBall hx⟩), hxt.symm, rfl⟩
    · rintro ⟨⟨s, x⟩, hs, hst⟩
      change s = t at hst
      subst s
      have heq : w t = (P o).chart (t : ℝ) (x : E2) := hs
      have hclosed : w t ∈ (B o t).closedRegion := ⟨x, x.property, heq.symm⟩
      rw [← (B o t).inside_union_boundary] at hclosed
      exact hclosed.elim id (fun h => False.elim (hwNotBoundary t h))
  have hGoodClosed : IsClosed Good := by
    rw [hGoodEq]
    exact isClosedMap_fst_of_compactSpace Z hZ
  have hGoodOpen : IsOpen Good := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨x, hx, hxt⟩ := ht
    have hs : ((t : ℝ), x) ∈ (G o).chart.source :=
      (G o).mem_source t.property (ball_subset_ball (G o).one_lt_radius.le hx)
    let Q : I → ℝ × E2 := fun s => ((s : ℝ), w s)
    have hQ : Continuous Q := continuous_subtype_val.prodMk hw
    have hQt : Q t = (G o).chart ((t : ℝ), x) := by
      rw [(G o).chart_apply]
      exact Prod.ext rfl hxt.symm
    have htTarget : Q t ∈ (G o).chart.target := by
      rw [hQt]
      exact (G o).chart.map_source hs
    let y : I → E2 := fun s => ((G o).chart.symm (Q s)).2
    have hy : ContinuousAt y t :=
      (((G o).smooth_symm.continuousOn.continuousAt
        ((G o).chart.open_target.mem_nhds htTarget)).comp hQ.continuousAt).snd
    have hyt : y t = x := by
      change ((G o).chart.symm (Q t)).2 = x
      rw [hQt, (G o).chart.left_inv hs]
    have hTarget : ∀ᶠ s : I in 𝓝 t, Q s ∈ (G o).chart.target :=
      hQ.continuousAt.eventually_mem ((G o).chart.open_target.mem_nhds htTarget)
    have hBall : ∀ᶠ s : I in 𝓝 t, y s ∈ ball (0 : E2) 1 :=
      hy.eventually_mem (isOpen_ball.mem_nhds (by rw [hyt]; exact hx))
    filter_upwards [hTarget, hBall] with s hsTarget hsBall
    have hright : (P o).chart (s : ℝ) (y s) = w s := by
      have hh := congrArg Prod.snd ((G o).chart.right_inv hsTarget)
      simpa only [(G o).chart_apply, (G o).inverse_fst hsTarget] using hh
    exact ⟨y s, hsBall, hright⟩
  let t0 : I := ⟨0, le_rfl, zero_le_one⟩
  have hstart : (B i t0).closedRegion ⊆ (B o t0).inside := by
    change ((G i).fiberBallNeighborhood 0 _).closedRegion ⊆
      ((G o).fiberBallNeighborhood 0 _).inside
    rw [(hInitial i).2, (hInitial o).1]
    exact image_mono hnested
  have hGoodAll : Good = univ :=
    (show IsClopen Good from ⟨hGoodClosed, hGoodOpen⟩).eq_univ
      ⟨t0, hstart (image_mono sphere_subset_closedBall (hwBoundary t0))⟩
  refine ⟨P, G, (fun t ht k => (G k).fiberBallNeighborhood_boundary t ht), hInitial, ?_⟩
  intro t ht
  let tt : I := ⟨t, ht⟩
  have hwInside : w tt ∈ (B o tt).inside := by
    have hmem : tt ∈ Good := by rw [hGoodAll]; exact mem_univ _
    exact hmem
  have hsub : (B i tt).boundary ⊆ (B o tt).inside := by
    rcases (B o tt).preconnected_subset_inside_or_outside
        ((B i tt).boundary_connected hdim).isPreconnected (hBoundary tt) with hin | hout
    · exact hin
    · exact False.elim (hout (hwBoundary tt) (image_mono ball_subset_closedBall hwInside))
  exact (B o tt).closedRegion_subset_inside_of_boundary_subset (B i tt)
    ((B o tt).boundary_connected hdim).isPreconnected
    ((B i tt).boundary_connected hdim) (hBoundary tt).symm hsub

end PoincareConjecture.M25.Topology3D
