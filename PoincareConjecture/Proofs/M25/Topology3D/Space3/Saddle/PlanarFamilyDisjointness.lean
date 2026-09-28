import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsFamily
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

theorem saddle_planar_family_closedRegion_disjoint
    {c0 c1 : ℝ → UnitCircle → E2} {a b : ℝ}
    (D0 : PlanarSchoenfliesFamilyData c0 a b)
    (D1 : PlanarSchoenfliesFamilyData c1 a b)
    (G0 : PlanarFamilyGraphChart D0)
    (G1 : PlanarFamilyGraphChart D1)
    (hab : a ≤ b)
    (hboundary : ∀ t ∈ Icc a b,
      Disjoint (Set.range (c0 t)) (Set.range (c1 t)))
    (hstart : Disjoint
      (G0.fiberBallNeighborhood a ⟨le_rfl, hab⟩).closedRegion
      (G1.fiberBallNeighborhood a ⟨le_rfl, hab⟩).closedRegion) :
    ∀ t : ℝ, ∀ ht : t ∈ Icc a b,
      Disjoint (G0.fiberBallNeighborhood t ht).closedRegion
        (G1.fiberBallNeighborhood t ht).closedRegion := by
  classical
  let T := {t : ℝ // t ∈ Icc a b}
  let K := {x : E2 // x ∈ closedBall (0 : E2) 1}
  let : ConnectedSpace T := isConnected_iff_connectedSpace.mp (isConnected_Icc hab)
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E2) 1)
  let B0 : T → BallNeighborhoodChart E2 E2 :=
    fun t => G0.fiberBallNeighborhood (t : ℝ) t.property
  let B1 : T → BallNeighborhoodChart E2 E2 :=
    fun t => G1.fiberBallNeighborhood (t : ℝ) t.property
  let Good : Set T := {t | Disjoint (B0 t).closedRegion (B1 t).closedRegion}
  have hFamily {c : ℝ → UnitCircle → E2}
      (D : PlanarSchoenfliesFamilyData c a b) (G : PlanarFamilyGraphChart D) :
      Continuous (fun p : T × K => D.chart (p.1 : ℝ) (p.2 : E2)) := by
    have harg : Continuous (fun p : T × K => ((p.1 : ℝ), (p.2 : E2))) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    have hc := G.chart.continuousOn.comp_continuous harg (fun p =>
      G.mem_source p.1.property ((closedBall_subset_ball G.one_lt_radius) p.2.property))
    simpa only [Function.comp_def, G.chart_apply] using hc.snd
  have h0 : Continuous (fun p : T × (K × K) => D0.chart (p.1 : ℝ) (p.2.1 : E2)) :=
    (hFamily D0 G0).comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h1 : Continuous (fun p : T × (K × K) => D1.chart (p.1 : ℝ) (p.2.2 : E2)) :=
    (hFamily D1 G1).comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  let Z : Set (T × (K × K)) :=
    {p | D0.chart (p.1 : ℝ) (p.2.1 : E2) = D1.chart (p.1 : ℝ) (p.2.2 : E2)}
  have hZ : IsClosed Z := isClosed_eq h0 h1
  have hBad : Goodᶜ = Prod.fst '' Z := by
    ext t
    constructor
    · intro ht
      have hnot : ¬ Disjoint (B0 t).closedRegion (B1 t).closedRegion := ht
      obtain ⟨z, hz0, hz1⟩ := Set.not_disjoint_iff.mp hnot
      obtain ⟨x, hx, hxz⟩ := hz0
      obtain ⟨y, hy, hyz⟩ := hz1
      refine ⟨(t, (⟨x, hx⟩, ⟨y, hy⟩)), ?_, rfl⟩
      change D0.chart (t : ℝ) x = D1.chart (t : ℝ) y
      exact hxz.trans hyz.symm
    · rintro ⟨⟨s, x, y⟩, hs, hst⟩
      change s = t at hst
      subst s
      have heq : D0.chart (t : ℝ) (x : E2) = D1.chart (t : ℝ) (y : E2) := hs
      change ¬ Disjoint (B0 t).closedRegion (B1 t).closedRegion
      intro hd
      exact disjoint_left.mp hd
        ⟨(x : E2), x.property, rfl⟩ ⟨(y : E2), y.property, heq.symm⟩
  have hGoodOpen : IsOpen Good := by
    apply isClosed_compl_iff.mp
    rw [hBad]
    exact isClosedMap_fst_of_compactSpace Z hZ
  have hBoundary (t : T) : Disjoint (B0 t).boundary (B1 t).boundary := by
    simpa only [B0, B1, PlanarFamilyGraphChart.fiberBallNeighborhood_boundary] using
      hboundary (t : ℝ) t.property
  have hInsideMeet (t : T) (ht : t ∉ Good) :
      ((B0 t).inside ∩ (B1 t).inside).Nonempty := by
    obtain ⟨z, hz0, hz1⟩ := Set.not_disjoint_iff.mp ht
    have hz0c : z ∈ closure (B0 t).inside := by rw [(B0 t).closure_inside]; exact hz0
    have hz1c : z ∈ closure (B1 t).inside := by rw [(B1 t).closure_inside]; exact hz1
    rw [← (B0 t).inside_union_boundary] at hz0
    rw [← (B1 t).inside_union_boundary] at hz1
    rcases hz0 with hi0 | hb0 <;> rcases hz1 with hi1 | hb1
    · exact ⟨z, hi0, hi1⟩
    · exact mem_closure_iff.mp hz1c (B0 t).inside (B0 t).inside_open hi0
    · obtain ⟨w, hw1, hw0⟩ :=
        mem_closure_iff.mp hz0c (B1 t).inside (B1 t).inside_open hi1
      exact ⟨w, hw0, hw1⟩
    · exact False.elim (disjoint_left.mp (hBoundary t) hb0 hb1)
  have hBadOpen : IsOpen Goodᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    obtain ⟨z, hz0, hz1⟩ := hInsideMeet t ht
    obtain ⟨x0, hx0, hx0z⟩ := hz0
    obtain ⟨x1, hx1, hx1z⟩ := hz1
    let x0K : K := ⟨x0, ball_subset_closedBall hx0⟩
    let w : T → E2 := fun s => D0.chart (s : ℝ) x0
    have hw : Continuous w :=
      (hFamily D0 G0).comp (continuous_id.prodMk (continuous_const (y := x0K)))
    have hs1 : ((t : ℝ), x1) ∈ G1.chart.source :=
      G1.mem_source t.property
        (ball_subset_ball G1.one_lt_radius.le hx1)
    have hwt : w t = D1.chart (t : ℝ) x1 := hx0z.trans hx1z.symm
    let Q : T → ℝ × E2 := fun s => ((s : ℝ), w s)
    have hQ : Continuous Q := continuous_subtype_val.prodMk hw
    have hQt : Q t = G1.chart ((t : ℝ), x1) := by
      rw [G1.chart_apply]
      exact Prod.ext rfl hwt
    have htTarget : Q t ∈ G1.chart.target := by
      rw [hQt]
      exact G1.chart.map_source hs1
    let y : T → E2 := fun s => (G1.chart.symm (Q s)).2
    have hy : ContinuousAt y t :=
      ((G1.smooth_symm.continuousOn.continuousAt
        (G1.chart.open_target.mem_nhds htTarget)).comp hQ.continuousAt).snd
    have hyt : y t = x1 := by
      change (G1.chart.symm (Q t)).2 = x1
      rw [hQt, G1.chart.left_inv hs1]
    have hTarget : ∀ᶠ s : T in 𝓝 t, Q s ∈ G1.chart.target :=
      hQ.continuousAt.eventually_mem (G1.chart.open_target.mem_nhds htTarget)
    have hBall : ∀ᶠ s : T in 𝓝 t, y s ∈ ball (0 : E2) 1 :=
      hy.eventually_mem (isOpen_ball.mem_nhds (by rw [hyt]; exact hx1))
    filter_upwards [hTarget, hBall] with s hs hyball
    have hright : D1.chart (s : ℝ) (y s) = w s := by
      have hh := congrArg Prod.snd (G1.chart.right_inv hs)
      simpa only [G1.chart_apply, G1.inverse_fst hs] using hh
    change ¬ Disjoint (B0 s).closedRegion (B1 s).closedRegion
    intro hd
    exact disjoint_left.mp hd
      ⟨x0, ball_subset_closedBall hx0, rfl⟩
      ⟨y s, ball_subset_closedBall hyball, hright⟩
  have hClopen : IsClopen Good := ⟨isOpen_compl_iff.mp hBadOpen, hGoodOpen⟩
  have hNonempty : Good.Nonempty := ⟨⟨a, le_rfl, hab⟩, hstart⟩
  have hAll : Good = univ := hClopen.eq_univ hNonempty
  intro t ht
  have hmem : (⟨t, ht⟩ : T) ∈ Good := by rw [hAll]; exact mem_univ _
  exact hmem

end PoincareConjecture.M25.Topology3D
