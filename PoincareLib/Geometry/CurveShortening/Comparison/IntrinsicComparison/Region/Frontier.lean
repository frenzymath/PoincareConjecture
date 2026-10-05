import PoincareLib.Geometry.CurveShortening.Comparison.IntrinsicComparison.Region.EdgeIncidence
import PoincareLib.Topology.Surface.Triangulation.Regions.Boundary

/-!
# Exact exposed boundary of a finite coordinate region

Regular closedness excludes isolated frontier points in the plane.
The paired open sides are interior, so removing the finite corner set
leaves only unpaired sides on the frontier. Closure restores every corner.

Morgan--Tian context: Proposition 19.35, printed pp. 467-481, especially Claim 19.40, pp.
470-471. The explicit coordinate-mesh and regional Gauss--Bonnet constructions are project
derivations.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology ContDiff Manifold
open PoincareMT.Topology.Surface

namespace PoincareMT

/-- A finite set cannot isolate a frontier point of a regular closed planar region. Both its
interior and its open complement approach every frontier point, while a punctured coordinate
disk remains connected. Source: Morgan--Tian Proposition 19.35, printed pp. 467-481,
including the Gauss--Bonnet argument in Lemma 19.45, p. 474; the explicit regional
construction is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-euler-turning.md`, Mathematical
Checks. -/
theorem m64Intrinsic_regularClosed_frontier_dense_off_finite
    {R V : Set AnnulusCoordinates} (hR : IsClosed R)
    (hreg : closure (interior R) = R) (hV : V.Finite) :
    frontier R ⊆ closure (frontier R \ V) := by
  have hdense : Dense Vᶜ := by
    simpa only [compl_eq_univ_sdiff] using (dense_univ.sdiff_finite hV)
  intro p hp
  apply _root_.mem_closure_iff.mpr
  intro N hN hpN
  by_contra hnone
  have hfrontN : N ∩ frontier R ⊆ V := by
    intro x hx
    by_contra hxV
    exact hnone ⟨x, hx.1, hx.2, hxV⟩
  let c := chartAt AnnulusCoordinates p
  have hpc : p ∈ c.source := mem_chart_source _ p
  have hnbhd : c.target ∩ c.symm ⁻¹' N ∈ 𝓝 (c p) := by
    refine inter_mem (c.open_target.mem_nhds (c.map_source hpc)) ?_
    apply (c.continuousAt_symm (c.map_source hpc)).preimage_mem_nhds
    simpa only [c.left_inv hpc] using hN.mem_nhds hpN
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnbhd
  let D := c.symm '' ball (c p) r
  have htarget : ball (c p) r ⊆ c.target := fun _ hz => (hball hz).1
  have hDopen : IsOpen D := c.isOpen_image_symm_of_subset_target isOpen_ball htarget
  have hpD : p ∈ D := ⟨c p, mem_ball_self hr, c.left_inv hpc⟩
  have hDN : D ⊆ N := by
    rintro _ ⟨z, hz, rfl⟩
    exact (hball hz).2
  have hDconn : IsPreconnected (D \ V) :=
    isPreconnected_chart_ball_sdiff_finite p hr htarget hV
  have hdisjoint : Disjoint (D \ V) (frontier R) := by
    apply disjoint_left.mpr
    intro z hz hzfront
    exact hz.2 (hfrontN ⟨hDN hz.1, hzfront⟩)
  have hpcl : p ∈ closure (interior R) := hreg.symm ▸ hR.frontier_subset hp
  obtain ⟨z, hzD, hzR⟩ := _root_.mem_closure_iff.mp hpcl D hDopen hpD
  obtain ⟨w, hwV, hwD, hwR⟩ := hdense.exists_mem_open
    (hDopen.inter isOpen_interior) ⟨z, hzD, hzR⟩
  have hinside : D \ V ⊆ interior R :=
    Poincare.Topology.preconnected_subset_interior_of_disjoint_frontier hDconn hdisjoint
      ⟨w, ⟨hwD, hwV⟩, hwR⟩
  have hpout : p ∈ closure Rᶜ := by
    rw [frontier_eq_closure_inter_closure] at hp
    exact hp.2
  obtain ⟨z, hzD, hzR⟩ := _root_.mem_closure_iff.mp hpout D hDopen hpD
  obtain ⟨w, hwV, hwD, hwR⟩ := hdense.exists_mem_open
    (hDopen.inter hR.isOpen_compl) ⟨z, hzD, hzR⟩
  exact hwR (interior_subset (hinside ⟨hwD, hwV⟩))

/-- The complete frontier of an actual compatible finite coordinate family is exactly the
union of its unpaired complete side images. No boundary-edge listing or vertex coverage
assumption is supplied. Source: Morgan--Tian Proposition 19.35, printed pp. 467-481,
including the Gauss--Bonnet argument in Lemma 19.45, p. 474; the explicit regional
construction is reviewed in
`proof-work/tasks/M64/reviews/2026-09-27-round1-intrinsic-euler-turning.md`, Mathematical
Checks. -/
theorem m64Intrinsic_region_frontier_eq_unpaired_sides
    {I : Type*} [Finite I] (face : I → SmoothFace AnnulusCoordinates)
    (F : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
    (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ v : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i v)})
    (hfront : ∀ i j, i ≠ j → (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier) :
    frontier (⋃ i, (face i).carrier) =
      ⋃ p : {p : I × Fin 3 // ∀ q : I × Fin 3,
          faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p},
        ((face p.1.1).boundary p.1.2).map '' Icc (0 : ℝ) 1 := by
  classical
  let R := ⋃ i, (face i).carrier
  let V := range (fun p : I × Fin 3 => F p.1 (b p.1 p.2))
  let A := {p : I × Fin 3 // ∀ q : I × Fin 3,
    faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face p.1 p.2 → q = p}
  let B := ⋃ p : A, ((face p.1.1).boundary p.1.2).map '' Icc (0 : ℝ) 1
  have hR : IsClosed R := isClosed_iUnion_of_finite (fun i => (face i).isClosed_carrier)
  have hreg : closure (interior R) = R := by
    apply Poincare.Topology.closure_interior_iUnion_of_regular_closed _
      (fun i => (face i).isClosed_carrier)
    intro i
    rw [hcarrier]
    exact coordinate_triangle_closure_interior (F i) (b i) (hsource i)
  have hB : IsClosed B := isClosed_iUnion_of_finite (fun p =>
    (isCompact_Icc.image_of_continuousOn
      ((face p.1.1).boundary p.1.2).smooth.continuousOn).isClosed)
  have hsub : frontier R \ V ⊆ B := by
    rintro x ⟨hx, hxV⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hR.frontier_subset hx)
    have hxfront : x ∈ frontier (face i).carrier := by
      refine ⟨subset_closure hxi, ?_⟩
      intro hint
      exact hx.2 (interior_mono (subset_iUnion (fun j => (face j).carrier) i) hint)
    rw [(face i).boundary_carrier] at hxfront
    obtain ⟨k, t, ht, htx⟩ := mem_iUnion.mp hxfront
    have ht0 : t ≠ 0 := by
      intro heq
      apply hxV
      refine ⟨(i, k.succAbove 0), ?_⟩
      simpa only [heq, hboundary, Function.comp_apply, affineChartSegment,
        zero_smul, sub_zero, one_smul, add_zero] using htx
    have ht1 : t ≠ 1 := by
      intro heq
      apply hxV
      refine ⟨(i, k.succAbove 1), ?_⟩
      simpa only [heq, hboundary, Function.comp_apply, affineChartSegment,
        one_smul, sub_self, zero_smul, zero_add, ← add_sub_assoc, add_sub_cancel_left] using htx
    have htopen : t ∈ Ioo (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩
    have hunpaired : ∀ q : I × Fin 3,
        faceBoundaryIndex face q.1 q.2 = faceBoundaryIndex face i k → q = (i, k) := by
      intro q hq
      by_contra hne
      have hxint := m64Intrinsic_paired_side_subset_region_interior face F b hsource
        hcarrier hboundary hfront (i, k) q (Ne.symm hne) hq.symm ⟨t, htopen, htx⟩
      exact hx.2 hxint
    exact mem_iUnion.mpr ⟨⟨(i, k), hunpaired⟩, t, ht, htx⟩
  change frontier R = B
  apply Subset.antisymm
  · exact (m64Intrinsic_regularClosed_frontier_dense_off_finite hR hreg
      (finite_range _)).trans (closure_minimal hsub hB)
  · rintro x hx
    obtain ⟨p, hp⟩ := mem_iUnion.mp hx
    exact m64Intrinsic_unpaired_side_subset_region_frontier face F b hsource hboundary
      hinter p.1 p.2 hp

end PoincareMT
