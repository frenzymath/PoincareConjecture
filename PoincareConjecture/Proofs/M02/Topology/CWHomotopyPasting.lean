import PoincareConjecture.Proofs.M02.Topology.CWCellPasting

set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

open _root_.Topology.RelCWComplex

theorem exists_cw_skeleton_homotopy_pasting
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y]
    (C D : Set X) [_root_.Topology.RelCWComplex C D] (m : Nat)
    (f g : C(↥(skeletonLT C (m + 1)), Y))
    (H : C(unitInterval × ↥(skeletonLT C m), Y))
    (h0 : ∀ x : ↥(skeletonLT C m),
      H (0, x) = f ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩)
    (h1 : ∀ x : ↥(skeletonLT C m),
      H (1, x) = g ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩)
    (G : cell C m → C(unitInterval × closedBall (0 : Fin m → Real) 1, Y))
    (hG0 : ∀ (j : cell C m) z,
      G j (0, z) = f ⟨map m j z, closedCell_subset_skeletonLT m j ⟨z, z.property, rfl⟩⟩)
    (hG1 : ∀ (j : cell C m) z,
      G j (1, z) = g ⟨map m j z, closedCell_subset_skeletonLT m j ⟨z, z.property, rfl⟩⟩)
    (hGside : ∀ (j : cell C m) (t : unitInterval) (z : sphere (0 : Fin m → Real) 1),
      G j (t, ⟨z.val, sphere_subset_closedBall z.property⟩) =
        H (t, ⟨map m j z, cellFrontier_subset_skeletonLT m j ⟨z, z.property, rfl⟩⟩)) :
    ∃ F : f.Homotopy g, ∀ (t : unitInterval) (x : ↥(skeletonLT C m)),
      F (t, ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩) = H (t, x) := by
  let A := skeletonLT C m
  let B := skeletonLT C (m + 1)
  let old : C(↥A, C(unitInterval, Y)) :=
    ContinuousMap.curry (H.comp (Homeomorph.prodComm ↥A unitInterval : C(_, _)))
  let new (j : cell C m) : C(closedBall (0 : Fin m → Real) 1, C(unitInterval, Y)) :=
    ContinuousMap.curry ((G j).comp
      (Homeomorph.prodComm (closedBall (0 : Fin m → Real) 1) unitInterval : C(_, _)))
  have hboundary (j : cell C m) (z : sphere (0 : Fin m → Real) 1) :
      new j ⟨z.val, sphere_subset_closedBall z.property⟩ =
        old ⟨map m j z, cellFrontier_subset_skeletonLT m j ⟨z, z.property, rfl⟩⟩ := by
    ext t
    exact hGside j t z
  obtain ⟨K, hKold, hKcell⟩ := exists_cw_skeleton_pasting C D m old new hboundary
  let F : C(unitInterval × ↥B, Y) :=
    K.uncurry.comp (Homeomorph.prodComm unitInterval ↥B : C(_, _))
  have hend (t : unitInterval) (q : C(↥B, Y))
      (hold : ∀ x : ↥A, H (t, x) = q ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩)
      (hcell : ∀ (j : cell C m) z,
        G j (t, z) = q ⟨map m j z, closedCell_subset_skeletonLT m j ⟨z, z.property, rfl⟩⟩) :
      ∀ x, F (t, x) = q x := by
    intro x
    have hx : x.val ∈ (A : Set X) ∪ ⋃ j : cell C m, closedCell m j := by
      simpa only [A, skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ, SetLike.mem_coe]
        using x.property
    rcases hx with hx | hx
    · exact (DFunLike.congr_fun (hKold ⟨x.val, hx⟩) t).trans (hold ⟨x.val, hx⟩)
    · obtain ⟨j, z, hz, hzx⟩ := Set.mem_iUnion.mp hx
      have he : K x = new j ⟨z, hz⟩ :=
        (congrArg K (Subtype.ext hzx.symm)).trans (hKcell j ⟨z, hz⟩)
      exact (DFunLike.congr_fun he t).trans
        ((hcell j ⟨z, hz⟩).trans (congrArg q (Subtype.ext hzx)))
  refine ⟨{
    toContinuousMap := F
    map_zero_left := hend 0 f h0 hG0
    map_one_left := hend 1 g h1 hG1 }, ?_⟩
  intro t x
  exact DFunLike.congr_fun (hKold x) t

end

end PoincareConjecture.Proofs.M02.Topology
