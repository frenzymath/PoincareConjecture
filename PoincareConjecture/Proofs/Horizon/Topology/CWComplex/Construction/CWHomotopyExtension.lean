import PoincareConjecture.Proofs.Horizon.Topology.CWComplex.Construction.CWCellPasting
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Extension.DiskHomotopyExtension

set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval

universe u v

namespace Poincare.Topology

noncomputable section

open _root_.Topology.RelCWComplex

theorem exists_cw_skeleton_homotopy_extension
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y]
    (C D : Set X) [_root_.Topology.RelCWComplex C D] (m : Nat)
    (f : C(↥(skeletonLT C (m + 1)), Y))
    (H : C(unitInterval × ↥(skeletonLT C m), Y))
    (h0 : ∀ x : ↥(skeletonLT C m),
      H (0, x) = f ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩) :
    ∃ F : C(unitInterval × ↥(skeletonLT C (m + 1)), Y),
      (∀ x, F (0, x) = f x) ∧
      (∀ (t : unitInterval) (x : ↥(skeletonLT C m)),
        F (t, ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩) = H (t, x)) := by
  let A := skeletonLT C m
  let B := skeletonLT C (m + 1)
  let c (j : cell C m) : C(closedBall (0 : Fin m → ℝ) 1, ↥B) :=
    ⟨fun z => ⟨map m j z, closedCell_subset_skeletonLT m j ⟨z, z.property, rfl⟩⟩,
      ((continuousOn m j).domRestrict).subtype_mk _⟩
  let a (j : cell C m) : C(sphere (0 : Fin m → ℝ) 1, ↥A) :=
    ⟨fun z => ⟨map m j z, cellFrontier_subset_skeletonLT m j ⟨z, z.property, rfl⟩⟩,
      (((continuousOn m j).mono sphere_subset_closedBall).domRestrict).subtype_mk _⟩
  let Hj (j : cell C m) : C(unitInterval × sphere (0 : Fin m → ℝ) 1, Y) :=
    H.comp ⟨fun p => (p.1, a j p.2), continuous_fst.prodMk ((a j).continuous.comp continuous_snd)⟩
  have hj0 (j : cell C m) (z : sphere (0 : Fin m → ℝ) 1) :
      Hj j (0, z) = (f.comp (c j)) ⟨z.val, sphere_subset_closedBall z.property⟩ := h0 (a j z)
  have hfill (j : cell C m) := exists_disk_homotopy_extension (f.comp (c j)) (Hj j) (hj0 j)
  choose G hG0 hGside using hfill
  let old : C(↥A, C(unitInterval, Y)) :=
    ContinuousMap.curry (H.comp (Homeomorph.prodComm ↥A unitInterval : C(_, _)))
  let new (j : cell C m) : C(closedBall (0 : Fin m → ℝ) 1, C(unitInterval, Y)) :=
    ContinuousMap.curry (G j |>.comp
      (Homeomorph.prodComm (closedBall (0 : Fin m → ℝ) 1) unitInterval : C(_, _)))
  have hboundary (j : cell C m) (z : sphere (0 : Fin m → ℝ) 1) :
      new j ⟨z.val, sphere_subset_closedBall z.property⟩ = old (a j z) := by
    ext t
    exact hGside j t z
  obtain ⟨K, hKold, hKcell⟩ := exists_cw_skeleton_pasting C D m old new hboundary
  let F : C(unitInterval × ↥B, Y) :=
    K.uncurry.comp (Homeomorph.prodComm unitInterval ↥B : C(_, _))
  refine ⟨F, ?_, ?_⟩
  · intro x
    have hx : x.val ∈ (skeletonLT C m : Set X) ∪ ⋃ j : cell C m, closedCell m j := by
      simpa only [skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ, SetLike.mem_coe]
        using x.property
    rcases hx with hx | hx
    · have he : K x = old ⟨x.val, hx⟩ := hKold ⟨x.val, hx⟩
      exact (DFunLike.congr_fun he 0).trans (h0 ⟨x.val, hx⟩)
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      obtain ⟨z, hz, hzx⟩ := hxj
      have he : K x = new j ⟨z, hz⟩ :=
        (congrArg K (Subtype.ext hzx.symm)).trans (hKcell j ⟨z, hz⟩)
      exact (DFunLike.congr_fun he 0).trans
        ((hG0 j ⟨z, hz⟩).trans (congrArg f (Subtype.ext hzx)))
  · intro t x
    exact DFunLike.congr_fun (hKold x) t

end

end Poincare.Topology
