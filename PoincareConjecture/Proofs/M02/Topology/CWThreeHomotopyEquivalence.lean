import PoincareConjecture.Proofs.M02.Topology.CWHomotopyExtension
import PoincareConjecture.Proofs.M02.Topology.CWThreeSkeletonContraction
import PoincareConjecture.Proofs.M02.Topology.CWHomotopyPasting
import PoincareConjecture.Proofs.M02.Topology.CubeHomotopyLifting
import Mathlib.Topology.Homotopy.Equiv

set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval ContinuousMap

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

open _root_.Topology.RelCWComplex

theorem nonempty_homotopyEquiv_of_cw_three_pi_bijective
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {C : Set X} [_root_.Topology.CWComplex C] [PathConnectedSpace C]
    {S : Type v} [TopologicalSpace S] [T2Space S]
    (hdim : (skeletonLT C ((3 : ℕ∞) + 1) : Set X) = C)
    (hpi1 : ∀ x : C, Subsingleton (HomotopyGroup.Pi 1 C x))
    (hpi2 : ∀ x : C, Subsingleton (HomotopyGroup.Pi 2 C x))
    (x0 : C) (j0 : cell C 0) (hj0 : map 0 j0 0 = x0.val)
    (q : C((Fin 3 → unitInterval), S))
    (hq : _root_.Topology.IsQuotientMap q)
    (hfiber : ∀ a b, q a = q b ↔ a = b ∨
      (a ∈ Cube.boundary (Fin 3) ∧ b ∈ Cube.boundary (Fin 3)))
    (f : C(S, C)) (hbase : f (q (fun _ => 0)) = x0)
    (hbij : Function.Bijective (homotopyGroupPostcomp 2 f (q (fun _ => 0)))) :
    Nonempty (C ≃ₕ S) := by
  let A := skeletonLT C (3 : ℕ∞)
  let B := skeletonLT C ((3 : ℕ∞) + 1)
  let s0 : S := q (fun _ => 0)
  let a0 : ↥A := ⟨map 0 j0 0, skeletonLT_mono (by norm_num)
    (closedCell_subset_skeletonLT 0 j0 ⟨0, by simp, rfl⟩)⟩
  let i : C(↥A, ↥B) :=
    ⟨fun x => ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  let inc : C(↥B, C) :=
    ⟨fun x => ⟨x.val, B.subset_complex x.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  have hCB (x : C) : x.val ∈ B := by
    change x.val ∈ (B : Set X)
    rw [hdim]
    exact x.property
  let back : C(C, ↥B) :=
    ⟨fun x => ⟨x.val, hCB x⟩, continuous_subtype_val.subtype_mk hCB⟩
  have hpoint : inc (i a0) = x0 := Subtype.ext hj0
  have hbackpoint : back x0 = i a0 := Subtype.ext hj0.symm
  obtain ⟨H, hH0, hH1, hHfixed⟩ :=
    exists_cw_three_skeleton_contraction_fixed hpi1 hpi2 (ContinuousMap.id C) j0
  have hHend (x : ↥A) : H (1, x) = x0 := (hH1 x).trans hpoint
  have hHbase (t : unitInterval) : H (t, a0) = x0 := (hHfixed t).trans hpoint
  obtain ⟨F, hF0, hFold⟩ :=
    exists_cw_skeleton_homotopy_extension C ∅ 3 inc H hH0
  let p : C(↥B, C) :=
    F.comp ⟨fun z => (1, z), continuous_const.prodMk continuous_id⟩
  let V : inc.Homotopy p :=
    { toContinuousMap := F, map_zero_left := hF0, map_one_left := fun _ => rfl }
  have hpold (x : ↥A) : p (i x) = x0 := (hFold 1 x).trans (hHend x)
  have hVfixed (t : unitInterval) : V (t, i a0) = x0 :=
    (hFold t a0).trans (hHbase t)
  let c (j : cell C 3) : C(closedBall (0 : Fin 3 → Real) 1, ↥B) :=
    ⟨fun z => ⟨map 3 j z, closedCell_subset_skeletonLT 3 j ⟨z, z.property, rfl⟩⟩,
      ((continuousOn 3 j).domRestrict).subtype_mk _⟩
  have hboundary (j : cell C 3) (z : sphere (0 : Fin 3 → Real) 1) :
      (p.comp (c j)) ⟨z.val, sphere_subset_closedBall z.property⟩ = f s0 := by
    exact (hpold ⟨map 3 j z,
      cellFrontier_subset_skeletonLT 3 j ⟨z, z.property, rfl⟩⟩).trans hbase.symm
  have hlifts (j : cell C 3) :=
    exists_characteristic_disk_lift 2 f s0 hbij.2 (p.comp (c j)) (hboundary j)
  choose gj Gj hgj hGj0 hGj1 hGjside using hlifts
  obtain ⟨gB, hgBold, hgBcell⟩ := exists_cw_skeleton_pasting C ∅ 3
    (ContinuousMap.const ↥A s0) gj hgj
  let oldH : C(unitInterval × ↥A, C) := ContinuousMap.const _ x0
  have hold0 (x : ↥A) : oldH (0, x) = (f.comp gB) (i x) :=
    hbase.symm.trans (congrArg f (hgBold x).symm)
  have hold1 (x : ↥A) : oldH (1, x) = p (i x) := (hpold x).symm
  have hcell0 (j : cell C 3) z : Gj j (0, z) = (f.comp gB) (c j z) :=
    (hGj0 j z).trans (congrArg f (hgBcell j z).symm)
  have hcell1 (j : cell C 3) z : Gj j (1, z) = p (c j z) := hGj1 j z
  have hcellside (j : cell C 3) (t : unitInterval) (z : sphere (0 : Fin 3 → Real) 1) :
      Gj j (t, ⟨z.val, sphere_subset_closedBall z.property⟩) =
        oldH (t, ⟨map 3 j z,
          cellFrontier_subset_skeletonLT 3 j ⟨z, z.property, rfl⟩⟩) :=
    (hGjside j t z).trans hbase
  obtain ⟨W, hWold⟩ := exists_cw_skeleton_homotopy_pasting C ∅ 3
    (f.comp gB) p oldH hold0 hold1 Gj hcell0 hcell1 hcellside
  let T : (f.comp gB).Homotopy inc := W.trans V.symm
  have hTfixed (t : unitInterval) : T (t, i a0) = x0 := by
    rw [ContinuousMap.Homotopy.trans_apply]
    split_ifs
    · exact hWold _ a0
    · exact hVfixed _
  let g : C(C, S) := gB.comp back
  let L : (f.comp g).Homotopy (ContinuousMap.id C) :=
    (T.compContinuousMap back).cast (by rfl) (by ext x; rfl)
  have hLfixed (t : unitInterval) : L (t, x0) = x0 := by
    change T (t, back x0) = x0
    rw [hbackpoint]
    exact hTfixed t
  have hgbase : g x0 = s0 := by
    change gB (back x0) = s0
    rw [hbackpoint]
    exact hgBold a0
  have hgfbase : (g.comp f) s0 = s0 := by
    change g (f s0) = s0
    rw [hbase]
    exact hgbase
  let Lf : (f.comp (g.comp f)).Homotopy f :=
    (L.compContinuousMap f).cast (by rfl) (by ext x; rfl)
  have hLffixed (t : unitInterval) : Lf (t, s0) = f s0 := by
    change L (t, f s0) = f s0
    rw [hbase]
    exact hLfixed t
  have hright := homotopic_of_cube_quotient_postcomp_injective
    2 q hq hfiber f hbij.1 (g.comp f) hgfbase Lf hLffixed
  exact ⟨{ toFun := g, invFun := f, left_inv := ⟨L⟩, right_inv := hright }⟩

end

end PoincareConjecture.Proofs.M02.Topology
