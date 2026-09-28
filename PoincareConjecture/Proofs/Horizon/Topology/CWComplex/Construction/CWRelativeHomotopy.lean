import PoincareConjecture.Proofs.Horizon.Topology.CWComplex.Construction.CWCellPasting
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Extension.DiskRelativeHomotopy








set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval

universe u v

namespace Poincare.Topology

noncomputable section

open _root_.Topology.RelCWComplex

theorem exists_cw_skeleton_relative_homotopy
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y]
    (C D : Set X) [_root_.Topology.RelCWComplex C D] (n : Nat)
    (hpi : ∀ y : Y, Subsingleton (HomotopyGroup.Pi (n + 1) Y y))
    (f g : C(↥(skeletonLT C ((n + 2 : Nat) : ℕ∞)), Y))
    (H : C(unitInterval × ↥(skeletonLT C ((n + 1 : Nat) : ℕ∞)), Y))
    (h0 : ∀ x : ↥(skeletonLT C ((n + 1 : Nat) : ℕ∞)),
      H (0, x) = f ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩)
    (h1 : ∀ x : ↥(skeletonLT C ((n + 1 : Nat) : ℕ∞)),
      H (1, x) = g ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩) :
    ∃ F : C(unitInterval × ↥(skeletonLT C ((n + 2 : Nat) : ℕ∞)), Y),
      (∀ x, F (0, x) = f x) ∧ (∀ x, F (1, x) = g x) ∧
      (∀ (t : unitInterval) (x : ↥(skeletonLT C ((n + 1 : Nat) : ℕ∞))),
        F (t, ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩) = H (t, x)) := by
  let A := skeletonLT C ((n + 1 : Nat) : ℕ∞)
  let B := skeletonLT C ((n + 2 : Nat) : ℕ∞)
  let c (j : cell C (n + 1)) : C(closedBall (0 : Fin (n + 1) → ℝ) 1, ↥B) :=
    ⟨fun z => ⟨map (n + 1) j z,
      closedCell_subset_skeletonLT (n + 1) j ⟨z, z.property, rfl⟩⟩,
      ((continuousOn (n + 1) j).domRestrict).subtype_mk _⟩
  let a (j : cell C (n + 1)) : C(sphere (0 : Fin (n + 1) → ℝ) 1, ↥A) :=
    ⟨fun z => ⟨map (n + 1) j z,
      cellFrontier_subset_skeletonLT (n + 1) j ⟨z, z.property, rfl⟩⟩,
      (((continuousOn (n + 1) j).mono sphere_subset_closedBall).domRestrict).subtype_mk _⟩
  let Hj (j : cell C (n + 1)) : C(unitInterval × sphere (0 : Fin (n + 1) → ℝ) 1, Y) :=
    H.comp ⟨fun p => (p.1, a j p.2), continuous_fst.prodMk ((a j).continuous.comp continuous_snd)⟩
  have hj0 (j : cell C (n + 1)) (z : sphere (0 : Fin (n + 1) → ℝ) 1) :
      Hj j (0, z) = (f.comp (c j)) ⟨z.val, sphere_subset_closedBall z.property⟩ := h0 (a j z)
  have hj1 (j : cell C (n + 1)) (z : sphere (0 : Fin (n + 1) → ℝ) 1) :
      Hj j (1, z) = (g.comp (c j)) ⟨z.val, sphere_subset_closedBall z.property⟩ := h1 (a j z)
  have hfill (j : cell C (n + 1)) := exists_disk_relative_homotopy_of_pi_trivial n hpi
    (f.comp (c j)) (g.comp (c j)) (Hj j) (hj0 j) (hj1 j)
  choose G hG0 hG1 hGside using hfill
  let old : C(↥A, C(unitInterval, Y)) :=
    ContinuousMap.curry (H.comp (Homeomorph.prodComm ↥A unitInterval : C(_, _)))
  let new (j : cell C (n + 1)) : C(closedBall (0 : Fin (n + 1) → ℝ) 1, C(unitInterval, Y)) :=
    ContinuousMap.curry (G j |>.comp
      (Homeomorph.prodComm (closedBall (0 : Fin (n + 1) → ℝ) 1) unitInterval : C(_, _)))
  have hboundary (j : cell C (n + 1)) (z : sphere (0 : Fin (n + 1) → ℝ) 1) :
      new j ⟨z.val, sphere_subset_closedBall z.property⟩ = old (a j z) := by
    ext t
    exact hGside j t z
  obtain ⟨Kraw, hKrawold, hKrawcell⟩ := exists_cw_skeleton_pasting C D (n + 1) old new hboundary
  have heq : (B : Set X) = skeletonLT C ((n + 1 : Nat) + 1) := by
    dsimp only [B]
    have hn : ((n + 2 : Nat) : ℕ∞) = ((n + 1 : Nat) : ℕ∞) + 1 := by
      rw [ENat.natCast_add]
      rfl
    exact congrArg (fun k : ℕ∞ => (skeletonLT C k : Set X)) hn
  let e : ↥B ≃ₜ ↥(skeletonLT C ((n + 1 : Nat) + 1)) := Homeomorph.setCongr heq
  let K : C(↥B, C(unitInterval, Y)) := Kraw.comp (e : C(_, _))
  have hKold (x : ↥A) : K ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩ = old x :=
    (congrArg Kraw (Subtype.ext rfl)).trans (hKrawold x)
  have hKcell (j : cell C (n + 1)) (z : closedBall (0 : Fin (n + 1) → ℝ) 1) :
      K (c j z) = new j z :=
    (congrArg Kraw (Subtype.ext rfl)).trans (hKrawcell j z)
  let F : C(unitInterval × ↥B, Y) :=
    K.uncurry.comp (Homeomorph.prodComm unitInterval ↥B : C(_, _))
  have hend (t : unitInterval) (q : C(↥B, Y))
      (hold : ∀ x : ↥A, H (t, x) = q ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩)
      (hcell : ∀ (j : cell C (n + 1)) z, G j (t, z) = q (c j z)) :
      ∀ x, F (t, x) = q x := by
    intro x
    have hxprop : x.val ∈ skeletonLT C ((n + 1 : Nat) + 1) := by
      have hp := x.property
      change x.val ∈ skeletonLT C ((n + 2 : Nat) : ℕ∞) at hp
      have hn : ((n + 2 : Nat) : ℕ∞) = ((n + 1 : Nat) : ℕ∞) + 1 := by
        rw [ENat.natCast_add]
        rfl
      rw [hn] at hp
      exact hp
    have hx : x.val ∈ (A : Set X) ∪ ⋃ j : cell C (n + 1), closedCell (n + 1) j := by
      simpa only [A, skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ, SetLike.mem_coe]
        using hxprop
    rcases hx with hx | hx
    · exact (DFunLike.congr_fun (hKold ⟨x.val, hx⟩) t).trans (hold ⟨x.val, hx⟩)
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp hx
      obtain ⟨z, hz, hzx⟩ := hxj
      have he : K x = new j ⟨z, hz⟩ :=
        (congrArg K (Subtype.ext hzx.symm)).trans (hKcell j ⟨z, hz⟩)
      exact (DFunLike.congr_fun he t).trans
        ((hcell j ⟨z, hz⟩).trans (congrArg q (Subtype.ext hzx)))
  exact ⟨F, hend 0 f h0 hG0, hend 1 g h1 hG1,
    fun t x => DFunLike.congr_fun (hKold x) t⟩

end

end Poincare.Topology
