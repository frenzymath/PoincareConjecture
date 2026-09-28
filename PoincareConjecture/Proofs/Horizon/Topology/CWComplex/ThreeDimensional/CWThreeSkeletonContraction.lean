import PoincareConjecture.Proofs.Horizon.Topology.CWComplex.Construction.CWRelativeHomotopy

set_option autoImplicit false

open Set Metric
open scoped Topology unitInterval

universe u v

namespace Poincare.Topology

noncomputable section

open _root_.Topology.RelCWComplex

theorem exists_cw_three_skeleton_contraction_of_paths
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y] [PathConnectedSpace Y]
    {C : Set X} [_root_.Topology.CWComplex C]
    (hpi1 : ∀ y : Y, Subsingleton (HomotopyGroup.Pi 1 Y y))
    (hpi2 : ∀ y : Y, Subsingleton (HomotopyGroup.Pi 2 Y y))
    (f : C(C, Y)) (y0 : Y)
    (hpaths : ∀ j : cell C 0, Path (f (⟨map 0 j 0,
      (skeletonLT C 3).subset_complex (skeletonLT_mono (by norm_num)
        (closedCell_subset_skeletonLT 0 j ⟨0, by simp, rfl⟩))⟩)) y0) :
    ∃ H : C(unitInterval × ↥(skeletonLT C 3), Y),
      (∀ x, H (0, x) = f ⟨x.val, (skeletonLT C 3).subset_complex x.property⟩) ∧
      (∀ x, H (1, x) = y0) ∧
      (∀ (t : unitInterval) (j : cell C 0), H (t, ⟨map 0 j 0,
        skeletonLT_mono (by norm_num)
          (closedCell_subset_skeletonLT 0 j ⟨0, by simp, rfl⟩)⟩) = hpaths j t) := by
  classical
  let f2 : C(↥(skeletonLT C ((2 : Nat) : ℕ∞)), Y) :=
    f.comp ⟨fun x => ⟨x.val, (skeletonLT C 3).subset_complex
      (skeletonLT_mono (by norm_num) x.property)⟩,
      continuous_subtype_val.subtype_mk _⟩
  let path (j : cell C 0) := hpaths j
  let G0 (j : cell C 0) : C(closedBall (0 : Fin 0 → ℝ) 1, C(unitInterval, Y)) :=
    ContinuousMap.const _ (path j).toContinuousMap
  let old0 : C(↥(skeletonLT C 0), C(unitInterval, Y)) :=
    ContinuousMap.const _ (Path.refl y0).toContinuousMap
  have hG0 : ∀ (j : cell C 0) (z : sphere (0 : Fin 0 → ℝ) 1),
      G0 j ⟨z.val, sphere_subset_closedBall z.property⟩ = old0 ⟨map 0 j z,
        cellFrontier_subset_skeletonLT 0 j ⟨z, z.property, rfl⟩⟩ := by
    intro j z
    have hs : sphere (0 : Fin 0 → ℝ) 1 = ∅ := sphere_eq_empty_of_subsingleton one_ne_zero
    rw [hs] at z
    exact z.property.elim
  obtain ⟨K1, hK1old, hK1cell⟩ := exists_cw_skeleton_pasting C (∅ : Set X) 0 old0 G0 hG0
  have he01 : ((0 : ℕ∞) + 1) = ((1 : Nat) : ℕ∞) := by norm_num
  let e01 : ↥(skeletonLT C ((0 : ℕ∞) + 1)) ≃ₜ ↥(skeletonLT C ((1 : Nat) : ℕ∞)) :=
    Homeomorph.setCongr (by rw [he01])
  let K1' : C(↥(skeletonLT C ((1 : Nat) : ℕ∞)), C(unitInterval, Y)) :=
    K1.comp ⟨e01.symm, e01.symm.continuous⟩
  let H1 : C(unitInterval × ↥(skeletonLT C ((1 : Nat) : ℕ∞)), Y) := by
    exact K1'.uncurry.comp
        (Homeomorph.prodComm unitInterval
          ↥(skeletonLT C ((1 : Nat) : ℕ∞)) : C(_, _))
  have hK1cell' (j : cell C 0) (z : closedBall (0 : Fin 0 → ℝ) 1) :
      K1' ⟨map 0 j z,
        (by
          apply skeletonLT_mono (show ((0 : ℕ∞) + 1) ≤ ((1 : Nat) : ℕ∞) by norm_num)
          exact closedCell_subset_skeletonLT 0 j ⟨z, z.property, rfl⟩)⟩ = G0 j z := by
    dsimp only [K1', ContinuousMap.comp_apply]
    exact (congrArg K1 (Subtype.ext rfl)).trans (hK1cell j z)
  have hK1cell_value (t : unitInterval) (x : ↥(skeletonLT C ((1 : Nat) : ℕ∞)))
      (j : cell C 0) (z : closedBall (0 : Fin 0 → ℝ) 1)
      (hzx : map 0 j z = x.val) : H1 (t, x) = (G0 j z) t := by
    have hx' : x = ⟨map 0 j z,
        (by
          apply skeletonLT_mono (show ((0 : ℕ∞) + 1) ≤ ((1 : Nat) : ℕ∞) by norm_num)
          exact closedCell_subset_skeletonLT 0 j ⟨z, z.property, rfl⟩)⟩ :=
      Subtype.ext hzx.symm
    rw [hx']
    change K1' ⟨map 0 j z, _⟩ t = (G0 j z) t
    exact congrArg (fun q : C(unitInterval, Y) => q t) (hK1cell' j z)
  have hK1zero (x : ↥(skeletonLT C ((1 : Nat) : ℕ∞))) :
      H1 (0, x) = f2 ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩ := by
    rcases _root_.Topology.CWComplex.mem_skeletonLT_iff.mp x.property with ⟨k, hk, j, hxj⟩
    have hkNat : k < 1 := by exact_mod_cast hk
    have hk0 : k = 0 := by omega
    subst k
    obtain ⟨z, hz, hzx⟩ := hxj
    have hz0 : z = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
    subst z
    have hv := hK1cell_value 0 x j ⟨0, by simp⟩ hzx
    rw [hv]
    change (hpaths j) 0 = f ⟨x.val, _⟩
    rw [(hpaths j).source]
    exact congrArg f (Subtype.ext hzx)
  have hK1one (x : ↥(skeletonLT C ((1 : Nat) : ℕ∞))) : H1 (1, x) = y0 := by
    rcases _root_.Topology.CWComplex.mem_skeletonLT_iff.mp x.property with ⟨k, hk, j, hxj⟩
    have hkNat : k < 1 := by exact_mod_cast hk
    have hk0 : k = 0 := by omega
    subst k
    obtain ⟨z, hz, hzx⟩ := hxj
    have hz0 : z = (0 : Fin 0 → ℝ) := Subsingleton.elim _ _
    subst z
    have hv := hK1cell_value 1 x j ⟨0, by simp⟩ hzx
    rw [hv]
    simp [G0, path]
  let g2 : C(↥(skeletonLT C ((2 : Nat) : ℕ∞)), Y) := ContinuousMap.const _ y0
  obtain ⟨H2, hH20, hH21, hH2side⟩ := exists_cw_skeleton_relative_homotopy
    C (∅ : Set X) 0 hpi1 f2 g2 H1 hK1zero hK1one
  let f3 : C(↥(skeletonLT C ((3 : Nat) : ℕ∞)), Y) :=
    f.comp ⟨fun x => ⟨x.val, (skeletonLT C 3).subset_complex x.property⟩,
      continuous_subtype_val.subtype_mk _⟩
  let g3 : C(↥(skeletonLT C ((3 : Nat) : ℕ∞)), Y) := ContinuousMap.const _ y0
  obtain ⟨H3, hH30, hH31, hH3side⟩ := exists_cw_skeleton_relative_homotopy
    C (∅ : Set X) 1 hpi2 f3 g3 H2 hH20 hH21
  have hzero (t : unitInterval) (j : cell C 0) :
      H3 (t, ⟨map 0 j 0,
        skeletonLT_mono (by norm_num)
          (closedCell_subset_skeletonLT 0 j ⟨0, by simp, rfl⟩)⟩) = (hpaths j) t := by
    let x1 : ↥(skeletonLT C ((1 : Nat) : ℕ∞)) :=
      ⟨map 0 j 0, closedCell_subset_skeletonLT 0 j ⟨0, by simp, rfl⟩⟩
    let x2 : ↥(skeletonLT C ((2 : Nat) : ℕ∞)) :=
      ⟨map 0 j 0, skeletonLT_mono (by norm_num) x1.property⟩
    rw [hH3side t x2]
    rw [hH2side t x1]
    exact hK1cell_value t x1 j ⟨0, by simp⟩ rfl
  refine ⟨H3, ?_, hH31, hzero⟩
  intro x
  exact hH30 x

theorem exists_cw_three_skeleton_contraction
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y] [PathConnectedSpace Y]
    {C : Set X} [_root_.Topology.CWComplex C]
    (hpi1 : ∀ y : Y, Subsingleton (HomotopyGroup.Pi 1 Y y))
    (hpi2 : ∀ y : Y, Subsingleton (HomotopyGroup.Pi 2 Y y))
    (f : C(C, Y)) (y0 : Y) :
    ∃ H : C(unitInterval × ↥(skeletonLT C 3), Y),
      (∀ x, H (0, x) = f ⟨x.val, (skeletonLT C 3).subset_complex x.property⟩) ∧
      (∀ x, H (1, x) = y0) := by
  obtain ⟨H, h0, h1, _⟩ := exists_cw_three_skeleton_contraction_of_paths hpi1 hpi2 f y0
    (fun _ => PathConnectedSpace.somePath _ _)
  exact ⟨H, h0, h1⟩

theorem exists_cw_three_skeleton_contraction_fixed
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y] [PathConnectedSpace Y]
    {C : Set X} [_root_.Topology.CWComplex C]
    (hpi1 : ∀ y : Y, Subsingleton (HomotopyGroup.Pi 1 Y y))
    (hpi2 : ∀ y : Y, Subsingleton (HomotopyGroup.Pi 2 Y y))
    (f : C(C, Y)) (j0 : cell C 0) :
    ∃ H : C(unitInterval × ↥(skeletonLT C 3), Y),
      (∀ x, H (0, x) = f ⟨x.val, (skeletonLT C 3).subset_complex x.property⟩) ∧
      (∀ x, H (1, x) = f ⟨map 0 j0 0,
        (skeletonLT C 3).subset_complex (skeletonLT_mono (by norm_num)
          (closedCell_subset_skeletonLT 0 j0 ⟨0, by simp, rfl⟩))⟩) ∧
      (∀ t : unitInterval, H (t, ⟨map 0 j0 0,
        skeletonLT_mono (by norm_num)
          (closedCell_subset_skeletonLT 0 j0 ⟨0, by simp, rfl⟩)⟩) =
        f ⟨map 0 j0 0,
          (skeletonLT C 3).subset_complex (skeletonLT_mono (by norm_num)
            (closedCell_subset_skeletonLT 0 j0 ⟨0, by simp, rfl⟩))⟩) := by
  let y0 : Y := f ⟨map 0 j0 0,
    (skeletonLT C 3).subset_complex (skeletonLT_mono (by norm_num)
      (closedCell_subset_skeletonLT 0 j0 ⟨0, by simp, rfl⟩))⟩
  let hpaths (j : cell C 0) : Path (f ⟨map 0 j 0,
      (skeletonLT C 3).subset_complex (skeletonLT_mono (by norm_num)
        (closedCell_subset_skeletonLT 0 j ⟨0, by simp, rfl⟩))⟩) y0 := by
    by_cases hj : j = j0
    · subst j
      exact Path.refl y0
    · exact PathConnectedSpace.somePath _ _
  obtain ⟨H, h0, h1, hzero⟩ := exists_cw_three_skeleton_contraction_of_paths
    hpi1 hpi2 f y0 hpaths
  refine ⟨H, h0, ?_, ?_⟩
  · simpa [y0] using h1
  · intro t
    simpa [y0, hpaths] using hzero t j0

end

end Poincare.Topology
