import PoincareConjecture.Proofs.Horizon.Topology.CWComplex.Construction.CWCellExtension








set_option autoImplicit false

open Set Metric
open scoped Topology

universe u v

namespace Poincare.Topology

noncomputable section

open _root_.Topology.RelCWComplex

theorem exists_cw_skeleton_pasting
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y]
    (C D : Set X) [_root_.Topology.RelCWComplex C D] (m : Nat)
    (f : C(↥(skeletonLT C m), Y))
    (G : cell C m → C(closedBall (0 : Fin m → ℝ) 1, Y))
    (hG : ∀ (j : cell C m) (z : sphere (0 : Fin m → ℝ) 1),
      G j ⟨z.val, sphere_subset_closedBall z.property⟩ =
        f ⟨map m j z, cellFrontier_subset_skeletonLT m j ⟨z, z.property, rfl⟩⟩) :
    ∃ F : C(↥(skeletonLT C (m + 1)), Y),
      (∀ x : ↥(skeletonLT C m), F ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩ = f x) ∧
      (∀ (j : cell C m) (z : closedBall (0 : Fin m → ℝ) 1),
        F ⟨map m j z, closedCell_subset_skeletonLT m j ⟨z, z.property, rfl⟩⟩ = G j z) := by
  classical
  let A := skeletonLT C m
  let B := skeletonLT C (m + 1)
  have hAB : (A : Set X) ⊆ B := skeletonLT_mono (by norm_num)
  have hnew (x : B) (hx : x.val ∉ A) :
      ∃ (j : cell C m) (z : ball (0 : Fin m → ℝ) 1), map m j z = x.val := by
    rcases mem_skeletonLT_iff.mp x.property with hD | ⟨k, hk, j, hxj⟩
    · exact (hx (A.base_subset hD)).elim
    · have hkm : k < m + 1 := by exact_mod_cast hk
      by_cases hlt : k < m
      · apply (hx ?_).elim
        exact mem_skeletonLT_iff.mpr (Or.inr ⟨k, by exact_mod_cast hlt, j, hxj⟩)
      · have heq : k = m := by omega
        subst k
        obtain ⟨z, hz, hzx⟩ := hxj
        exact ⟨j, ⟨z, hz⟩, hzx⟩
  choose jnew znew hcoord using hnew
  let g (x : B) : Y :=
    if hx : x.val ∈ A then f ⟨x.val, hx⟩ else
      G (jnew x hx) ⟨(znew x hx).val, ball_subset_closedBall (znew x hx).property⟩
  have hgold (x : A) : g ⟨x.val, hAB x.property⟩ = f x := by
    simp only [g, dif_pos x.property]
    exact congrArg f (Subtype.ext rfl)
  have hnewcell (j : cell C m) (z : closedBall (0 : Fin m → ℝ) 1) :
      map m j z ∈ B := closedCell_subset_skeletonLT m j ⟨z, z.property, rfl⟩
  have hgcell (j : cell C m) (z : closedBall (0 : Fin m → ℝ) 1) :
      g ⟨map m j z, hnewcell j z⟩ = G j z := by
    by_cases hz : (z : Fin m → ℝ) ∈ sphere 0 1
    · have ha : map m j z ∈ A := cellFrontier_subset_skeletonLT m j ⟨z, hz, rfl⟩
      exact (hgold ⟨map m j z, ha⟩).trans (hG j ⟨z.val, hz⟩).symm
    · have hzball : z.val ∈ ball (0 : Fin m → ℝ) 1 := by
        rw [mem_ball_zero_iff]
        exact lt_of_le_of_ne (mem_closedBall_zero_iff.mp z.property)
          (fun h => hz (mem_sphere_zero_iff_norm.mpr h))
      let x : B := ⟨map m j z, hnewcell j z⟩
      have hxcell : x.val ∈ openCell m j := ⟨z, hzball, rfl⟩
      have hx : x.val ∉ A :=
        (disjoint_skeletonLT_openCell (C := C) (j := j) le_rfl).notMem_of_mem_right hxcell
      have hxnew : x.val ∈ openCell m (jnew x hx) :=
        ⟨znew x hx, (znew x hx).property, hcoord x hx⟩
      have hj : jnew x hx = j := by
        by_contra hne
        exact (disjoint_openCell_of_ne (C := C) (by simpa using hne)).notMem_of_mem_left
          hxnew hxcell
      have hcoords : (znew x hx).val = z.val := by
        apply (map m j).injOn
        · rw [source_eq]
          exact (znew x hx).property
        · rw [source_eq]
          exact hzball
        · simpa only [hj] using hcoord x hx
      change g x = G j z
      dsimp only [g]
      rw [dif_neg hx, hj]
      exact congrArg (G j) (Subtype.ext hcoords)
  have hg : Continuous g := by
    apply continuous_of_cw_disks (B : Set X) D g
    · intro k j
      have hk : k < m + 1 := by
        have hk' := j.property
        simp only [B, skeletonLT_I, mem_ofPred_eq] at hk'
        exact_mod_cast hk'
      by_cases hlt : k < m
      · have hmapA (z : closedBall (0 : Fin k → ℝ) 1) : map (C := C) k j.val z ∈ A := by
          apply skeletonLT_mono (show (k + 1 : ℕ∞) ≤ m by exact_mod_cast hlt) ?_
          exact closedCell_subset_skeletonLT k j.val ⟨z, z.property, rfl⟩
        have hc : Continuous (fun z : closedBall (0 : Fin k → ℝ) 1 =>
            (⟨map (C := C) k j.val z, hmapA z⟩ : A)) :=
          ((continuousOn k j.val).domRestrict).subtype_mk _
        exact (f.continuous.comp hc).congr (fun z => (hgold ⟨_, hmapA z⟩).symm)
      · have heq : k = m := by omega
        subst k
        exact (G j.val).continuous.congr (fun z => (hgcell j.val z).symm)
    · have hc : Continuous (fun z : D => (⟨z.val, A.base_subset z.property⟩ : A)) :=
        continuous_subtype_val.subtype_mk _
      exact (f.continuous.comp hc).congr (fun z => (hgold ⟨_, A.base_subset z.property⟩).symm)
  exact ⟨⟨g, hg⟩, hgold, hgcell⟩

end

end Poincare.Topology
