import PoincareConjecture.Proofs.M02.Topology.SphereDiskExtension
import Mathlib.Topology.CWComplex.Classical.Subcomplex









set_option autoImplicit false

open Set Metric
open scoped Topology

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

open _root_.Topology.RelCWComplex


theorem continuous_of_cw_disks
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y]
    (C D : Set X) [_root_.Topology.RelCWComplex C D]
    (f : C → Y)
    (hcells : ∀ (n : Nat) (j : cell C n),
      Continuous (fun z : closedBall (0 : Fin n → ℝ) 1 =>
        f ⟨map n j z, closedCell_subset_complex n j ⟨z, z.property, rfl⟩⟩))
    (hbase : Continuous (fun z : D => f ⟨z, base_subset_complex z.property⟩)) :
    Continuous f := by
  apply continuous_iff_isClosed.mpr
  intro T hT
  let W : Set X := Subtype.val '' (f ⁻¹' T)
  have hWC : W ⊆ C := by rintro x ⟨z, _, rfl⟩; exact z.property
  have hW : IsClosed W := by
    apply (_root_.Topology.RelCWComplex.closed C W hWC).mpr
    constructor
    · intro n j
      let d : C(closedBall (0 : Fin n → ℝ) 1, X) :=
        ⟨fun z => map n j z, (continuousOn n j).domRestrict⟩
      let c (z : closedBall (0 : Fin n → ℝ) 1) : C :=
        ⟨d z, closedCell_subset_complex n j ⟨z, z.property, rfl⟩⟩
      have heq : d '' ((f ∘ c) ⁻¹' T) = W ∩ closedCell n j := by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨⟨c z, hz, rfl⟩, ⟨z, z.property, rfl⟩⟩
        · rintro ⟨⟨w, hw, hwx⟩, ⟨z, hz, hzx⟩⟩
          refine ⟨⟨z, hz⟩, ?_, hzx⟩
          have hcw : c ⟨z, hz⟩ = w := Subtype.ext (hzx.trans hwx.symm)
          change f (c ⟨z, hz⟩) ∈ T
          rw [hcw]
          exact hw
      rw [← heq]
      exact ((hT.preimage (hcells n j)).isCompact.image d.continuous).isClosed
    · let b (z : D) : C := ⟨z, base_subset_complex z.property⟩
      have heq : Subtype.val '' ((f ∘ b) ⁻¹' T) = W ∩ D := by
        ext x
        constructor
        · rintro ⟨z, hz, rfl⟩
          exact ⟨⟨b z, hz, rfl⟩, z.property⟩
        · rintro ⟨⟨w, hw, hwx⟩, hxD⟩
          refine ⟨⟨x, hxD⟩, ?_, rfl⟩
          have hbw : b ⟨x, hxD⟩ = w := Subtype.ext hwx.symm
          change f (b ⟨x, hxD⟩) ∈ T
          rw [hbw]
          exact hw
      rw [← heq]
      exact (isClosedBase C).isClosedMap_subtype_val _ (hT.preimage hbase)
  have hpre : Subtype.val ⁻¹' W = f ⁻¹' T :=
    preimage_image_eq _ Subtype.val_injective
  rw [← hpre]
  exact hW.preimage continuous_subtype_val


theorem exists_cw_skeleton_extension
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y]
    (C D : Set X) [_root_.Topology.RelCWComplex C D] (n : Nat)
    (hpi : ∀ y : Y, Subsingleton (HomotopyGroup.Pi (n + 1) Y y))
    (f : C(↥(skeletonLT C (n + 2)), Y)) :
    ∃ F : C(↥(skeletonLT C (n + 3)), Y),
      ∀ x : ↥(skeletonLT C (n + 2)),
        F ⟨x.val, skeletonLT_mono (by norm_num) x.property⟩ = f x := by
  classical
  let A := skeletonLT C (n + 2)
  let B := skeletonLT C (n + 3)
  have hAB : (A : Set X) ⊆ B := skeletonLT_mono (by norm_num)
  have hfront (j : cell C (n + 2)) (z : sphere (0 : Fin (n + 2) → ℝ) 1) :
      map (n + 2) j z ∈ A := cellFrontier_subset_skeletonLT (n + 2) j ⟨z, z.property, rfl⟩
  let b (j : cell C (n + 2)) : C(sphere (0 : Fin (n + 2) → ℝ) 1, Y) :=
    f.comp ⟨fun z => ⟨map (n + 2) j z, hfront j z⟩,
      (((continuousOn (n + 2) j).mono sphere_subset_closedBall).domRestrict).subtype_mk _⟩
  have hfill (j : cell C (n + 2)) := exists_characteristic_disk_extension n hpi (b j)
  choose G hG using hfill
  have hnew (x : B) (hx : x.val ∉ A) :
      ∃ (j : cell C (n + 2)) (z : ball (0 : Fin (n + 2) → ℝ) 1),
        map (n + 2) j z = x.val := by
    rcases mem_skeletonLT_iff.mp x.property with hD | ⟨m, hm, j, hxj⟩
    · exact (hx (A.base_subset hD)).elim
    · have hmn : m < n + 3 := by exact_mod_cast hm
      by_cases hmk : m < n + 2
      · apply (hx ?_).elim
        exact mem_skeletonLT_iff.mpr (Or.inr ⟨m, by exact_mod_cast hmk, j, hxj⟩)
      · have hmeq : m = n + 2 := by omega
        subst m
        obtain ⟨z, hz, hzx⟩ := hxj
        exact ⟨j, ⟨z, hz⟩, hzx⟩
  choose jnew znew hcoord using hnew
  let g (x : B) : Y :=
    if hx : x.val ∈ A then f ⟨x.val, hx⟩ else
      G (jnew x hx) ⟨(znew x hx).val, ball_subset_closedBall (znew x hx).property⟩
  have hgold (x : A) : g ⟨x.val, hAB x.property⟩ = f x := by
    simp only [g, dif_pos x.property]
    exact congrArg f (Subtype.ext rfl)
  have hnewcell (j : cell C (n + 2)) (z : closedBall (0 : Fin (n + 2) → ℝ) 1) :
      map (n + 2) j z ∈ B := closedCell_subset_skeletonLT (n + 2) j ⟨z, z.property, rfl⟩
  have hgcell (j : cell C (n + 2)) (z : closedBall (0 : Fin (n + 2) → ℝ) 1) :
      g ⟨map (n + 2) j z, hnewcell j z⟩ = G j z := by
    by_cases hz : (z : Fin (n + 2) → ℝ) ∈ sphere 0 1
    · have ha := hfront j ⟨z.val, hz⟩
      rw [show g ⟨map (n + 2) j z, hnewcell j z⟩ =
        f ⟨map (n + 2) j z, ha⟩ from hgold ⟨map (n + 2) j z, ha⟩]
      exact (hG j ⟨z.val, hz⟩).symm
    · have hzball : z.val ∈ ball (0 : Fin (n + 2) → ℝ) 1 := by
        rw [mem_ball_zero_iff]
        exact lt_of_le_of_ne (mem_closedBall_zero_iff.mp z.property)
          (fun h => hz (mem_sphere_zero_iff_norm.mpr h))
      let x : B := ⟨map (n + 2) j z, hnewcell j z⟩
      have hxcell : x.val ∈ openCell (n + 2) j := ⟨z, hzball, rfl⟩
      have hx : x.val ∉ A :=
        (disjoint_skeletonLT_openCell (C := C) (j := j) (by simp)).notMem_of_mem_right hxcell
      have hxnew : x.val ∈ openCell (n + 2) (jnew x hx) :=
        ⟨znew x hx, (znew x hx).property, hcoord x hx⟩
      have hj : jnew x hx = j := by
        by_contra hne
        exact (disjoint_openCell_of_ne (C := C) (by simpa using hne)).notMem_of_mem_left
          hxnew hxcell
      have hcoords : (znew x hx).val = z.val := by
        apply (map (n + 2) j).injOn
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
    · intro m j
      have hm : m < n + 3 := by
        have hm' := j.property
        simp only [B, skeletonLT_I, mem_ofPred_eq] at hm'
        exact_mod_cast hm'
      by_cases hmk : m < n + 2
      · have hmapA (z : closedBall (0 : Fin m → ℝ) 1) : map (C := C) m j.val z ∈ A := by
          apply skeletonLT_mono (show (m + 1 : ℕ∞) ≤ n + 2 by exact_mod_cast hmk) ?_
          exact closedCell_subset_skeletonLT m j.val ⟨z, z.property, rfl⟩
        have hc : Continuous (fun z : closedBall (0 : Fin m → ℝ) 1 =>
            (⟨map (C := C) m j.val z, hmapA z⟩ : A)) :=
          ((continuousOn m j.val).domRestrict).subtype_mk _
        exact (f.continuous.comp hc).congr (fun z => (hgold ⟨_, hmapA z⟩).symm)
      · have heq : m = n + 2 := by omega
        subst m
        exact (G j.val).continuous.congr (fun z => (hgcell j.val z).symm)
    · have hc : Continuous (fun z : D => (⟨z.val, A.base_subset z.property⟩ : A)) :=
        continuous_subtype_val.subtype_mk _
      exact (f.continuous.comp hc).congr (fun z => (hgold ⟨_, A.base_subset z.property⟩).symm)
  exact ⟨⟨g, hg⟩, hgold⟩

end

end PoincareConjecture.Proofs.M02.Topology
