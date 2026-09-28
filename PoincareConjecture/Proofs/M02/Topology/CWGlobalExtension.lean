import PoincareConjecture.Proofs.M02.Topology.CWCellExtension

set_option autoImplicit false

open Set Metric
open scoped Topology

universe u v

namespace PoincareConjecture.Proofs.M02.Topology

noncomputable section

open _root_.Topology.RelCWComplex

theorem exists_cw_extension_from_one_skeleton
    {X : Type u} [TopologicalSpace X] [T2Space X]
    {Y : Type v} [TopologicalSpace Y]
    (C D : Set X) [_root_.Topology.RelCWComplex C D]
    (hpi : ∀ (n : Nat) (y : Y), Subsingleton (HomotopyGroup.Pi (n + 1) Y y))
    (f : C(↥(skeletonLT C 2), Y)) :
    ∃ F : C(C, Y), ∀ x : ↥(skeletonLT C 2),
      F ⟨x.val, (skeletonLT C 2).subset_complex x.property⟩ = f x := by
  classical
  let A (n : Nat) := skeletonLT C (n + 2)
  have hmono {i j : Nat} (hij : i ≤ j) : (A i : Set X) ⊆ A j :=
    skeletonLT_mono (by exact_mod_cast Nat.add_le_add_right hij 2)
  have hstep (n : Nat) (g : C(↥(A n), Y)) :
      ∃ G : C(↥(A (n + 1)), Y), ∀ x : ↥(A n),
        G ⟨x.val, hmono (Nat.le_succ n) x.property⟩ = g x := by
    have heq : (A (n + 1) : Set X) = skeletonLT C (n + 3) := by
      dsimp only [A]
      rw [ENat.natCast_add, ENat.natCast_one, add_assoc]
      rfl
    let e : ↥(A (n + 1)) ≃ₜ ↥(skeletonLT C (n + 3)) := Homeomorph.setCongr heq
    obtain ⟨G, hG⟩ := exists_cw_skeleton_extension C D n (hpi n) g
    refine ⟨G.comp (e : C(_, _)), fun x => ?_⟩
    exact (congrArg G (Subtype.ext rfl)).trans (hG x)
  choose next hnext using hstep
  let F : ∀ n : Nat, C(↥(A n), Y) := Nat.rec f (fun n g => next n g)
  have hcompat {i j : Nat} (hij : i ≤ j) (x : ↥(A i)) :
      F j ⟨x.val, hmono hij x.property⟩ = F i x := by
    induction j, hij using Nat.le_induction with
    | base => exact congrArg (F i) (Subtype.ext rfl)
    | succ j hij ih =>
      exact (hnext j (F j) ⟨x.val, hmono hij x.property⟩).trans ih
  have hexists (x : C) : ∃ n : Nat, x.val ∈ A n := by
    have hx : x.val ∈ D ∪ ⋃ (m : Nat) (j : cell C m), closedCell m j := by
      simpa only [_root_.Topology.RelCWComplex.union] using x.property
    rcases hx with hxD | hx
    · exact ⟨0, (A 0).base_subset hxD⟩
    · obtain ⟨m, hm⟩ := mem_iUnion.mp hx
      obtain ⟨j, hxj⟩ := mem_iUnion.mp hm
      refine ⟨m, skeletonLT_mono (show (m + 1 : ℕ∞) ≤ m + 2 by norm_num) ?_⟩
      exact closedCell_subset_skeletonLT m j hxj
  choose stage hstage using hexists
  let g (x : C) : Y := F (stage x) ⟨x.val, hstage x⟩
  have hstage_eq (n : Nat) (x : ↥(A n)) :
      g ⟨x.val, (A n).subset_complex x.property⟩ = F n x := by
    let c : C := ⟨x.val, (A n).subset_complex x.property⟩
    have ha := hcompat (Nat.le_max_left (stage c) n) ⟨c.val, hstage c⟩
    have hb := hcompat (Nat.le_max_right (stage c) n) x
    exact ha.symm.trans hb
  have hg : Continuous g := by
    apply continuous_of_cw_disks C D g
    · intro m j
      have hmap (z : closedBall (0 : Fin m → ℝ) 1) : map m j z ∈ A m := by
        apply skeletonLT_mono (show (m + 1 : ℕ∞) ≤ m + 2 by norm_num) ?_
        exact closedCell_subset_skeletonLT m j ⟨z, z.property, rfl⟩
      have hc : Continuous (fun z : closedBall (0 : Fin m → ℝ) 1 =>
          (⟨map m j z, hmap z⟩ : ↥(A m))) :=
        ((continuousOn m j).domRestrict).subtype_mk _
      exact ((F m).continuous.comp hc).congr (fun z => (hstage_eq m ⟨_, hmap z⟩).symm)
    · have hc : Continuous (fun z : D => (⟨z.val, (A 0).base_subset z.property⟩ : ↥(A 0))) :=
        continuous_subtype_val.subtype_mk _
      exact ((F 0).continuous.comp hc).congr
        (fun z => (hstage_eq 0 ⟨_, (A 0).base_subset z.property⟩).symm)
  exact ⟨⟨g, hg⟩, hstage_eq 0⟩

end

end PoincareConjecture.Proofs.M02.Topology
