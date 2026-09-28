import PoincareConjecture.Proofs.Horizon.Topology.Gluing.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology

universe u v

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} {X : Type v} {Y : ι → Type v}
  [TopologicalSpace X] [∀ i, TopologicalSpace (Y i)]

abbrev Piece (X : Type v) (Y : ι → Type v) : Option ι → Type v
  | none => X
  | some i => Y i

instance pieceTopology (i : Option ι) : TopologicalSpace (Piece X Y i) := by
  cases i <;> exact inferInstance

variable (e : ∀ i, OpenPartialHomeomorph X (Y i))

def capTransition (i j : ι) : OpenPartialHomeomorph (Y i) (Y j) := by
  classical
  exact if h : i = j then by subst j; exact OpenPartialHomeomorph.refl (Y i)
  else (e i).symm.trans (e j)

def transition : ∀ i j : Option ι, OpenPartialHomeomorph (Piece X Y i) (Piece X Y j)
  | none, none => OpenPartialHomeomorph.refl X
  | none, some j => e j
  | some i, none => (e i).symm
  | some i, some j => capTransition e i j

@[simp] theorem capTransition_self (i : ι) :
    capTransition e i i = OpenPartialHomeomorph.refl (Y i) := by
  simp [capTransition]

theorem capTransition_inverse (i j : ι) :
    capTransition e j i = (capTransition e i j).symm := by
  by_cases h : i = j
  · subst j; simp
  · simp [capTransition, h, Ne.symm h, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]

variable (hd : Pairwise (fun i j => Disjoint (e i).source (e j).source))

include hd in
theorem capTransition_source_empty {i j : ι} (h : i ≠ j) :
    (capTransition e i j).source = ∅ := by
  rw [capTransition, dif_neg h]
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  exact Set.disjoint_left.mp (hd h) ((e i).map_target hx.1) hx.2

def overlaps : Poincare.Gluing.OverlapSystem (Piece X Y) where
  transition := transition e
  self := by
    intro i
    cases i <;> simp [transition]
  inverse := by
    intro i j
    cases i <;> cases j
    all_goals first | rfl | exact capTransition_inverse e _ _
  comp_source := by
    intro i j k x hx hy
    cases i with
    | none =>
      cases j with
      | none => exact hy
      | some j =>
        cases k with
        | none => exact mem_univ _
        | some k =>
          by_cases h : j = k
          · subst k; exact hx
          · exact False.elim (by
              change e j x ∈ (capTransition e j k).source at hy
              rw [capTransition_source_empty e hd h] at hy
              exact hy)
    | some i =>
      cases j with
      | none =>
        cases k with
        | none => exact hx
        | some k =>
          by_cases h : i = k
          · subst k; simp [transition]
          · exact False.elim (Set.disjoint_left.mp (hd h) ((e i).map_target hx) hy)
      | some j =>
        by_cases h : i = j
        · subst j
          simpa [transition] using hy
        · exact False.elim (by
            change x ∈ (capTransition e i j).source at hx
            rw [capTransition_source_empty e hd h] at hx
            exact hx)
  comp_apply := by
    intro i j k x hx hy
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j =>
        cases k with
        | none => exact (e j).left_inv hx
        | some k =>
          by_cases h : j = k
          · subst k; simp [transition]
          · exact False.elim (by
              change e j x ∈ (capTransition e j k).source at hy
              rw [capTransition_source_empty e hd h] at hy
              exact hy)
    | some i =>
      cases j with
      | none =>
        cases k with
        | none => rfl
        | some k =>
          by_cases h : i = k
          · subst k
            simpa [transition] using (e i).right_inv hx
          · exact False.elim (Set.disjoint_left.mp (hd h) ((e i).map_target hx) hy)
      | some j =>
        by_cases h : i = j
        · subst j; simp [transition]
        · exact False.elim (by
            change x ∈ (capTransition e i j).source at hx
            rw [capTransition_source_empty e hd h] at hx
            exact hx)

end PoincareConjecture.Surgery.Terminal.Gluing
