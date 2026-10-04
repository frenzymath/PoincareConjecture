import PoincareLib.Topology.Gluing.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Overlaps for the discarded-side cap patches

Each patch maps partially to the old discarded interior. Distinct patches
are identified exactly where those maps agree; each whole patch retains
its diagonal identity, including the interiors of the added balls.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u v w

namespace PoincareMT.M38

variable {I : Type u} {P : I → Type v} {O : Type w}
  [∀ i, TopologicalSpace (P i)] [TopologicalSpace O]

/-- Patch changes use the common old interior, with the whole diagonal
retained so that a cap's new interior is not removed from the quotient. -/
noncomputable def cappingTransition (e : ∀ i, OpenPartialHomeomorph (P i) O)
    (i j : I) : OpenPartialHomeomorph (P i) (P j) := by
  classical
  exact if h : i = j then h ▸ OpenPartialHomeomorph.refl (P i)
    else (e i).trans (e j).symm

/-- The whole patch, including the new cap interior, has identity overlap
with itself. -/
@[simp] theorem cappingTransition_self (e : ∀ i, OpenPartialHomeomorph (P i) O)
    (i : I) : cappingTransition e i i = OpenPartialHomeomorph.refl (P i) := by
  simp [cappingTransition]

/-- Away from the diagonal, identification means equality of the two
defined old-interior images. Both source conditions are retained. -/
theorem cappingTransition_graph (e : ∀ i, OpenPartialHomeomorph (P i) O)
    {i j : I} (hij : i ≠ j) (x : P i) (y : P j) :
    (x ∈ (cappingTransition e i j).source ∧ cappingTransition e i j x = y) ↔
      x ∈ (e i).source ∧ y ∈ (e j).source ∧ e i x = e j y := by
  simp only [cappingTransition, dif_neg hij, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.trans_apply, OpenPartialHomeomorph.symm_source]
  constructor
  · rintro ⟨⟨hx, hxy⟩, rfl⟩
    exact ⟨hx, (e j).map_target hxy, ((e j).right_inv hxy).symm⟩
  · rintro ⟨hx, hy, hxy⟩
    refine ⟨⟨hx, ?_⟩, ?_⟩
    · change e i x ∈ (e j).target
      rw [hxy]
      exact (e j).map_source hy
    rw [hxy, (e j).left_inv hy]

/-- Partial maps to the actual discarded interior define a consistent
overlap system on all the old and newly attached patches. -/
noncomputable def cappingOverlap (e : ∀ i, OpenPartialHomeomorph (P i) O) :
    Poincare.Gluing.OverlapSystem P where
  transition := cappingTransition e
  self := fun i => by simp [cappingTransition]
  inverse := by
    intro i j
    by_cases hij : i = j
    · subst j
      simp [cappingTransition]
    · simp [cappingTransition, hij, Ne.symm hij,
        OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
  comp_source := by
    intro i j k x hx hy
    by_cases hij : i = j
    · subst j
      simpa only [cappingTransition_self,
        OpenPartialHomeomorph.refl_apply, id_eq] using hy
    by_cases hjk : j = k
    · subst k
      exact hx
    by_cases hik : i = k
    · subst k
      simp [cappingTransition]
    have hxy := (cappingTransition_graph e hij x (cappingTransition e i j x)).mp
      ⟨hx, rfl⟩
    have hyz := (cappingTransition_graph e hjk (cappingTransition e i j x)
      (cappingTransition e j k (cappingTransition e i j x))).mp ⟨hy, rfl⟩
    exact ((cappingTransition_graph e hik x _).mpr
      ⟨hxy.1, hyz.2.1, hxy.2.2.trans hyz.2.2⟩).1
  comp_apply := by
    intro i j k x hx hy
    by_cases hij : i = j
    · subst j
      simp [cappingTransition]
    by_cases hjk : j = k
    · subst k
      simp [cappingTransition]
    have hxy := (cappingTransition_graph e hij x (cappingTransition e i j x)).mp
      ⟨hx, rfl⟩
    have hyz := (cappingTransition_graph e hjk (cappingTransition e i j x)
      (cappingTransition e j k (cappingTransition e i j x))).mp ⟨hy, rfl⟩
    by_cases hik : i = k
    · subst k
      simpa only [cappingTransition_self,
        OpenPartialHomeomorph.refl_apply, id_eq] using
        (e i).injOn hyz.2.1 hxy.1 (hxy.2.2.trans hyz.2.2).symm
    · exact ((cappingTransition_graph e hik x _).mpr
        ⟨hxy.1, hyz.2.1, hxy.2.2.trans hyz.2.2⟩).2.symm

end PoincareMT.M38
