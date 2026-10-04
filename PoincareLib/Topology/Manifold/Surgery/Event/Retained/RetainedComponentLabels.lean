import PoincareLib.Topology.Manifold.Surgery.Event.Retained.RetainedAnnuli
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Extending retained component labels across actual caps

The cap complement and actual extended ball charts cover the post-slice.
Their component labels agree on every overlap, so the existing continuous
open-cover gluing API supplies a label on the entire actual post-slice.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier] (P : ∀ i, EventCapCoordinates F T hT i)

/-- The exact retained complement together with the actual full ball charts. -/
def retainedPatch : Option (Fin (F.event T hT).cap_count) →
    TopologicalSpace.Opens (F.slice T).carrier
  | none => eventCapComplementOpen F T hT
  | some i => ⟨(P i).ball.map '' Metric.ball 0 2, (P i).ball_patch_open⟩

/-- Old points retain their component label; each cap patch has the
constant label of its own connected retained annulus. -/
noncomputable def retainedPatchLabel (j : Option (Fin (F.event T hT).cap_count)) :
    C(retainedPatch F T hT P j, ConnectedComponents (eventCapComplementOpen F T hT)) :=
  match j with
  | none => ⟨ConnectedComponents.mk, ConnectedComponents.continuous_coe⟩
  | some i => ContinuousMap.const _ (ConnectedComponents.mk (P i).retainedAnnularPoint)

/-- Every patch label agrees with the actual old component on its
intersection with the retained complement. -/
theorem retainedPatchLabel_on_complement (j : Option (Fin (F.event T hT).cap_count))
    (x : (F.slice T).carrier) (hxj : x ∈ retainedPatch F T hT P j)
    (hx : x ∈ eventCapComplementOpen F T hT) :
    retainedPatchLabel F T hT P j ⟨x, hxj⟩ = ConnectedComponents.mk ⟨x, hx⟩ := by
  cases j with
  | none => rfl
  | some i => exact ((P i).retained_annulus_component_eq ⟨x, hx⟩ hxj).symm

/-- Any overlap between two distinct full ball patches is outside all
closed caps. The extended patches need not be assumed disjoint. -/
theorem retained_ball_overlap (i j : Fin (F.event T hT).cap_count) (hij : i ≠ j)
    (x : (F.slice T).carrier)
    (hxi : x ∈ retainedPatch F T hT P (some i))
    (hxj : x ∈ retainedPatch F T hT P (some j)) :
    x ∈ eventCapComplementOpen F T hT := by
  by_contra hnot
  have hcap (k : Fin (F.event T hT).cap_count)
      (hxk : x ∈ retainedPatch F T hT P (some k)) :
      x ∈ ((F.event T hT).caps k).carrier := by
    obtain ⟨z, hz, rfl⟩ := hxk
    have hle : ‖z‖ ≤ 1 := by
      by_contra h
      exact hnot (((P k).ball_mem_cap_complement_iff hz).mpr (lt_of_not_ge h))
    rw [← (P k).ball_closedBall]
    exact ⟨z, by simpa only [Metric.mem_closedBall, dist_zero_right] using hle, rfl⟩
  exact Set.disjoint_left.mp ((F.event T hT).cap_disjoint i j hij)
    (hcap i hxi) (hcap j hxj)

/-- The actual patch labels agree pairwise on their complete intersections. -/
theorem retainedPatchLabel_agree (j k : Option (Fin (F.event T hT).cap_count))
    (x : (F.slice T).carrier) (hxj : x ∈ retainedPatch F T hT P j)
    (hxk : x ∈ retainedPatch F T hT P k) :
    retainedPatchLabel F T hT P j ⟨x, hxj⟩ =
      retainedPatchLabel F T hT P k ⟨x, hxk⟩ := by
  by_cases hx : x ∈ eventCapComplementOpen F T hT
  · rw [retainedPatchLabel_on_complement F T hT P j x hxj hx,
      retainedPatchLabel_on_complement F T hT P k x hxk hx]
  · cases j with
    | none => exact (hx hxj).elim
    | some i =>
        cases k with
        | none => exact (hx hxk).elim
        | some j =>
            by_cases hij : i = j
            · subst j
              rfl
            · exact (hx (retained_ball_overlap F T hT P i j hij x hxj hxk)).elim

/-- These actual open patches contain a neighborhood of every post-slice
point, even when the event has no cap indices. -/
theorem retainedPatch_cover (x : (F.slice T).carrier) :
    ∃ j, (retainedPatch F T hT P j : Set (F.slice T).carrier) ∈ 𝓝 x := by
  by_cases hx : x ∈ eventCapComplementOpen F T hT
  · exact ⟨none, (eventCapComplementOpen F T hT).isOpen.mem_nhds hx⟩
  · have hcaps : x ∈ ⋃ i, ((F.event T hT).caps i).carrier := by
      by_contra h
      exact hx h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hcaps
    rw [← (P i).ball_closedBall] at hi
    obtain ⟨z, hz, rfl⟩ := hi
    refine ⟨some i, (P i).ball_patch_open.mem_nhds ?_⟩
    exact ⟨z, Metric.closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hz, rfl⟩

/-- The continuous old-component label on the literal post-surgery slice. -/
noncomputable def postRetainedComponentLabel :
    C((F.slice T).carrier, ConnectedComponents (eventCapComplementOpen F T hT)) :=
  ContinuousMap.liftCover (fun j => retainedPatch F T hT P j)
    (retainedPatchLabel F T hT P) (retainedPatchLabel_agree F T hT P)
    (retainedPatch_cover F T hT P)

/-- On the retained complement the descended label is exactly its own
component quotient map. -/
theorem postRetainedComponentLabel_old (x : eventCapComplementOpen F T hT) :
    postRetainedComponentLabel F T hT P x.val = ConnectedComponents.mk x :=
  ContinuousMap.liftCover_coe
    (S := fun j : Option (Fin (F.event T hT).cap_count) =>
      (retainedPatch F T hT P j : Set (F.slice T).carrier))
    (φ := retainedPatchLabel F T hT P)
    (hφ := retainedPatchLabel_agree F T hT P) (hS := retainedPatch_cover F T hT P)
    (i := (none : Option (Fin (F.event T hT).cap_count))) x

/-- On each whole cap patch the descended label is that of its actual
nonempty retained annulus. -/
theorem postRetainedComponentLabel_cap (i : Fin (F.event T hT).cap_count)
    (x : (F.slice T).carrier) (hx : x ∈ (P i).ball.map '' Metric.ball 0 2) :
    postRetainedComponentLabel F T hT P x =
      ConnectedComponents.mk (P i).retainedAnnularPoint :=
  ContinuousMap.liftCover_coe (i := some i) ⟨x, hx⟩

end PoincareMT.M38
