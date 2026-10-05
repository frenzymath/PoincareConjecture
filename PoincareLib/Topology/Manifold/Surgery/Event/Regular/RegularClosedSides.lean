import PoincareLib.Topology.Manifold.Surgery.Event.Event.EventCollars

/-!
# The two closed sides of an actual finite surgery cut

The negative event half-collar approaches every point of its central
sphere. Since these are precisely the retained frontier, the retained
region is the closure of its interior. The discarded closed side therefore
has exactly the same frontier, with no additional boundary components.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M38

variable (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
  [Nonempty (F.slice T).carrier]

/-- The actual central sphere is approached from the retained open collar. -/
theorem event_collar_center_mem_closure_retained
    (i : Fin (F.event T hT).cap_count) (z : UnitTwoSphere) :
    eventCollarMap F T hT i (z, 0) ∈ closure (interior (F.event T hT).retained_pre) := by
  let V : Set RoundCylinderSpace := Set.univ ×ˢ Set.Ioo (-(1 / 2) : ℝ) 0
  have hclosure : closure V = Set.univ ×ˢ Set.Icc (-(1 / 2) : ℝ) 0 := by
    dsimp only [V]
    rw [closure_prod_eq, closure_univ, closure_Ioo (by norm_num)]
  have hsub : closure V ⊆ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := by
    rw [hclosure]
    intro p hp
    exact ⟨hp.1, by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hzero : (z, 0) ∈ closure V := by
    rw [hclosure]
    exact ⟨Set.mem_univ z, by norm_num, le_rfl⟩
  have himage : eventCollarMap F T hT i (z, 0) ∈
      closure (eventCollarMap F T hT i '' V) :=
    ((event_collar_smooth F T hT i).continuousOn.mono hsub).image_closure
      (Set.mem_image_of_mem _ hzero)
  apply closure_mono (show eventCollarMap F T hT i '' V ⊆
    interior (F.event T hT).retained_pre from ?_) himage
  apply Set.Subset.trans (Set.image_mono ?_) (event_collar_negative_retained F T hT i)
  intro p hp
  exact ⟨hp.1, by linarith [hp.2.1], hp.2.2⟩

/-- The stored retained region has no points isolated from its interior. -/
theorem event_retained_closure_interior :
    closure (interior (F.event T hT).retained_pre) = (F.event T hT).retained_pre := by
  apply ((F.event T hT).retained_pre_compact.isClosed.closure_interior_subset).antisymm
  intro x hx
  by_cases hi : x ∈ interior (F.event T hT).retained_pre
  · exact subset_closure hi
  have hboundary : x ∈ frontier (F.event T hT).retained_pre := by
    rw [(F.event T hT).retained_pre_compact.isClosed.frontier_eq]
    exact ⟨hx, hi⟩
  rw [(F.event T hT).pre_boundary] at hboundary
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hboundary
  rw [← event_collar_central F T hT i] at hi
  obtain ⟨⟨z, s⟩, ⟨_, hs⟩, rfl⟩ := hi
  have hs0 : s = 0 := hs
  subst s
  exact event_collar_center_mem_closure_retained F T hT i z

/-- The discarded side has precisely the actual retained frontier. -/
theorem event_discarded_frontier :
    frontier (interior (F.event T hT).retained_pre)ᶜ =
      frontier (F.event T hT).retained_pre := by
  rw [frontier_compl]
  simp only [frontier, interior_interior, event_retained_closure_interior,
    (F.event T hT).retained_pre_compact.isClosed.closure_eq]

/-- Its open interior is exactly the complement of the closed retained side. -/
theorem event_discarded_interior :
    interior (interior (F.event T hT).retained_pre)ᶜ = (F.event T hT).retained_preᶜ := by
  rw [interior_compl, event_retained_closure_interior]

/-- Both sides are regular closed sets; this also retains wholly discarded
ambient components without manufacturing boundary spheres for them. -/
theorem event_discarded_closure_interior :
    closure (interior (interior (F.event T hT).retained_pre)ᶜ) =
      (interior (F.event T hT).retained_pre)ᶜ := by
  rw [event_discarded_interior, closure_compl]

end PoincareMT.M38
