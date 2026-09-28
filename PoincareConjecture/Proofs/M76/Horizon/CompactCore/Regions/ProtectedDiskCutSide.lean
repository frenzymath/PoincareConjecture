import PoincareConjecture.Proofs.M76.Wall.ActualCutDomains
import Mathlib.Analysis.Convex.Topology

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem PLDomain.protected_disk_lies_on_one_side
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {K Y F : Set X}
    (hK : PLDomain e K) (hcut : Y ∩ frontier K = F)
    {f : V2 → X} (hf : ContinuousOn f D) (hfY : MapsTo f D Y)
    (hproper : ∀ z : D, f z ∈ F ↔ (z : V2) ∈ Q) :
    (MapsTo f D K ∧ MapsTo f (ball (0 : V2) 1) (interior K)) ∨
      (MapsTo f D (interior K)ᶜ ∧ MapsTo f (ball (0 : V2) 1) Kᶜ) := by
  have havoid {z : V2} (hz : z ∈ ball (0 : V2) 1) : f z ∉ frontier K := by
    intro hzF
    have hzD := ball_subset_closedBall hz
    have hF : f z ∈ F := hcut ▸ ⟨hfY hzD, hzF⟩
    have hrim := (hproper ⟨z, hzD⟩).mp hF
    have hlt : dist z 0 < 1 := hz
    have heq : dist z 0 = 1 := hrim
    exact (ne_of_lt hlt) heq
  have hcover : f '' ball (0 : V2) 1 ⊆ interior K ∪ Kᶜ := by
    rintro _ ⟨z, hz, rfl⟩
    by_cases hk : f z ∈ K
    · exact Or.inl ((mem_interior_iff_notMem_frontier hk).mpr (havoid hz))
    · exact Or.inr hk
  have hdisjoint : Disjoint (interior K) Kᶜ := by
    exact Set.disjoint_left.mpr (fun _ hi hc => hc (interior_subset hi))
  have hconn : IsPreconnected (f '' ball (0 : V2) 1) :=
    (convex_ball (0 : V2) 1).isPreconnected.image f (hf.mono ball_subset_closedBall)
  have hrim {z : V2} (hz : z ∈ D) (hout : z ∉ ball (0 : V2) 1) :
      f z ∈ frontier K := by
    have hzQ : z ∈ Q := le_antisymm hz (le_of_not_gt hout)
    exact (hcut.symm ▸ (hproper ⟨z, hz⟩).mpr hzQ).2
  rcases hconn.subset_or_subset isOpen_interior hK.closed.isOpen_compl
      hdisjoint hcover with hinside | houtside
  · refine Or.inl ⟨?_, fun z hz => hinside ⟨z, hz, rfl⟩⟩
    intro z hz
    by_cases hi : z ∈ ball (0 : V2) 1
    · exact interior_subset (hinside ⟨z, hi, rfl⟩)
    · exact hK.closed.frontier_subset (hrim hz hi)
  · refine Or.inr ⟨?_, fun z hz => houtside ⟨z, hz, rfl⟩⟩
    intro z hz hi
    by_cases hzint : z ∈ ball (0 : V2) 1
    · exact houtside ⟨z, hzint, rfl⟩ (interior_subset hi)
    · exact Set.disjoint_left.mp disjoint_interior_frontier hi (hrim hz hzint)

end PoincareConjecture.M76
