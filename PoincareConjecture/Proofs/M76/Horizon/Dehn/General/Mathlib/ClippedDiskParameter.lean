import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Analysis.Normed.Group.Constructions










set_option autoImplicit false

open Set Metric

namespace Geometry

local notation "V2" => (Fin 2 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

theorem clipped_disk_parameter_interior
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : V2 → X) (hf : ContinuousOn f D2)
    (T : OpenPartialHomeomorph X Y) (B J : Set Y) (q : Y → V2)
    (hB : B = T '' (f '' D2 ∩ T.source) ∩ J)
    (hqD : MapsTo q B D2)
    (hright : ∀ z ∈ B, f (q z) ∈ T.source ∧ T (f (q z)) = z)
    (hleft : ∀ x ∈ D2, f x ∈ T.source → T (f x) ∈ J → q (T (f x)) = x)
    (z : Y) (hz : z ∈ B) (hzJ : z ∈ interior J) :
    q z ∈ closure (interior (q '' B)) ∧
      (q z ∈ ball (0 : V2) 1 → q z ∈ interior (q '' B)) := by
  let V := T.source ∩ T ⁻¹' interior J
  have hV : IsOpen V := T.isOpen_inter_preimage isOpen_interior
  have hpre : IsOpen ((fun x : D2 => f x) ⁻¹' V) := hV.preimage hf.domRestrict
  obtain ⟨O, hO, hOpre⟩ := isOpen_induced_iff.mp hpre
  have hpoint : q z ∈ O := by
    have hxV : (⟨q z, hqD hz⟩ : D2) ∈ (fun x : D2 => f x) ⁻¹' V := by
      change f (q z) ∈ V
      refine ⟨(hright z hz).1, ?_⟩
      change T (f (q z)) ∈ interior J
      rw [(hright z hz).2]
      exact hzJ
    exact hOpre.symm.subset hxV
  have hcover : D2 ∩ O ⊆ q '' B := by
    intro x hx
    have hxV : f x ∈ V := hOpre.subset
      (show (⟨x, hx.1⟩ : D2) ∈ Subtype.val ⁻¹' O from hx.2)
    have hcoord : T (f x) ∈ B := hB.symm.subset
      ⟨mem_image_of_mem T ⟨mem_image_of_mem f hx.1, hxV.1⟩, interior_subset hxV.2⟩
    exact ⟨T (f x), hcoord, hleft x hx.1 hxV.1 (interior_subset hxV.2)⟩
  have hlocal : interior D2 ∩ O ⊆ interior (q '' B) :=
    interior_maximal (fun _ hx => hcover ⟨interior_subset hx.1, hx.2⟩)
      (isOpen_interior.inter hO)
  constructor
  · apply closure_mono hlocal
    apply hO.closure_inter
    refine ⟨?_, hpoint⟩
    rw [interior_closedBall _ one_ne_zero, closure_ball _ one_ne_zero]
    exact hqD hz
  · intro hball
    apply hlocal
    rw [interior_closedBall _ one_ne_zero]
    exact ⟨hball, hpoint⟩

end Geometry
