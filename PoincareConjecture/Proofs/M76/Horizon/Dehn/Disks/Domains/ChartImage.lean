import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLChartRestriction
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

variable {X ι : Type*} [TopologicalSpace X]



theorem chart_inverse_isOpenEmbedding
    (a : OpenPartialHomeomorph X V3) (U : TopologicalSpace.Opens V3)
    (hU : Nonempty U) (hUT : (U : Set V3) ⊆ a.target) :
    IsOpenEmbedding (fun y : U ↦ a.symm (y : V3)) := by
  let C := a.symm.subtypeRestr hU
  have hsource : C.source = univ := by
    dsimp only [C]
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    ext y
    change (y : V3) ∈ a.target ↔ y ∈ (univ : Set U)
    exact iff_of_true (hUT y.property) (mem_univ y)
  exact C.isOpenEmbedding hsource



theorem frontier_chart_image_eq
    (a : OpenPartialHomeomorph X V3) (U : TopologicalSpace.Opens V3)
    (hU : Nonempty U) (hUT : (U : Set V3) ⊆ a.target) (R : Set X) :
    frontier {y : U | a.symm (y : V3) ∈ R} =
      {y : U | a.symm (y : V3) ∈ frontier R} := by
  have hj := chart_inverse_isOpenEmbedding a U hU hUT
  exact (hj.isOpenMap.preimage_frontier_eq_frontier_preimage hj.continuous R).symm




theorem PLDomain.chart_image
    {e : ι → OpenPartialHomeomorph X V3} {R : Set X} (he : PLDomain e R)
    (i : ι) (U : TopologicalSpace.Opens V3) (hU : Nonempty U)
    (hUT : (U : Set V3) ⊆ (e i).target) :
    PLDomain (fun _ : Unit ↦ U.openPartialHomeomorphSubtypeCoe hU)
      {y : U | (e i).symm (y : V3) ∈ R} := by
  let j := U.openPartialHomeomorphSubtypeCoe hU
  let C := (e i).symm.subtypeRestr hU
  have hCsource : C.source = univ := by
    dsimp only [C]
    rw [OpenPartialHomeomorph.subtypeRestr_source]
    ext y
    change (y : V3) ∈ (e i).target ↔ y ∈ (univ : Set U)
    exact iff_of_true (hUT y.property) (mem_univ y)
  have hCopen := chart_inverse_isOpenEmbedding (e i) U hU hUT
  refine ⟨fun y ↦ ⟨(), mem_univ y⟩, ?_, he.closed.preimage hCopen.continuous, ?_⟩
  · intro _ _
    exact j.self_transition_mem_piecewiseAffineGroupoid
  · intro x hx
    have hxold : (e i).symm (x : V3) ∈ frontier R :=
      (frontier_chart_image_eq (e i) U hU hUT R).subset hx
    obtain ⟨ell, v, B, hv, hxB, hzero, hB, hhalf⟩ := he.halfspace _ hxold
    let D := C.trans B
    have hxC : x ∈ C.source := hCsource.symm ▸ mem_univ x
    refine ⟨ell, v, D, hv, ⟨hxC, hxB⟩, hzero, ?_, ?_⟩
    · intro _
      apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
      have hPL := (mem_piecewiseAffineGroupoid_iff_forward _).mp (hB i)
      have hsource : (j.symm.trans D).source ⊆ ((e i).symm.trans B).source := by
        intro z hz
        have hzval : ((j.symm z : U) : V3) = z := j.right_inv hz.1
        refine ⟨?_, ?_⟩
        · apply hUT
          exact hzval ▸ (j.symm z).property
        have hh := hz.2.2
        change (e i).symm ((j.symm z : U) : V3) ∈ B.source at hh
        rwa [hzval] at hh
      apply (hPL.mono (j.symm.trans D).open_source hsource).congr
      intro z hz
      have hzval : ((j.symm z : U) : V3) = z := j.right_inv hz.1
      change B ((e i).symm z) = B ((e i).symm ((j.symm z : U) : V3))
      rw [hzval]
    · intro y hy
      exact hhalf ((e i).symm (y : V3)) hy.2

end PoincareConjecture.M76
