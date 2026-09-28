import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.SourceCollar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimCircles
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.RimComponents



set_option autoImplicit false
open Set Metric BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "D" => closedBall (0 : Fin 1 → ℝ) 1
local notation "C" => AddCircle (4 * (128 : ℝ))



theorem exists_sourceBoundaryCircle_component_collar
    (phi : C(H, H)) (theta : C) (F : (ContinuousMap.id H).HomotopyRel phi B)
    (b : D) (hb : ‖(b : Fin 1 → ℝ)‖ = 1) {S : Set X}
    (hSF : S ⊆ sourceSurface phi theta)
    (hcomponent : ∀ x ∈ S, connectedComponentIn (sourceSurface phi theta) x = S)
    (hbase : (sourceBoundaryCircle phi theta F b hb 0 : X) ∈ S)
    {U : Set (sourceSurface phi theta)} (hU : IsOpen U)
    (c : (↥(sourceSurface phi theta ∩ frontier R) × Ico (0 : ℝ) 1) ≃ₜ U)
    (hcbase : ∀ x, (c (collarBase x) : sourceSurface phi theta) =
      Set.inclusion inter_subset_left x) :
    ∃ V : Set S, IsOpen V ∧
      ∃ d : (C × Ico (0 : ℝ) 1) ≃ₜ V,
        ∀ z, (d (collarBase z) : S) =
          sourceBoundaryCircleInComponent phi theta F b hb hcomponent hbase z := by
  let A := sourceRimCircleCoordinates phi theta F b hb
  let i : C → ↥(sourceSurface phi theta ∩ frontier R) := fun z => (A z).val
  have hi : Topology.IsOpenEmbedding i :=
    (sourceRimCircle_isClopen phi theta F b).isOpen.isOpenEmbedding_subtypeVal.comp
      A.isOpenEmbedding
  let f : (C × Ico (0 : ℝ) 1) → sourceSurface phi theta :=
    fun z => (c (i z.1, z.2)).val
  have hf : Topology.IsOpenEmbedding f :=
    hU.isOpenEmbedding_subtypeVal.comp
      (c.isOpenEmbedding.comp (hi.prodMap (Homeomorph.refl _).isOpenEmbedding))
  have hfbase (z : C) : f (collarBase z) = sourceBoundaryCircle phi theta F b hb z :=
    hcbase (i z)
  let : PathConnectedSpace (Ico (0 : ℝ) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      ((convex_Ico (0 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩)
  let fX : (C × Ico (0 : ℝ) 1) → X := fun z => (f z : X)
  have hfX : Continuous fX := continuous_subtype_val.comp hf.continuous
  have hrange : range fX ⊆ S := by
    have hr := (isPreconnected_range hfX).subset_connectedComponentIn
      (mem_range_self (f := fX) (collarBase (0 : C)))
      (show range fX ⊆ sourceSurface phi theta by
        rintro _ ⟨z, rfl⟩
        exact (f z).property)
    have hzero : fX (collarBase (0 : C)) =
        (sourceBoundaryCircle phi theta F b hb 0 : X) :=
      congrArg Subtype.val (hfbase 0)
    rw [hzero, hcomponent _ hbase] at hr
    exact hr
  let g : (C × Ico (0 : ℝ) 1) → S :=
    fun z => ⟨fX z, hrange (mem_range_self z)⟩
  have hg : Topology.IsEmbedding g :=
    (Topology.IsEmbedding.subtypeVal.comp hf.isEmbedding).codRestrict S
      (fun z => hrange (mem_range_self z))
  have hr : range g = (Set.inclusion hSF) ⁻¹' range f := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, Subtype.ext (congrArg (fun y : sourceSurface phi theta => (y : X)) hz)⟩
  refine ⟨range g, ?_, hg.toHomeomorph, ?_⟩
  · rw [hr]
    exact hf.isOpen_range.preimage (continuous_subtype_val.subtype_mk _)
  · intro z
    apply Subtype.ext
    exact congrArg (fun y : sourceSurface phi theta => (y : X)) (hfbase z)

end PoincareConjecture.M76.HamiltonIntervalTorus
