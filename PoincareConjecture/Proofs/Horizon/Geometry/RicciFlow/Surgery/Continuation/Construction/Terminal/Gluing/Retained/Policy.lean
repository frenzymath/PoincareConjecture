import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CutTopology
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Gluing.Retained.Identification

noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Surgery.Terminal.Gluing

variable {ι : Type u} [Finite ι] {S : GeneralizedSliceCarrier.{u}}
  {g : RiemannianMetric 3 S.carrier} {K : MetricSurgeryConstants}
  {g₀ : StandardInitialMetric} (D : LeviCivitaData g) (rho : ℝ)
  (I : ι → MetricSurgeryInput K g) (cuts : ∀ i, SurgeryEndCut (I i).neck)

def policyRetainedOpen : Opens S.carrier :=
  ⟨SurgeryTerminalCoreComponents D rho \ ⋃ i, closure (cuts i).tail,
    (SurgeryTerminalCoreComponents.isClopen D rho).isOpen.inter
      (isClosed_iUnion_of_finite fun _ => isClosed_closure).isOpen_compl⟩

theorem closure_policyRetainedOpen_subset :
    closure (policyRetainedOpen D rho I cuts : Set S.carrier) ⊆
      SurgeryTerminalCoreComponents D rho \ ⋃ i, (cuts i).tail := by
  apply closure_minimal
  · intro x hx
    refine ⟨hx.1, ?_⟩
    intro ht
    obtain ⟨i, hi⟩ := mem_iUnion.mp ht
    exact hx.2 (mem_iUnion.mpr ⟨i, subset_closure hi⟩)
  · exact (SurgeryTerminalCoreComponents.isClopen D rho).isClosed.inter
      (isOpen_iUnion fun i => (cuts i).tail_isOpen).isClosed_compl

theorem policyRetainedOpen_disjoint_central (i : ι) :
    Disjoint (policyRetainedOpen D rho I cuts : Set S.carrier) (I i).neck.central_sphere := by
  apply disjoint_left.mpr
  intro x hx hs
  exact hx.2 (mem_iUnion.mpr ⟨i, frontier_subset_closure ((cuts i).frontier_eq.symm ▸ hs)⟩)

theorem frontier_policyRetainedOpen_subset :
    frontier (policyRetainedOpen D rho I cuts : Set S.carrier) ⊆
      ⋃ i, (I i).neck.central_sphere := by
  intro x hx
  have hK := closure_policyRetainedOpen_subset D rho I cuts hx.1
  have hxU : x ∉ policyRetainedOpen D rho I cuts := by
    intro h
    exact hx.2 (mem_interior_iff_mem_nhds.mpr
      ((policyRetainedOpen D rho I cuts).isOpen.mem_nhds h))
  have hcl : x ∈ ⋃ i, closure (cuts i).tail := not_not.mp (fun hn => hxU ⟨hK.1, hn⟩)
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcl
  rw [(cuts i).closure_tail] at hi
  exact mem_iUnion.mpr ⟨i, hi.resolve_left (fun ht => hK.2 (mem_iUnion.mpr ⟨i, ht⟩))⟩

variable (hneck : Pairwise (fun i j => Disjoint (I i).neck.carrier (I j).neck.carrier))
  (htails : Pairwise (fun i j => Disjoint (cuts i).tail (cuts j).tail))
  (hcenter : ∀ i, (I i).neck.center ∈ SurgeryTerminalCoreComponents D rho)

include hneck htails hcenter in
theorem policyRetainedOpen_neck_inter (i : ι) :
    (policyRetainedOpen D rho I cuts : Set S.carrier) ∩ (I i).neck.carrier =
      (I i).negativeHalf := by
  classical
  apply Subset.antisymm
  · rintro x ⟨hx, hxN⟩
    exact ((cuts i).carrier_diff_closure_tail).subset
      ⟨hxN, fun ht => hx.2 (mem_iUnion.mpr ⟨i, ht⟩)⟩
  · intro x hx
    refine ⟨⟨?_, ?_⟩, hx.1⟩
    · exact SurgeryTerminalCoreComponents.component_subset D rho (hcenter i)
        ((I i).neck.carrier_subset_connectedComponent hx.1)
    · intro ht
      obtain ⟨j, hj⟩ := mem_iUnion.mp ht
      by_cases hij : i = j
      · subst j
        exact disjoint_left.mp (cuts i).negative_disjoint_closure hx hj
      · exact disjoint_left.mp
          ((cuts i).carrier_disjoint_other_closure (cuts j) (hneck hij) (htails hij)) hx.1 hj

include hneck htails hcenter in
theorem closure_policyRetainedOpen (R : ∀ i, MetricSurgeryResult g₀ (I i)) :
    closure (policyRetainedOpen D rho I cuts : Set S.carrier) =
      SurgeryTerminalCoreComponents D rho \ ⋃ i, (cuts i).tail := by
  apply Subset.antisymm (closure_policyRetainedOpen_subset D rho I cuts)
  intro x hx
  by_cases hxU : x ∈ policyRetainedOpen D rho I cuts
  · exact subset_closure hxU
  · have hcl : x ∈ ⋃ i, closure (cuts i).tail := not_not.mp (fun hn => hxU ⟨hx.1, hn⟩)
    obtain ⟨i, hi⟩ := mem_iUnion.mp hcl
    rw [(cuts i).closure_tail] at hi
    have hs : x ∈ (I i).neck.central_sphere :=
      hi.resolve_left (fun ht => hx.2 (mem_iUnion.mpr ⟨i, ht⟩))
    apply centralSphere_subset_closure_retained I R (policyRetainedOpen D rho I cuts)
      (policyRetainedOpen_neck_inter D rho I cuts hneck htails hcenter) i hs

theorem low_subset_policyRetainedOpen
    (hcuts : ∀ i, Disjoint (cuts i).tail {x | D.scalarCurvature x ≤ rho⁻¹ ^ 2})
    (hnecks : ∀ i, Disjoint (I i).neck.central_sphere {x | D.scalarCurvature x ≤ rho⁻¹ ^ 2}) :
    {x | D.scalarCurvature x ≤ rho⁻¹ ^ 2} ⊆ policyRetainedOpen D rho I cuts := by
  intro x hx
  refine ⟨SurgeryTerminalCoreComponents.low_subset D rho hx, ?_⟩
  intro ht
  obtain ⟨i, hi⟩ := mem_iUnion.mp ht
  rw [(cuts i).closure_tail] at hi
  exact hi.elim (fun h => disjoint_left.mp (hcuts i) h hx)
    (fun h => disjoint_left.mp (hnecks i) h hx)

end PoincareConjecture.Surgery.Terminal.Gluing
