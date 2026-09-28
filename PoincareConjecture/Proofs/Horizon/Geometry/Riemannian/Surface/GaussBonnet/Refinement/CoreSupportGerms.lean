import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Refinement.CoreBoundarySectors
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.PolygonalCores

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle
open Poincare.Topology.Plane.Meshes

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

section LocalSupports

variable {X : Type*} [TopologicalSpace X]

theorem core_eventuallyEq_compl_interior
    {U A C : Set X} (hU : IsOpen U) (hC : IsClosed C)
    (hcover : closure U = A ∪ C) (hfront : C ∩ A ⊆ frontier A)
    {q : X} (hq : q ∈ U) : C =ᶠ[𝓝 q] (interior A)ᶜ := by
  have hsub : U ∩ Aᶜ ⊆ C := by
    intro z hz
    have hc : z ∈ A ∪ C := hcover ▸ subset_closure hz.1
    exact hc.resolve_left hz.2
  filter_upwards [hU.mem_nhds hq] with z hz
  apply propext
  constructor
  · intro hc hi
    exact (hfront ⟨hc, interior_subset hi⟩).2 hi
  · intro hi
    have hcl : z ∈ closure Aᶜ := by rw [closure_compl]; exact hi
    exact closure_minimal hsub hC (hU.inter_closure ⟨hz, hcl⟩)

theorem finite_closed_union_eventuallyEq_incident
    {I : Type*} [Finite I] (A : I → Set X) (hA : ∀ i, IsClosed (A i)) (q : X) :
    (⋃ i, A i) =ᶠ[𝓝 q] (⋃ i : {i : I // q ∈ A i}, A i.1) := by
  let _ := Fintype.ofFinite I
  have hnear : ∀ᶠ z in 𝓝 q, ∀ i, q ∉ A i → z ∉ A i := by
    apply Filter.eventually_all.mpr
    intro i
    by_cases hi : q ∈ A i
    · exact Filter.Eventually.of_forall fun _ h => False.elim (h hi)
    · filter_upwards [(hA i).isOpen_compl.mem_nhds hi] with z hz
      exact fun _ => hz
  filter_upwards [hnear] with z hz
  apply propext
  constructor
  · intro h
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨⟨i, by by_contra h; exact hz i h hi⟩, hi⟩
  · intro h
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    exact mem_iUnion.mpr ⟨i.1, hi⟩

theorem support_eventuallyEq_interior {A B : Set X} {q : X}
    (h : A =ᶠ[𝓝 q] B) : interior A =ᶠ[𝓝 q] interior B := by
  obtain ⟨V, hV, hVo, hqV⟩ := mem_nhds_iff.mp h
  filter_upwards [hVo.mem_nhds hqV] with z hz
  apply propext
  apply Filter.EventuallyEq.mem_interior_iff
  exact Filter.mem_of_superset (hVo.mem_nhds hz) hV

theorem core_eventuallyEq_compl_incident_interior
    {I : Type*} [Finite I] (A : I → Set X) (hA : ∀ i, IsClosed (A i))
    {U C : Set X} (hU : IsOpen U) (hC : IsClosed C)
    (hcover : closure U = (⋃ i, A i) ∪ C)
    (hfront : C ∩ (⋃ i, A i) ⊆ frontier (⋃ i, A i))
    {q : X} (hq : q ∈ U) :
    C =ᶠ[𝓝 q] (interior (⋃ i : {i : I // q ∈ A i}, A i.1))ᶜ := by
  have hc := core_eventuallyEq_compl_interior hU hC hcover hfront hq
  have hi := support_eventuallyEq_interior (finite_closed_union_eventuallyEq_incident A hA q)
  filter_upwards [hc, hi] with z hc hi
  change C z = ¬ interior (⋃ i : {i : I // q ∈ A i}, A i.1) z
  change C z = ¬ interior (⋃ i, A i) z at hc
  rw [hi] at hc
  exact hc

end LocalSupports

variable {S : Type*} [TopologicalSpace S] [T2Space S]

theorem coordinate_core_support_eventuallyEq_compl_interior
    (F : OpenPartialHomeomorph Plane S) (M : TriangleMesh)
    (hsource : M.toPlaneComplex.support ⊆ F.source)
    {U A : Set S} (hU : IsOpen U)
    (hcover : closure U = A ∪ F '' M.toPlaneComplex.support)
    (hfront : (F '' M.toPlaneComplex.support) ∩ A ⊆ frontier A)
    {q : Plane} (hq : q ∈ F.source) (hqU : F q ∈ U) :
    M.toPlaneComplex.support =ᶠ[𝓝 q] (interior (F ⁻¹' A))ᶜ := by
  have hclosed : IsClosed (F '' M.toPlaneComplex.support) :=
    (M.toPlaneComplex.isCompact_support.image_of_continuousOn
      (F.continuousOn.mono hsource)).isClosed
  have hg := (core_eventuallyEq_compl_interior hU hclosed hcover hfront hqU).comp_tendsto
    (F.continuousAt hq)
  filter_upwards [hg, F.open_source.mem_nhds hq] with z hz hzs
  apply propext
  have hmem : F z ∈ F '' M.toPlaneComplex.support ↔ z ∈ M.toPlaneComplex.support := by
    constructor
    · rintro ⟨w, hw, heq⟩
      exact F.injOn (hsource hw) hzs heq ▸ hw
    · exact mem_image_of_mem F
  have hint : F z ∈ interior A ↔ z ∈ interior (F ⁻¹' A) := by
    rw [mem_interior_iff_mem_nhds, mem_interior_iff_mem_nhds, ← F.map_nhds_eq hzs]
    rfl
  have he : (F z ∈ F '' M.toPlaneComplex.support) ↔ F z ∉ interior A :=
    propext_iff.mp hz
  rw [hmem, hint] at he
  exact he

theorem coordinate_core_support_eventuallyEq_compl_incident_interior
    {I : Type*} [Finite I] (A : I → Set S) (hA : ∀ i, IsClosed (A i))
    (F : OpenPartialHomeomorph Plane S) (M : TriangleMesh)
    (hsource : M.toPlaneComplex.support ⊆ F.source)
    {U : Set S} (hU : IsOpen U)
    (hcover : closure U = (⋃ i, A i) ∪ F '' M.toPlaneComplex.support)
    (hfront : (F '' M.toPlaneComplex.support) ∩ (⋃ i, A i) ⊆ frontier (⋃ i, A i))
    {q : Plane} (hq : q ∈ F.source) (hqU : F q ∈ U) :
    M.toPlaneComplex.support =ᶠ[𝓝 q]
      (interior (⋃ i : {i : I // F q ∈ A i}, F ⁻¹' A i.1))ᶜ := by
  have hc := coordinate_core_support_eventuallyEq_compl_interior
    F M hsource hU hcover hfront hq hqU
  have hlocal : (F ⁻¹' (⋃ i, A i)) =ᶠ[𝓝 q]
      (⋃ i : {i : I // F q ∈ A i}, F ⁻¹' A i.1) := by
    have h := (finite_closed_union_eventuallyEq_incident A hA (F q)).comp_tendsto
      (F.continuousAt hq)
    filter_upwards [h] with z hz
    apply propext
    change (F z ∈ ⋃ i, A i) ↔ z ∈ ⋃ i : {i : I // F q ∈ A i}, F ⁻¹' A i.1
    have he : (F z ∈ ⋃ i, A i) ↔ F z ∈ ⋃ i : {i : I // F q ∈ A i}, A i.1 :=
      propext_iff.mp hz
    simpa only [mem_iUnion, mem_preimage] using he
  have hi := support_eventuallyEq_interior hlocal
  filter_upwards [hc, hi] with z hc hi
  change M.toPlaneComplex.support z =
    ¬ interior (⋃ i : {i : I // F q ∈ A i}, F ⁻¹' A i.1) z
  change M.toPlaneComplex.support z = ¬ interior (F ⁻¹' (⋃ i, A i)) z at hc
  rw [hi] at hc
  exact hc

variable [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]

omit [T2Space S] in

theorem meshVertexAngleContribution_restriction_eq_tangent_selection
    (g : RiemannianMetric 2 S) (F : OpenPartialHomeomorph Plane S)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    (M : TriangleMesh) (P Q : Finset M.Vertex → Prop)
    (hsource : (M.restrictTriangles P).toPlaneComplex.support ⊆ F.source)
    {q : Plane} (hq : q ∈ F.source)
    (hlocal : (M.restrictTriangles P).toPlaneComplex.support =ᶠ[𝓝 q]
      (M.restrictTriangles Q).toPlaneComplex.support) :
    meshVertexAngleContribution g F (M.restrictTriangles P) (F q) =
      meshVertexAngleContribution (coordinateTangentMetric g F hF hFi q hq)
        (OpenPartialHomeomorph.refl Plane) (M.restrictTriangles Q) q := by
  rw [meshVertexAngleContribution_eq_tangentMetric g F hF hFi q hq _ hsource]
  exact meshVertexAngleContribution_restrictTriangles_eq_of_support_eventuallyEq
    _ (OpenPartialHomeomorph.refl Plane) M P Q (by simp) (by simp) hlocal

end PoincareConjecture.Topology.Surface
