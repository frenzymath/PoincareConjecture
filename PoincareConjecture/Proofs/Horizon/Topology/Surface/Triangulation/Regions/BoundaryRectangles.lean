


import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Regions.Neighborhoods








set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface
namespace FiniteChartRegionDecomposition

universe u

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
variable (D : FiniteChartRegionDecomposition (M := M))


structure BoundaryRectangle (a : D.EdgeIndex) where
  left : ℝ
  right : ℝ
  width : ℝ
  left_pos : 0 < left
  left_lt_right : left < right
  right_lt_one : right < 1
  width_pos : 0 < width
  coordinates : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M
  rectangle_subset :
    collarParameterEquiv ⁻¹' (Icc left right ×ˢ Icc (-width / 2) (width / 2)) ⊆
      coordinates.source
  axis : ∀ t, coordinates (collarParameterEquiv.symm (t, 0)) = (D.edge a.1 a.2).map t
  target_subset : coordinates.target ⊆
    (chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M)).source
  smooth : ContMDiffOn (𝓡 2) (𝓡 2) ∞ coordinates coordinates.source
  smooth_symm : ContMDiffOn (𝓡 2) (𝓡 2) ∞ coordinates.symm coordinates.target

namespace BoundaryRectangle

variable {D} {a : D.EdgeIndex} (R : D.BoundaryRectangle a)


def closedSource : Set (EuclideanSpace ℝ (Fin 2)) :=
  collarParameterEquiv ⁻¹' (Icc R.left R.right ×ˢ Icc (-R.width / 2) (R.width / 2))


def openSource : Set (EuclideanSpace ℝ (Fin 2)) :=
  collarParameterEquiv ⁻¹' (Ioo R.left R.right ×ˢ Ioo (-R.width / 2) (R.width / 2))


def carrier : Set M := R.coordinates '' R.closedSource


def openCarrier : Set M := R.coordinates '' R.openSource

omit [T2Space M] in
theorem openSource_subset_closedSource : R.openSource ⊆ R.closedSource :=
  preimage_mono (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)

omit [T2Space M] in
theorem closedSource_subset : R.closedSource ⊆ R.coordinates.source := R.rectangle_subset

omit [T2Space M] in
theorem openCarrier_subset_carrier : R.openCarrier ⊆ R.carrier :=
  image_mono R.openSource_subset_closedSource

omit [T2Space M] in
theorem isCompact_closedSource : IsCompact R.closedSource :=
  collarParameterEquiv.toHomeomorph.isCompact_preimage.mpr (isCompact_Icc.prod isCompact_Icc)

omit [T2Space M] in
theorem isOpen_openSource : IsOpen R.openSource :=
  (isOpen_Ioo.prod isOpen_Ioo).preimage collarParameterEquiv.continuous

omit [T2Space M] in
theorem isCompact_carrier : IsCompact R.carrier :=
  R.isCompact_closedSource.image_of_continuousOn
    (R.coordinates.continuousOn.mono R.closedSource_subset)

omit [T2Space M] in
theorem isOpen_openCarrier : IsOpen R.openCarrier :=
  R.coordinates.isOpen_image_of_subset_source R.isOpen_openSource
    (R.openSource_subset_closedSource.trans R.closedSource_subset)

omit [T2Space M] in
theorem carrier_subset_target : R.carrier ⊆ R.coordinates.target := by
  rintro _ ⟨z, hz, rfl⟩
  exact R.coordinates.map_source (R.closedSource_subset hz)

omit [T2Space M] in
theorem carrier_subset_chart : R.carrier ⊆
    (chartAt (EuclideanSpace ℝ (Fin 2)) (a.1.1 : M)).source :=
  R.carrier_subset_target.trans R.target_subset

omit [T2Space M] in
theorem closure_openSource : closure R.openSource = R.closedSource := by
  change closure (collarParameterEquiv.toHomeomorph ⁻¹'
    (Ioo R.left R.right ×ˢ Ioo (-R.width / 2) (R.width / 2))) = _
  rw [← collarParameterEquiv.toHomeomorph.preimage_closure, closure_prod_eq,
    closure_Ioo R.left_lt_right.ne,
    closure_Ioo (show -R.width / 2 ≠ R.width / 2 by linarith [R.width_pos])]
  rfl

theorem closure_openCarrier : closure R.openCarrier = R.carrier := by
  apply subset_antisymm
  · exact closure_minimal R.openCarrier_subset_carrier R.isCompact_carrier.isClosed
  · rintro _ ⟨z, hz, rfl⟩
    apply mem_closure_image (R.coordinates.continuousAt (R.closedSource_subset hz))
    rwa [R.closure_openSource]

omit [T2Space M] in
theorem edge_open_segment_subset : (D.edge a.1 a.2).map '' Ioo R.left R.right ⊆
    R.openCarrier := by
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨collarParameterEquiv.symm (t, 0), ?_, R.axis t⟩
  change collarParameterEquiv (collarParameterEquiv.symm (t, 0)) ∈
    Ioo R.left R.right ×ˢ Ioo (-R.width / 2) (R.width / 2)
  rw [collarParameterEquiv.apply_symm_apply]
  exact ⟨ht, by constructor <;> linarith [R.width_pos]⟩

end BoundaryRectangle



theorem exists_boundary_rectangles
    (P : ∀ p : D.vertices, ChartCircleArrangementVertexPatch D.radius p) :
    ∃ R : ∀ a : D.EdgeIndex, D.BoundaryRectangle a,
      (∀ a, (D.edge a.1 a.2).map '' Icc 0 (R a).left ⊆
          (P ⟨(D.edge a.1 a.2).map 0, (D.endpoints_mem_vertices a).1⟩).openCarrier ∧
        (D.edge a.1 a.2).map '' Icc (R a).right 1 ⊆
          (P ⟨(D.edge a.1 a.2).map 1, (D.endpoints_mem_vertices a).2⟩).openCarrier) ∧
      Pairwise (fun a b => Disjoint (R a).carrier (R b).carrier) ∧
      (∀ a b, a ≠ b → Disjoint (R a).carrier ((D.edge b.1 b.2).map '' Icc (0 : ℝ) 1)) ∧
      chartDiskBoundaryUnion D.centers D.radius ⊆
        (⋃ p, (P p).openCarrier) ∪ (⋃ a, (R a).openCarrier) := by
  obtain ⟨l, r, ε, C, hbounds, hends, hstrip, haxis, hchart, hC, hCinv, hdis, havoid, _⟩ :=
    D.exists_boundary_neighborhood P
  let R (a : D.EdgeIndex) : D.BoundaryRectangle a := {
    left := l a
    right := r a
    width := ε a
    left_pos := (hbounds a).1
    left_lt_right := (hbounds a).2.1
    right_lt_one := (hbounds a).2.2.1
    width_pos := (hbounds a).2.2.2
    coordinates := C a
    rectangle_subset := by
      intro z hz
      apply hstrip a
      change z 0 ∈ Icc (l a) (r a) ∧ z 1 ∈ Ioo (-ε a) (ε a)
      change z 0 ∈ Icc (l a) (r a) ∧ z 1 ∈ Icc (-ε a / 2) (ε a / 2) at hz
      exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2, (hbounds a).2.2.2]⟩
    axis := haxis a
    target_subset := hchart a
    smooth := hC a
    smooth_symm := hCinv a }
  refine ⟨R, hends, ?_, ?_, ?_⟩
  · intro a b hab
    exact (hdis hab).mono (R a).carrier_subset_target (R b).carrier_subset_target
  · intro a b hab
    exact (havoid a b hab).mono_left (R a).carrier_subset_target
  · rw [← D.boundary_cover]
    intro z hz
    obtain ⟨a, t, ht, rfl⟩ := mem_iUnion.mp hz
    by_cases htl : t ≤ l a
    · exact Or.inl (mem_iUnion.mpr ⟨_, (hends a).1 ⟨t, ⟨ht.1, htl⟩, rfl⟩⟩)
    by_cases hrt : r a ≤ t
    · exact Or.inl (mem_iUnion.mpr ⟨_, (hends a).2 ⟨t, ⟨hrt, ht.2⟩, rfl⟩⟩)
    · exact Or.inr (mem_iUnion.mpr ⟨a, (R a).edge_open_segment_subset
        ⟨t, ⟨lt_of_not_ge htl, lt_of_not_ge hrt⟩, rfl⟩⟩)

end FiniteChartRegionDecomposition
end PoincareConjecture.Topology.Surface
