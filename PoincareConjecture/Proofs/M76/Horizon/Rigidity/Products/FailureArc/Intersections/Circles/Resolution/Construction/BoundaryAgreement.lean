import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Circles.Reduction.LocalCharts

set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76.Dehn.Annuli.CircleResolution

theorem exists_open_boundary_agreement_of_interior_modification
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [T2Space X]
    {S U D : Set E} {R : Set X} {f k : E → X}
    (hD : IsCompact D) (hDS : D ⊆ interior S) (hUD : U ⊆ D)
    (hf : ContinuousOn f S) (hk : ContinuousOn k S)
    (hfproper : ∀ x ∈ S, f x ∈ frontier R ↔ x ∈ frontier S)
    (hkproper : ∀ x ∈ S, k x ∈ frontier R ↔ x ∈ frontier S)
    (hkeep : EqOn k f (S \ U)) :
    ∃ W : Set X, IsOpen W ∧ frontier R ⊆ W ∧
      ∀ z ∈ W, z ∈ k '' S ↔ z ∈ f '' S := by
  have hsub := hDS.trans interior_subset
  refine ⟨(f '' D ∪ k '' D)ᶜ,
    ((hD.image_of_continuousOn (hf.mono hsub)).isClosed.union
      (hD.image_of_continuousOn (hk.mono hsub)).isClosed).isOpen_compl,?_,?_⟩
  · rintro z hz (⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩)
    · exact ((hfproper x (hsub hx)).mp hz).2 (hDS hx)
    · exact ((hkproper x (hsub hx)).mp hz).2 (hDS hx)
  · intro z hz
    constructor
    · rintro ⟨x,hx,rfl⟩
      have hxu : x ∉ U := fun hh => hz (Or.inr ⟨x,hUD hh,rfl⟩)
      exact ⟨x,hx,(hkeep ⟨hx,hxu⟩).symm⟩
    · rintro ⟨x,hx,rfl⟩
      have hxu : x ∉ U := fun hh => hz (Or.inl ⟨x,hUD hh,rfl⟩)
      exact ⟨x,hx,hkeep ⟨hx,hxu⟩⟩

theorem boundary_pair_chart_of_local_agreement
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)}
    {S T T' W R : Set X} {y : X}
    (C : OriginalSurfacePairChart e S T y true)
    (hregion : ∀ z ∈ C.coordinates.source,
      C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2)
    (hfrontier : ∀ z ∈ C.coordinates.source,
      C.chart.symm z ∈ frontier R ↔ (C.coordinates z).1.2 = 0)
    (hW : IsOpen W) (hyW : y ∈ W)
    (hT : ∀ z ∈ W, z ∈ T' ↔ z ∈ T) :
    ∃ C' : OriginalSurfacePairChart e S T' y true,
      (∀ z ∈ C'.coordinates.source, C'.chart.symm z ∈ R ↔
        0 ≤ (C'.coordinates z).1.2) ∧
      ∀ z ∈ C'.coordinates.source, C'.chart.symm z ∈ frontier R ↔
        (C'.coordinates z).1.2 = 0 := by
  let V := C.chart '' (C.chart.source ∩ W)
  have hV : IsOpen V := C.chart.isOpen_image_of_subset_source
    (C.chart.open_source.inter hW) inter_subset_left
  have hVW (z : Fin 3 → ℝ) (hz : z ∈ V) : C.chart.symm z ∈ W := by
    obtain ⟨x,hx,rfl⟩ := hz
    rw [C.chart.left_inv hx.1]
    exact hx.2
  let C' : OriginalSurfacePairChart e S T' y true := {
    chart := C.chart
    coordinates := C.coordinates.restrOpen V hV
    compatible := C.compatible
    center_source := C.center_source
    center_coordinates := ⟨C.center_coordinates,⟨y,⟨C.center_source,hyW⟩,rfl⟩⟩
    center_zero := C.center_zero
    source_subset := fun _ hz => C.source_subset hz.1
    forwardPL := C.forwardPL.mono (C.coordinates.restrOpen V hV).open_source inter_subset_left
    inversePL := C.inversePL.mono (C.coordinates.restrOpen V hV).open_target inter_subset_left
    first_surface := fun z hz => C.first_surface z hz.1
    second_surface := fun z hz => (hT _ (hVW z hz.2)).trans (C.second_surface z hz.1) }
  exact ⟨C',fun z hz => hregion z hz.1,fun z hz => hfrontier z hz.1⟩

end PoincareConjecture.M76.Dehn.Annuli.CircleResolution
