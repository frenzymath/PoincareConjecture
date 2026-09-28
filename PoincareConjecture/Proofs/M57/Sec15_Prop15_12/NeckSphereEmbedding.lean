import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Sphere
import PoincareConjecture.Proofs.M57.Mathlib.SmoothEmbeddingTransport
import PoincareConjecture.Proofs.M57.Sec15_Prop15_12.RegionInverses
import PoincareConjecture.Proofs.M57.Sec15_Prop15_12.FreeSphereNullHomotopy
import PoincareConjecture.Statements.M53SphereSeparation










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem m57Sphere_range_subset_component
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (f : UnitTwoSphere → A.carrier) (hf : Continuous f)
    (hne : (C.inclusion ⁻¹' range f).Nonempty) :
    range f ⊆ range C.inclusion := by
  let : PathConnectedSpace UnitTwoSphere :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 3)) zero_le_one)
  obtain ⟨x, hx⟩ := hne
  have hxC : C.inclusion x ∈ connectedComponent (C.inclusion C.basepoint) :=
    C.range_eq_component ▸ (show C.inclusion x ∈ range C.inclusion from ⟨x, rfl⟩)
  rw [C.range_eq_component, connectedComponent_eq hxC]
  exact (isConnected_range hf).subset_connectedComponent hx



theorem m57ComponentSphere_range
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (f : UnitTwoSphere → A.carrier) (hf : range f ⊆ range C.inclusion) :
    range (C.inverse ∘ f) = C.inclusion ⁻¹' range f := by
  ext x
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p, (m57Component_inverse_right C (hf ⟨p, rfl⟩)).symm⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, (congrArg C.inverse hp).trans (C.left_inverse x)⟩




theorem m57ComponentSphere_separating
    (P02 : RepairedClosedTopologyProvider.{u}) (G53 : RepairedSphereSeparationTheory.{u})
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    [SimplyConnectedSpace C.carrier.carrier]
    (f : UnitTwoSphere → A.carrier)
    (hf : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (hne : (C.inclusion ⁻¹' range f).Nonempty) :
    SeparatingSphere (C.inclusion ⁻¹' range f) := by
  have hsub := m57Sphere_range_subset_component C f hf.contMDiff.continuous hne
  have hinj : Function.Injective (C.inverse ∘ f) := by
    intro x y hxy
    apply hf.isEmbedding.injective
    exact (m57Component_inverse_right C (hsub ⟨x, rfl⟩)).symm.trans
      ((congrArg C.inclusion hxy).trans (m57Component_inverse_right C (hsub ⟨y, rfl⟩)))
  have hemb := hf.comp_localDiffeomorph_along
    (fun x => m57ComponentInverse_localDiffeomorph C (f x) (hsub ⟨x, rfl⟩)) hinj
  let : CompactSpace C.carrier.carrier := ⟨C.compact⟩
  let : ConnectedSpace C.carrier.carrier := connectedSpace_iff_univ.mpr C.connected
  let S : SmoothEmbeddedNullHomotopicSphere (M := C.carrier.carrier) :=
    { sphere := C.inverse ∘ f
      smooth_embedding := hemb
      null_homotopic := m57FreeSphereNullHomotopy P02 _ hemb.contMDiff.continuous }
  obtain ⟨G⟩ := G53.separation (M := C.carrier.carrier)
  have h := G.separating S
  change SeparatingSphere (range (C.inverse ∘ f)) at h
  rwa [m57ComponentSphere_range C f hsub] at h




theorem m57NeckSphere_separating
    (P02 : RepairedClosedTopologyProvider.{u}) (G53 : RepairedSphereSeparationTheory.{u})
    {g₀ : StandardInitialMetric} (D : RepairedSurgeryFlowData.{u} g₀)
    (T : ℝ) (hT : T ∈ D.flow.surgery_times) [Nonempty (D.flow.slice T).carrier]
    (parent : SurgerySelectedComponent (D.flow.slice (D.flow.event T hT).tMinus))
    [SimplyConnectedSpace parent.carrier.carrier]
    (i : Fin (D.flow.event T hT).cap_count)
    (hne : (parent.inclusion ⁻¹' ((D.flow.event T hT).limit_identify.inverse ''
      ((D.flow.event T hT).necks i).neck.central_sphere)).Nonempty) :
    SeparatingSphere (parent.inclusion ⁻¹' ((D.flow.event T hT).limit_identify.inverse ''
      ((D.flow.event T hT).necks i).neck.central_sphere)) := by
  let E := D.flow.event T hT
  let N := (E.necks i).neck
  let q : UnitTwoSphere → E.terminal.carrier := fun p => N.coordinate_map (p, 0)
  have hi : Function.Injective E.limit_identify.inverse := by
    intro x y hxy
    exact (E.limit_identify.right_inverse (mem_univ x)).symm.trans
      ((congrArg E.limit_identify.map hxy).trans (E.limit_identify.right_inverse (mem_univ y)))
  have hemb : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
      (E.limit_identify.inverse ∘ q) :=
    N.centralSphere_isSmoothEmbedding.comp_localDiffeomorph_along
      (fun x => m57RegionInverse_localDiffeomorph E.limit_identify
        E.regular_limit_open isOpen_univ (q x) (mem_univ _))
      (hi.comp N.centralSphere_isSmoothEmbedding.isEmbedding.injective)
  have hrange : range (E.limit_identify.inverse ∘ q) =
      E.limit_identify.inverse '' N.central_sphere := by
    rw [range_comp, N.centralSphere_range]
  rw [← hrange] at hne ⊢
  exact m57ComponentSphere_separating P02 G53 parent _ hemb hne

end PoincareConjecture
