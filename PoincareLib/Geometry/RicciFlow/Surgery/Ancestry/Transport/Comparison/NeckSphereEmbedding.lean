import PoincareLib.Topology.Manifold.NeckCap.Cylinder.Sphere
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Transport.Mathlib.SmoothEmbeddingTransport
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Transport.Comparison.RegionInverses
import PoincareLib.Geometry.RicciFlow.Surgery.Ancestry.Transport.Comparison.FreeSphereNullHomotopy
import PoincareLib.Topology.Manifold.EmbeddedSphere.Theory

/-!
# The guarded surgery sphere in its actual parent

For Morgan--Tian Proposition 15.12 and Remark 15.13 (p. 365), move the
actual central neck sphere through the limit inverse and the selected
component inverse. A nonempty intersection places the whole connected
sphere in the parent. The supplied M02 and M53 services then prove separation.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT

/-- A connected sphere meeting a selected component lies entirely in that
component, the guarded-parent step in Proposition 15.12, p. 365. -/
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

/-- The sphere's image after the component inverse is the exact guarded
preimage set in the repaired comparison input of Proposition 15.12, p. 365. -/
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

/-- A smooth sphere meeting a simply connected compact selected parent
separates that parent, by the supplied M02 and M53 services (p. 365 and
the class-transport discussion on pp. 430-431). -/
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

/-- Every actual event neck sphere that meets the selected parent separates
it. Both region inverses are used on their valid domains (Proposition 15.12
and Remark 15.13, p. 365). -/
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

end PoincareMT
