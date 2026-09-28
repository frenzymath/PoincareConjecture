import PoincareConjecture.Proofs.M32.Thm11_31.Boundary
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Orientation.Existence
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Atlas.OpenEmbedding
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Atlas.LocalOrientation
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Nonorientable
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere
import Mathlib.Analysis.Convex.Contractible

set_option autoImplicit false

open Set Topology TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M32

theorem no_projective_product_of_orientationCompatibleAtlas
    {M : Type u} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (A : OrientationCompatibleAtlas M) :
    ¬ ∃ f : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → M, IsOpenEmbedding f := by
  rintro ⟨f, hf⟩
  let X := RealProjectiveTwo × Poincare.Topology.Orientation.ProjectivePlane.NormalInterval
  let : Nonempty X := Nonempty.map
    Poincare.Topology.Orientation.ProjectivePlane.projectivePlaneCover inferInstance
  let : T2Space X := hf.isEmbedding.t2Space
  let : SecondCountableTopology X := hf.isEmbedding.secondCountableTopology
  let P := Poincare.Topology.Orientation.ProjectivePlane.positiveThreeAtlasOpenEmbedding f hf
    (Poincare.Topology.positiveThreeAtlasOfSigned M A)
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) X := P.charts
  let : LocallyCompactSpace X :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) X
  obtain ⟨O⟩ :=
    Poincare.Topology.Orientation.ProjectivePlane.exists_localOrientation_of_positiveThreeAtlas P
  exact Poincare.Topology.Orientation.ProjectivePlane.projectivePlaneThickening_not_orientable O

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}

theorem horn_interior_homeomorph (horn : StrongHorn E epsilon) :
    Nonempty ((UnitTwoSphere × Ioo (0 : ℝ) 1) ≃ₜ
      ↥(horn.carrier \ horn.boundary_sphere)) := by
  let inc : Ioo (0 : ℝ) 1 → Ico (0 : ℝ) 1 := Set.inclusion Ioo_subset_Ico_self
  let f : UnitTwoSphere × Ioo (0 : ℝ) 1 → (E.extended.slice T).carrier :=
    fun z => horn.coordinate (z.1, inc z.2)
  have hf : IsEmbedding f :=
    IsEmbedding.subtypeVal.comp (horn.coordinate.isEmbedding.comp
      (IsEmbedding.id.prodMap (IsEmbedding.inclusion Ioo_subset_Ico_self)))
  have hrange : range f = horn.carrier \ horn.boundary_sphere := by
    rw [horn_carrier_diff_boundary_eq_image]
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, rfl⟩
      refine ⟨(q, (t : ℝ)), ⟨mem_univ _, t.property⟩, ?_⟩
      exact (horn.coordinate_eq (q, inc t)).symm
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      exact ⟨(q, ⟨t, ht⟩), horn.coordinate_eq _⟩
  exact ⟨hf.toHomeomorph.trans (Homeomorph.setCongr hrange)⟩

theorem horn_interior_simplyConnected (horn : StrongHorn E epsilon) :
    SimplyConnectedSpace ↥(horn.carrier \ horn.boundary_sphere) := by
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphereSimplyConnected_of_two_le (by norm_num)
  let : ContractibleSpace (Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨1 / 2, by norm_num⟩
  let e := (ContinuousMap.HomotopyEquiv.refl UnitTwoSphere).prodCongr
    (ContractibleSpace.hequiv (Ioo (0 : ℝ) 1) Unit).some
  let : SimplyConnectedSpace (UnitTwoSphere × Ioo (0 : ℝ) 1) :=
    (e.trans (Homeomorph.prodUnique UnitTwoSphere Unit).toHomotopyEquiv).simplyConnectedSpace
  obtain ⟨h⟩ := horn_interior_homeomorph horn
  exact h.symm.toHomotopyEquiv.simplyConnectedSpace

theorem horn_no_projective_product (horn : StrongHorn E epsilon) :
    ¬ ∃ f : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → (E.extended.slice T).carrier,
      IsOpenEmbedding f ∧ range f ⊆ horn.carrier := by
  let U : Opens (E.extended.slice T).carrier :=
    ⟨horn.carrier \ horn.boundary_sphere, horn_isOpen_carrier_diff_boundary horn⟩
  let : SimplyConnectedSpace U := horn_interior_simplyConnected horn
  obtain ⟨A⟩ := Poincare.Topology.nonempty_orientationCompatibleAtlas (M := U)
  rintro ⟨f, hf, hcarrier⟩
  have hinterior : range f ⊆ interior horn.carrier :=
    interior_maximal hcarrier hf.isOpen_range
  have hU (z : RealProjectiveTwo × Ioo (-1 : ℝ) 1) : f z ∈ U := by
    refine ⟨hcarrier (mem_range_self z), ?_⟩
    intro hboundary
    exact horn_boundary_sphere_not_mem_interior horn hboundary
      (hinterior (mem_range_self z))
  let fU : RealProjectiveTwo × Ioo (-1 : ℝ) 1 → U := fun z => ⟨f z, hU z⟩
  have hfU : IsOpenEmbedding fU :=
    IsOpenEmbedding.of_comp fU U.isOpen.isOpenEmbedding_subtypeVal hf
  exact no_projective_product_of_orientationCompatibleAtlas A ⟨fU, hfU⟩

end PoincareConjecture.M32
