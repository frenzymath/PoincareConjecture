import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.Topology
import PoincareLib.AlgebraicTopology.FundamentalGroup.TopologicalAdapters
import PoincareLib.Topology.Homotopy.Sphere
import PoincareLib.Topology.Manifold.ThreeDimensional.Orientation.Existence
import PoincareLib.Topology.Manifold.Orientation.ProjectivePlane.Exclusion
import Mathlib.Analysis.Convex.Contractible

/-!
# Projective-plane exclusion inside an actual horn

The open positive-coordinate part of the supplied horn is homeomorphic to
`S^2 x (0,1)`, hence simply connected. Its actual smooth structure therefore
has a compatible orientation atlas. The checked topological orientation
obstruction excludes any projective plane with a product neighborhood there.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}

/-- The actual open portion of the horn beyond its boundary sphere. -/
def interiorOpens (horn : StrongHorn E epsilon) : Opens (E.extended.slice T).carrier :=
  ⟨horn.carrier \ horn.boundary_sphere, horn.isOpen_carrier_diff_boundary⟩

/-- Restricting the supplied horn coordinates gives the usual open cylinder. -/
theorem nonempty_interiorHomeomorph (horn : StrongHorn E epsilon) :
    Nonempty ((UnitTwoSphere × Ioo (0 : ℝ) 1) ≃ₜ horn.interiorOpens) := by
  let inc : Ioo (0 : ℝ) 1 → Ico (0 : ℝ) 1 := Set.inclusion Ioo_subset_Ico_self
  let f : UnitTwoSphere × Ioo (0 : ℝ) 1 → (E.extended.slice T).carrier :=
    fun z => horn.coordinate (z.1, inc z.2)
  have hf : IsEmbedding f :=
    IsEmbedding.subtypeVal.comp (horn.coordinate.isEmbedding.comp
      (IsEmbedding.id.prodMap (IsEmbedding.inclusion Ioo_subset_Ico_self)))
  have hrange : range f = horn.carrier \ horn.boundary_sphere := by
    rw [horn.carrier_diff_boundary_eq_image]
    ext x
    constructor
    · rintro ⟨⟨q, t⟩, rfl⟩
      refine ⟨(q, (t : ℝ)), ⟨mem_univ _, t.property⟩, ?_⟩
      exact (horn.coordinate_eq (q, inc t)).symm
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      exact ⟨(q, ⟨t, ht⟩), horn.coordinate_eq _⟩
  exact ⟨hf.toHomeomorph.trans (Homeomorph.setCongr hrange)⟩

/-- The actual horn interior has trivial fundamental group. -/
theorem simplyConnectedSpace_interior (horn : StrongHorn E epsilon) :
    SimplyConnectedSpace horn.interiorOpens := by
  let : SimplyConnectedSpace UnitTwoSphere :=
    Poincare.Topology.sphereSimplyConnected_of_two_le (by norm_num)
  let : ContractibleSpace (Ioo (0 : ℝ) 1) :=
    (convex_Ioo (0 : ℝ) 1).contractibleSpace ⟨1 / 2, by norm_num⟩
  let : SimplyConnectedSpace (UnitTwoSphere × Ioo (0 : ℝ) 1) :=
    simplyConnectedSpace_prod_contractible _ _
  obtain ⟨e⟩ := horn.nonempty_interiorHomeomorph
  exact e.symm.toHomotopyEquiv.simplyConnectedSpace

/-- No projective-plane product neighborhood embeds openly into the actual
horn interior. Orientation exclusion is applied as a proved theorem. -/
theorem noTrivialNormalProjectivePlane_interior (horn : StrongHorn E epsilon) :
    NoTrivialNormalProjectivePlane (M := horn.interiorOpens) := by
  let : SimplyConnectedSpace horn.interiorOpens := horn.simplyConnectedSpace_interior
  obtain ⟨O⟩ := Poincare.Topology.nonempty_orientationCompatibleAtlas
    (M := horn.interiorOpens)
  exact m83OrientationExclusion horn.interiorOpens O

end PoincareMT.StrongHorn
