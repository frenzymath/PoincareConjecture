import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.Topology
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.TopologicalAdapters
import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Sphere
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.ThreeDimensional.Orientation.Existence
import PoincareConjecture.Proofs.Horizon.Compat.M33OrientationExclusion
import Mathlib.Analysis.Convex.Contractible

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology TopologicalSpace
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.StrongHorn

variable {F : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {E : GeneralizedFlowExtension F T}

def interiorOpens (horn : StrongHorn E epsilon) : Opens (E.extended.slice T).carrier :=
  ⟨horn.carrier \ horn.boundary_sphere, horn.isOpen_carrier_diff_boundary⟩

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

theorem noTrivialNormalProjectivePlane_interior (horn : StrongHorn E epsilon) :
    NoTrivialNormalProjectivePlane (M := horn.interiorOpens) := by
  let : SimplyConnectedSpace horn.interiorOpens := horn.simplyConnectedSpace_interior
  obtain ⟨O⟩ := Poincare.Topology.nonempty_orientationCompatibleAtlas
    (M := horn.interiorOpens)
  exact m33OrientationExclusion horn.interiorOpens O

end PoincareConjecture.StrongHorn
