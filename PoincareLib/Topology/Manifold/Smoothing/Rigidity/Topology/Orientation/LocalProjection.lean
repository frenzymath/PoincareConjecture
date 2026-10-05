import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Hierarchy.Annulus.Spheres.ClosedPhaseSphere
import PoincareLib.Topology.Manifold.Orientation.ProjectivePlane.Local.Homeomorph
import PoincareLib.Topology.Manifold.Smoothing.Dehn.General.OriginalPLStage

/-!
# Original PL orientation labels above the three-torus

The actual local projection pulls back the torus orientation. Comparison
with arbitrary compatible PL charts then supplies their locally constant
orientation labels, including every constructed original PL tower stage.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry
open Poincare.Topology.Orientation.ProjectivePlane

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_local_projection_atlas_labels
    {Y : Type} [TopologicalSpace Y] [T2Space Y] [LocallyCompactSpace Y]
    (f : Y → X0) (hf : IsLocalHomeomorph f)
    {ι : Type*} (e : ι → OpenPartialHomeomorph Y V3)
    (he : ∀ i j, (e i).symm.trans (e j) ∈ piecewiseAffineGroupoid V3) :
    ∃ label : ∀ i, LocallyConstant (e i).source PLOrientationSheet,
      ∀ i j (x : Y) (hi : x ∈ (e i).source) (hj : x ∈ (e j).source),
        (label j ⟨x, hj⟩).val =
          plAtlasTransitionSign e he i j ⟨x, hi, hj⟩ * (label i ⟨x, hi⟩).val := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let : LocallyCompactSpace X0 := (Q0).isOpenEmbedding.locallyCompactSpace
  obtain ⟨O⟩ := hamiltonZeroAmbient_localOrientation
  obtain ⟨O', _⟩ := exists_localOrientation_of_isLocalHomeomorph f hf O
  let a : V3 ≃ᴬ[ℝ] E3 := (EuclideanSpace.equiv (Fin 3) ℝ).symm.toContinuousAffineEquiv
  let q (i : ι) := (e i).transHomeomorph a.toHomeomorph
  have hq := affine_model_plAtlas_compatible e he a
  obtain ⟨label, hlabel⟩ := exists_plAtlas_labels_of_localOrientation
    O' euclideanLocalOrientation q hq
  refine ⟨label, ?_⟩
  intro i j x hi hj
  have h := hlabel i j x hi hj
  rw [plAtlasTransitionSign_affine_model e he a i j ⟨x, hi, hj⟩] at h
  exact h

end PoincareMT.M76
