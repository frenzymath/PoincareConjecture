import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Orientation.LocalProjection
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Boundary.Orientable.StageAnnulus

set_option autoImplicit false
open Set Metric Geometry PLAnnularStrip
open PoincareConjecture.M76 PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V1" => (Fin 1 → ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) hamiltonZeroPeriodLattice

variable {ι : Type} {e : ι → OpenPartialHomeomorph X0 V3}
  {S : SimplicialComplex ℝ (V1 × V2)} {g : (V1 × V2) → X0}
  {r : X0 → ℝ} {C R : Set X0} {st : Stage e S g r C} {F : Bool → Set X0}

theorem MarkedBoundaryPair.exists_proper_stage_annulus
    (P : MarkedBoundaryPair st R F) (hF : ∀ b, F b ⊆ frontier R) :
    ∃ (k : (V1 × V2) → st.Carrier) (f : C(ProtectedAnnulus.source, R)),
      PolyhedralPLInCharts st.charts k ProtectedAnnulus.source ∧
      Topology.IsEmbedding (fun x : ProtectedAnnulus.source ↦ k x) ∧
      (∀ x : ProtectedAnnulus.source, (f x : X0) = st.projection (k x)) ∧
      (∀ (b : Bool) (u : Q2), st.projection (k (ProtectedAnnulus.endpoint b, u)) ∈ F b) ∧
      (∀ b, ¬ (sourceAnnulusRim f b).Nullhomotopic) ∧
      ∀ x : ProtectedAnnulus.source,
        k x ∈ frontier (st.projection ⁻¹' R) ↔
          (x : V1 × V2).1 ∈ sphere (0 : V1) 1 := by
  let Q := hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates
  let : T2Space X0 := Q.isEmbedding.t2Space
  let : LocallyCompactSpace X0 := Q.isOpenEmbedding.locallyCompactSpace
  obtain ⟨O⟩ := hamiltonZeroAmbient_localOrientation
  obtain ⟨O', _⟩ :=
    Poincare.Topology.Orientation.ProjectivePlane.exists_localOrientation_of_isLocalHomeomorph
      st.projection st.projectionLocal O
  exact P.exists_proper_stage_annulus_of_localOrientation O' hF

end Geometry.OriginalPLTower
