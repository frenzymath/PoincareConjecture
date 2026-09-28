import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Components.ModelComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Cutting.Rim.ComponentCollar
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CollarTransport



set_option autoImplicit false
open Set Metric Geometry BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "D1" => closedBall (0 : Fin 1 → ℝ) 1

theorem source_model_component_rim_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (phi : C(H, H)) (theta : C) (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    (K J : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (Hmodel : K.space ≃ₜ sourceSurface phi theta)
    (F : X → E) (hFc : Continuous F)
    (hHF : ∀ x : sourceSurface phi theta, (Hmodel.symm x : E) = F x)
    (D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hJD : J ≤ K.edgeComponentComplex D)
    (b : D1) (hb : ‖(b : Fin 1 → ℝ)‖ = 1) (delta : C ≃ₜ J.space)
    (hdelta : ∀ c, (delta c : E) = F (sourceBoundaryCircle phi theta F0 b hb c : X))
    (hinj : ∀ x : sourceSurface phi theta, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) x))
    {U : Set (sourceSurface phi theta)} (hU : IsOpen U)
    (collar : (↥(sourceSurface phi theta ∩ frontier R) × Ico (0 : ℝ) 1) ≃ₜ U)
    (hbase : ∀ x, (collar (collarBase x) : sourceSurface phi theta) =
      Set.inclusion inter_subset_left x) :
    Function.Bijective (FundamentalGroup.map
      ((ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le hJD)).comp
        (delta : C(C, J.space))) 0) ∧
    ∀ x : J.space,
      ∃ c : OpenPartialHomeomorph (J.space × Ico (0 : ℝ) 1) (K.edgeComponentComplex D).space,
        collarBase x ∈ c.source ∧ ∀ a, collarBase a ∈ c.source →
          c (collarBase a) = Set.inclusion (SimplicialComplex.space_subset_of_le hJD) a := by
  obtain ⟨S, G, hSF, hcomponent, hG, hGF⟩ :=
    exists_source_component_of_model K hK Hmodel F hFc hHF D
  let incl := ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le hJD)
  let f : C(C, (K.edgeComponentComplex D).space) := incl.comp (delta : C(C, J.space))
  have hpoint (c : C) : (G (f c) : X) =
      (sourceBoundaryCircle phi theta F0 b hb c : X) := by
    rw [hG]
    apply congrArg Subtype.val
    apply Hmodel.symm.injective
    apply Subtype.ext
    rw [Hmodel.symm_apply_apply, hHF]
    exact hdelta c
  have hbS : (sourceBoundaryCircle phi theta F0 b hb 0 : X) ∈ S := by
    rw [← hpoint 0]
    exact (G (f 0)).property
  let fS := sourceBoundaryCircleInComponent phi theta F0 b hb hcomponent hbS
  have hcomm (c : C) : G (f c) = fS c := Subtype.ext (hpoint c)
  have hfactor : (G : C((K.edgeComponentComplex D).space, S)).comp f = fS := ContinuousMap.ext hcomm
  have hbij : Function.Bijective (FundamentalGroup.map
      ((G : C((K.edgeComponentComplex D).space, S)).comp f) 0) := by
    rw [hfactor]
    exact sourceBoundaryCircleInComponent_pi1_bijective phi theta F0 b hb
      hSF hcomponent hbS hinj 0
  have hGinj := (G.fundamentalGroupMulEquiv (f 0)).injective
  have hfbij : Function.Bijective (FundamentalGroup.map f 0) := by
    constructor
    · intro a b hab
      apply hbij.1
      rw [FundamentalGroup.map_comp, MonoidHom.comp_apply, MonoidHom.comp_apply, hab]
    · intro z
      obtain ⟨a, ha⟩ := hbij.2 (FundamentalGroup.map
        (G : C((K.edgeComponentComplex D).space, S)) (f 0) z)
      refine ⟨a, hGinj ?_⟩
      rw [FundamentalGroup.map_comp, MonoidHom.comp_apply] at ha
      exact ha
  obtain ⟨V, hV, d, hd⟩ := exists_sourceBoundaryCircle_component_collar
    phi theta F0 b hb hSF hcomponent hbS hU collar hbase
  exact ⟨hfbij, exists_local_collar_of_parametrized_collar G delta fS incl hcomm hV d hd⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
