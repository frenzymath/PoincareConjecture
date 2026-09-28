import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Components.RimData
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Components.OneRimObstruction
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.RimComponents



set_option autoImplicit false
open Set Metric Geometry BrownCollar

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "R" => latticeHandleDomain (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "B" => latticeHandleBoundary (Fin 1) (Fin 2) L
local notation "C" => AddCircle (4 * (128 : ℝ))
local notation "Q2" => sphere (0 : Fin 2 → ℝ) 1

open Classical in
theorem exists_common_rim_component_of_source_model
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (phi : C(H, H)) (theta : C) (F0 : (ContinuousMap.id H).HomotopyRel phi B)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (Hmodel : K.space ≃ₜ sourceSurface phi theta)
    (F : X → E) (hFc : Continuous F)
    (hHF : ∀ x : sourceSurface phi theta, (Hmodel.symm x : E) = F x)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (J : Bool → SimplicialComplex ℝ E) (hJK : ∀ side, J side ≤ K)
    (gamma : ∀ side, Q2 ≃ₜ (J side).space) (hgamma : ∀ side, (gamma side).IsFinitePL)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ side, s ∈ (J side).faces then 1 else 2)
    (delta : ∀ side, C ≃ₜ (J side).space)
    (hdelta : ∀ side c, (delta side c : E) = F (sourceBoundaryCircle phi theta F0
      (originalIntervalEndpoint side) (originalIntervalEndpoint_norm side) c : X))
    (hinj : ∀ x : sourceSurface phi theta, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(sourceSurface phi theta, X)) x))
    {U : Set (sourceSurface phi theta)} (hU : IsOpen U)
    (collar : (↥(sourceSurface phi theta ∩ frontier R) × Ico (0 : ℝ) 1) ≃ₜ U)
    (hbase : ∀ x, (collar (collarBase x) : sourceSurface phi theta) =
      Set.inclusion inter_subset_left x) :
    ∃ (D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
      (hJD : ∀ side, J side ≤ K.edgeComponentComplex D),
      (K.edgeComponentComplex D).faces.Finite ∧
      (∀ s ∈ (K.edgeComponentComplex D).faces,
        ∃ t ∈ (K.edgeComponentComplex D).faces, t.card = 3 ∧ s ⊆ t) ∧
      (∀ v ∈ (K.edgeComponentComplex D).vertices,
        IsConnected ((K.edgeComponentComplex D).link v).space) ∧
      IsPathConnected (K.edgeComponentComplex D).space ∧
      (∀ s ∈ (K.edgeComponentComplex D).faces, s.card = 2 →
        {t : Finset E | t ∈ (K.edgeComponentComplex D).faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
          if ∃ side, s ∈ (J side).faces then 1 else 2) ∧
      ∀ side, Function.Bijective (FundamentalGroup.map
        (ContinuousMap.inclusion (SimplicialComplex.space_subset_of_le (hJD side))) (delta side 0)) ∧
        ∀ x : (J side).space,
          ∃ c : OpenPartialHomeomorph ((J side).space × Ico (0 : ℝ) 1) (K.edgeComponentComplex D).space,
            collarBase x ∈ c.source ∧ ∀ a, collarBase a ∈ c.source →
              c (collarBase a) = Set.inclusion (SimplicialComplex.space_subset_of_le (hJD side)) a := by
  have hconn (side : Bool) : IsConnected (J side).space :=
    (Dehn.Annuli.circle_incidence (J side) (hK.subset (hJK side))
      (gamma side) (hgamma side)).2.2.1
  obtain ⟨r, hr, hmem⟩ := Dehn.Annuli.exists_rim_component_assignment K hK J hJK hconn
  have hp (D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      ∀ s ∈ (K.edgeComponentComplex D).faces,
        ∃ t ∈ (K.edgeComponentComplex D).faces, t.card = 3 ∧ s ⊆ t := by
    intro s hs
    obtain ⟨t, ht, htc, hst⟩ := hpure s hs.1
    exact ⟨t, K.edgeComponentComplex_coface D hs ht hst, htc, hst⟩
  have hl (D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      ∀ v ∈ (K.edgeComponentComplex D).vertices,
        IsConnected ((K.edgeComponentComplex D).link v).space := by
    intro v hv
    rw [← SimplicialComplex.faceLink_singleton_eq_link,
      K.edgeComponentComplex_vertex_link D hv, SimplicialComplex.faceLink_singleton_eq_link]
    exact hlinks v (K.edgeComponentComplex_le D hv)
  have hsame : r false = r true := by
    by_contra hne
    have hsingle (s : Finset E) (hs : s ∈ (K.edgeComponentComplex (r false)).faces) :
        (∃ side, s ∈ (J side).faces) ↔ s ∈ (J false).faces := by
      rw [hmem (r false) s hs]
      constructor
      · rintro ⟨⟨side, hside⟩, hs⟩
        cases side
        · exact hs
        · exact False.elim (hne hside.symm)
      · intro hs
        exact ⟨⟨false, rfl⟩, hs⟩
    obtain ⟨hbij, hlocal⟩ := source_model_component_rim_data phi theta F0 K (J false) hK
      Hmodel F hFc hHF (r false) (hr false) (originalIntervalEndpoint false)
      (originalIntervalEndpoint_norm false) (delta false) (hdelta false) hinj hU collar hbase
    apply false_of_single_generating_essential_rim (K.edgeComponentComplex (r false)) (J false)
      (hK.subset (K.edgeComponentComplex_le _)) (hp _) (hl _)
      (K.edgeComponentComplex_isPathConnected _) (hr false)
      (gamma false) (hgamma false) ?_ (delta false) hbij hlocal
    intro s hs hsc
    rw [K.edgeComponentComplex_cofaces (r false) hs 3, hcofaces s hs.1 hsc]
    simp only [hsingle s hs]
  have hJD (side : Bool) : J side ≤ K.edgeComponentComplex (r false) := by
    cases side
    · exact hr false
    · simpa only [hsame] using hr true
  refine ⟨r false, hJD, hK.subset (K.edgeComponentComplex_le _), hp _, hl _,
    K.edgeComponentComplex_isPathConnected _, ?_, ?_⟩
  · intro s hs hsc
    rw [K.edgeComponentComplex_cofaces (r false) hs 3]
    exact hcofaces s hs.1 hsc
  · intro side
    obtain ⟨hbij, hlocal⟩ := source_model_component_rim_data phi theta F0 K (J side) hK
      Hmodel F hFc hHF (r false) (hJD side) (originalIntervalEndpoint side)
      (originalIntervalEndpoint_norm side) (delta side) (hdelta side) hinj hU collar hbase
    refine ⟨?_, hlocal⟩
    rw [FundamentalGroup.map_comp] at hbij
    exact (Function.Bijective.of_comp_iff _ ((delta side).fundamentalGroupMulEquiv 0).bijective).mp hbij

end PoincareConjecture.M76.HamiltonIntervalTorus
