import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.SelectedCircleSurgeryFamily
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteFaceCounts

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

theorem selectedCircleSurgeryFamily_inter_subset_of_full
    {X κ : Type*} [DecidableEq κ]
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool) {T : Set X}
    (hfull : (⋃ j, circleSurgeryFamily S i new j) ∩ T ⊆ (⋃ j, S j) ∩ T) :
    (⋃ j, selectedCircleSurgeryFamily S i new b j) ∩ T ⊆ (⋃ j, S j) ∩ T :=
  (inter_subset_inter_left T (selectedCircleSurgeryFamily_subset S i new b)).trans hfull

theorem selectedCircleSurgeryFamily_contact_ncard_le
    {X κ : Type*} [DecidableEq κ]
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool) {T : Set X}
    (hfull : (⋃ j, circleSurgeryFamily S i new j) ∩ T ⊆ (⋃ j, S j) ∩ T)
    (hfinite : ((⋃ j, S j) ∩ T).Finite) :
    ((⋃ j, selectedCircleSurgeryFamily S i new b j) ∩ T).Finite ∧
      ((⋃ j, selectedCircleSurgeryFamily S i new b j) ∩ T).ncard ≤
        ((⋃ j, S j) ∩ T).ncard := by
  have hsub := selectedCircleSurgeryFamily_inter_subset_of_full S i new b hfull
  exact ⟨hfinite.subset hsub, ncard_le_ncard hsub hfinite⟩

theorem selectedCircleSurgeryFamily_original_edge_contact_counts
    {E X κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [DecidableEq E] [DecidableEq κ]
    (S : κ → Set X) (i : κ) (new : Bool → Set X) (b : Bool)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (g : E → X)
    {s : Finset E} (hs3 : s.card = 3)
    (hother : ∀ a ∈ K.faces, a.card ≤ 3 → a ≠ s →
      (⋃ j, circleSurgeryFamily S i new j) ∩ (g '' convexHull ℝ (a : Set E)) =
        (⋃ j, S j) ∩ (g '' convexHull ℝ (a : Set E)))
    (hedges : ∀ a ∈ K.faces, a.card = 2 →
      ((⋃ j, S j) ∩ (g '' convexHull ℝ (a : Set E))).Finite) :
    (∀ a ∈ K.faces, a.card = 2 →
      (⋃ j, selectedCircleSurgeryFamily S i new b j) ∩ (g '' convexHull ℝ (a : Set E)) ⊆
        (⋃ j, S j) ∩ (g '' convexHull ℝ (a : Set E))) ∧
    (∀ a ∈ K.faces, a.card = 2 →
      ((⋃ j, selectedCircleSurgeryFamily S i new b j) ∩
        (g '' convexHull ℝ (a : Set E))).Finite ∧
      ((⋃ j, selectedCircleSurgeryFamily S i new b j) ∩
        (g '' convexHull ℝ (a : Set E))).ncard ≤
      ((⋃ j, S j) ∩ (g '' convexHull ℝ (a : Set E))).ncard) ∧
    let T := ⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)
    (T ∩ ⋃ j, selectedCircleSurgeryFamily S i new b j) ⊆ (T ∩ ⋃ j, S j) ∧
    (T ∩ ⋃ j, selectedCircleSurgeryFamily S i new b j).Finite ∧
    (T ∩ ⋃ j, selectedCircleSurgeryFamily S i new b j).ncard ≤ (T ∩ ⋃ j, S j).ncard := by
  have hfull (a : Finset E) (ha : a ∈ K.faces) (ha2 : a.card = 2) :
      (⋃ j, circleSurgeryFamily S i new j) ∩ (g '' convexHull ℝ (a : Set E)) ⊆
        (⋃ j, S j) ∩ (g '' convexHull ℝ (a : Set E)) := by
    apply (hother a ha (by omega) ?_).subset
    intro has
    have hc := congrArg Finset.card has
    omega
  have hsub (a : Finset E) (ha : a ∈ K.faces) (ha2 : a.card = 2) :=
    selectedCircleSurgeryFamily_inter_subset_of_full S i new b (hfull a ha ha2)
  refine ⟨hsub, fun a ha ha2 =>
    selectedCircleSurgeryFamily_contact_ncard_le S i new b (hfull a ha ha2)
      (hedges a ha ha2), ?_⟩
  dsimp only
  have hwhole : ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
      ⋃ j, selectedCircleSurgeryFamily S i new b j) ⊆
      ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩ ⋃ j, S j) := by
    rintro x ⟨hxT, hxS⟩
    obtain ⟨a, hxa⟩ := mem_iUnion.mp hxT
    exact ⟨mem_iUnion.mpr ⟨a, hxa⟩, (hsub a.1 a.2.1 a.2.2 ⟨hxS, hxa⟩).1⟩
  have hfinite : ((⋃ a : K.FaceOfCard 2, g '' convexHull ℝ (a.1 : Set E)) ∩
      ⋃ j, S j).Finite := by
    let := K.finite_faceOfCard hK 2
    rw [iUnion_inter]
    exact Set.finite_iUnion (fun a => by
      simpa only [inter_comm] using hedges a.1 a.2.1 a.2.2)
  exact ⟨hwhole, hfinite.subset hwhole, ncard_le_ncard hwhole hfinite⟩

end PoincareConjecture.M76

namespace Geometry.SimplicialComplex

theorem faces_ncard_lt_of_le_deleteEdgeComponent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq E]
    (G : SimplicialComplex ℝ E) (hG : G.faces.Finite)
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (H : SimplicialComplex ℝ E) (hH : H ≤ G.deleteEdgeComponent C) :
    H.faces.Finite ∧ H.faces.ncard < G.faces.ncard := by
  have hdelete := G.deleteEdgeComponent_finite C hG
  exact ⟨hdelete.subset hH,
    lt_of_le_of_lt (ncard_le_ncard hH hdelete) (G.deleteEdgeComponent_faces_ncard_lt C hG)⟩

end Geometry.SimplicialComplex
