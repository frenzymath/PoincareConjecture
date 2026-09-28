import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.RelativeTriangleChains
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.CircleIncidence
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SubcomplexFaceInclusion

set_option autoImplicit false
open Set Metric Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (K L : SimplicialComplex ℝ E) [Fintype K.vertices]

local notation "KA" => K.vertexAbstractComplex.toPreAbstractSimplicialComplex

omit [FiniteDimensional ℝ E] in
open Classical in
theorem marked_edge_degree_eq_original (hLK : L ≤ K) (v : K.vertices) :
    (Finset.univ.filter (fun e : Edge KA ↦
      e.val.map (Function.Embedding.subtype _) ∈ L.faces ∧ v ∈ e.val)).card =
      {s : Finset E | s ∈ L.faces ∧ s.card = 2 ∧ (v : E) ∈ s}.ncard := by
  classical
  let emb : K.vertices ↪ E := Function.Embedding.subtype _
  rw [← ncard_coe_finset]
  apply ncard_congr (fun e _ ↦ e.val.map emb)
  · intro e he
    obtain ⟨heL, hve⟩ := (Finset.mem_filter.mp he).2
    exact ⟨heL, by simpa only [Finset.card_map] using e.property.2,
      Finset.mem_map.mpr ⟨v, hve, rfl⟩⟩
  · intro e f _ _ hef
    exact Subtype.ext (Finset.map_injective emb hef)
  · rintro s ⟨hs, hsc, hvs⟩
    let e := (K.vertexFaceEquiv 2).symm ⟨s, hLK hs, hsc⟩
    have he : e.val.map emb = s := K.vertexFaceEquiv_symm_map 2 _
    have hve : v ∈ e.val := by
      rw [← he] at hvs
      obtain ⟨w, hw, hwv⟩ := Finset.mem_map.mp hvs
      exact (Subtype.ext hwv : w = v) ▸ hw
    exact ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm ▸ hs, hve⟩, he⟩

omit [FiniteDimensional ℝ E] in
open Classical in
theorem boundary_circle_markedEdgeChain_cycle
    (hLK : L ≤ K)
    (hdegree : ∀ v ∈ L.vertices,
      {s : Finset E | s ∈ L.faces ∧ s.card = 2 ∧ v ∈ s}.ncard = 2) :
    (vertexCoboundary KA).dualMap (markedEdgeChain KA
      (fun e ↦ e.val.map (Function.Embedding.subtype _) ∈ L.faces)) = 0 := by
  classical
  apply markedEdgeChain_boundary_eq_zero_of_degrees
  intro v
  have hg : (Finset.univ.filter (fun e : Edge KA ↦
      e.val.map (Function.Embedding.subtype _) ∈ L.faces ∧ v ∈ e.val)).card = 0 ∨
    (Finset.univ.filter (fun e : Edge KA ↦
      e.val.map (Function.Embedding.subtype _) ∈ L.faces ∧ v ∈ e.val)).card = 2 := by
    rw [K.marked_edge_degree_eq_original L hLK v]
    by_cases hv : (v : E) ∈ L.vertices
    · exact Or.inr (hdegree v hv)
    · left
      have he : {s : Finset E | s ∈ L.faces ∧ s.card = 2 ∧ (v : E) ∈ s} = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        rintro s ⟨hs, _, hvs⟩
        exact hv (L.down_closed hs (Finset.singleton_subset_iff.mpr hvs)
          (Finset.singleton_nonempty _))
      rw [he, ncard_empty]
  convert hg using 1
  all_goals
    apply Iff.of_eq
    congr 2
    ext e
    simp

omit [Fintype K.vertices] in
open Classical in
theorem exists_boundary_circle_marked_edge
    (hLK : L ≤ K) (hL : L.faces.Finite)
    (gamma : sphere (0 : Fin 2 → ℝ) 1 ≃ₜ L.space) (hgamma : gamma.IsFinitePL) :
    ∃ e : Edge KA, e.val.map (Function.Embedding.subtype _) ∈ L.faces := by
  classical
  obtain ⟨_, hpure, hconn, _, _⟩ :=
    PoincareConjecture.M76.Dehn.Annuli.circle_incidence L hL gamma hgamma
  obtain ⟨x, hx⟩ := hconn.nonempty
  obtain ⟨s, hs, _⟩ := mem_space_iff.mp hx
  obtain ⟨t, ht, htc, _⟩ := hpure s hs
  let e := (K.vertexFaceEquiv 2).symm ⟨t, hLK ht, htc⟩
  exact ⟨e, by rw [K.vertexFaceEquiv_symm_map]; exact ht⟩

end Geometry.SimplicialComplex
