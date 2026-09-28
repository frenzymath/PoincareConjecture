import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.PairedMarkedModel
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage
import PoincareConjecture.Proofs.M76.Mathlib.FiniteMarkedPolygonSubdivision










set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
  {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}



theorem OrdinaryIntervalMarkedModel.selected_graph_finitePL
    (D : OrdinaryIntervalMarkedModel old i) :
    FinitePiecewiseAffineOn (D.graph ∘ f) (old.pieces i) ∧
      InjOn (D.graph ∘ f) (old.pieces i) ∧
      (D.graph ∘ f) '' old.pieces i = (D.marks (.inr 2)).space := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [D.selected_clip] using (D.clips_data 2).2.2.1
  · intro x hx y hy hxy
    exact old.injOn_piece_of_mate_ne i D.mate_ne hx hy
      (D.graph_separates (f x) (interior_subset (D.core_neighborhood ⟨x, hx, rfl⟩))
        (f y) hxy)
  · simpa only [D.selected_clip] using (D.clips_data 2).2.2.2


theorem OrdinaryIntervalMarkedModel.exists_model_circle_parameter [T2Space X]
    (D : OrdinaryIntervalMarkedModel old i) (a : Q2 ≃ₜ old.pieces i) (ha : a.IsFinitePL) :
    ∃ b : Q2 ≃ₜ (D.marks (.inr 2)).space,
      b.IsFinitePL ∧ b.symm.IsFinitePL ∧
      (∀ u : Q2, (b u : D.sample → ℝ × V3) = D.graph (f (a u))) ∧
      (∀ u : Q2, (D.inverse (b u) : X) = f (a u)) ∧
      IsEmbedding (fun u : Q2 ↦ f (a u)) ∧
      IsEmbedding (fun z : (D.marks (.inr 2)).space ↦ (D.inverse z : X)) ∧
      (fun z ↦ (D.inverse z : X)) '' (D.marks (.inr 2)).space = f '' old.pieces i := by
  obtain ⟨hPL, hinj, himage⟩ := D.selected_graph_finitePL
  obtain ⟨q, hq, hqval⟩ := hPL.exists_homeomorph_image hinj
  let q' := q.trans (Homeomorph.setCongr himage)
  have hq' : q'.IsFinitePL := by
    obtain ⟨g, hg, hgval⟩ := hq
    exact ⟨g, hg, hgval⟩
  let b := a.trans q'
  have hb : b.IsFinitePL := ha.trans hq'
  have hbval (u : Q2) : (b u : D.sample → ℝ × V3) = D.graph (f (a u)) := hqval (a u)
  have hgb (u : Q2) : (D.inverse (b u) : X) = f (a u) := by
    have hcore : f (a u) ∈ D.core := interior_subset (D.core_neighborhood ⟨a u, (a u).property, rfl⟩)
    have hH : (b u : D.sample → ℝ × V3) =
        D.homeomorph ⟨f (a u), hcore⟩ :=
      (hbval u).trans (D.homeomorph_value ⟨f (a u), hcore⟩).symm
    rw [hH, D.inverse_value, D.homeomorph.symm_apply_apply]
  have hmarkK : (D.marks (.inr 2)).space ⊆ D.complex.space :=
    SimplicialComplex.space_subset_of_le (D.marks_full (.inr 2)).1
  have hc : Continuous (fun z : (D.marks (.inr 2)).space ↦ (D.inverse z : X)) :=
    (D.inverse_PL.continuousOn.mono hmarkK).domRestrict
  have hi' : Function.Injective (fun z : (D.marks (.inr 2)).space ↦ (D.inverse z : X)) := by
    intro z w h
    apply Subtype.ext
    have h' := congrArg D.graph h
    rwa [D.graph_inverse _ (hmarkK z.property), D.graph_inverse _ (hmarkK w.property)] at h'
  have : CompactSpace (D.marks (.inr 2)).space := isCompact_iff_compactSpace.mp
    ((D.marks (.inr 2)).isCompact_space_of_finite (D.marks_full (.inr 2)).2.1)
  have hemb := (hc.isClosedEmbedding hi').isEmbedding
  have haemb : IsEmbedding (fun u : Q2 ↦ f (a u)) := by
    have h := hemb.comp b.isEmbedding
    convert h using 1
    funext u
    exact (hgb u).symm
  refine ⟨b, hb, hb.symm, hbval, hgb, haemb, hemb, ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    simpa only [D.selected_source] using
      (D.mem_mark_image (D.marks_image 2) z (hmarkK hz)).mp hz
  · rintro _ ⟨x, hx, rfl⟩
    let u := a.symm ⟨x, hx⟩
    refine ⟨b u, (b u).property, ?_⟩
    exact (hgb u).trans (congrArg f (congrArg Subtype.val (a.apply_symm_apply ⟨x, hx⟩)))



theorem OrdinaryIntervalMarkedModel.exists_model_circle_polygon
    (D : OrdinaryIntervalMarkedModel old i) {n : ℕ} (P : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hPs : P.boundary ℝ = old.pieces i) :
    ∃ (m : ℕ) (Q : Polygon (D.sample → ℝ × V3) (m + 3)), Function.Injective Q ∧
      Q.HasSimplicialEdges ∧ Q.boundary ℝ = (D.marks (.inr 2)).space := by
  obtain ⟨hPL, hinj, himage⟩ := D.selected_graph_finitePL
  obtain ⟨m, Q, hQi, hQ, hQs⟩ := P.exists_polygon_finitePL_image hP hPi hPL hPs.subset
    (hinj.mono hPs.subset)
  exact ⟨m, Q, hQi, hQ, hQs.trans (by rw [hPs, himage])⟩



theorem OrdinaryIntervalMarkedModel.exists_model_circle_polygon_with_vertices
    (D : OrdinaryIntervalMarkedModel old i) {n : ℕ} (P : Polygon V2 (n + 3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hPs : P.boundary ℝ = old.pieces i) :
    ∃ (m : ℕ) (Q : Polygon (D.sample → ℝ × V3) (m + 3)), Function.Injective Q ∧
      Q.HasSimplicialEdges ∧ Q.boundary ℝ = (D.marks (.inr 2)).space ∧
      (D.marks (.inr 2)).vertices ⊆ range Q := by
  classical
  obtain ⟨m, Q, hQi, hQ, hQs⟩ := D.exists_model_circle_polygon P hP hPi hPs
  obtain ⟨k, W, hW, hWi, hWs, hretain⟩ := Q.exists_subdivision_at_finite_marks hQ hQi
    ((D.marks (.inr 2)).finite_vertices_of_finite_faces (D.marks_full (.inr 2)).2.1)
    (hQs.symm ▸ (D.marks (.inr 2)).vertices_subset_space)
  exact ⟨k, W, hWi, hW, hWs.trans hQs, fun z hz ↦ hretain (Or.inr hz)⟩

end PoincareConjecture.M76.Dehn
