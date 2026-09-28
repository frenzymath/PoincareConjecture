import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.RimComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Surfaces.Components.ModelComponents

set_option autoImplicit false
open Set Metric PoincareConjecture.M76

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in
theorem exists_component_circle_rims
    (K B : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if s ∈ B.faces then 1 else 2)
    {m : ℕ} (J : Fin m → SimplicialComplex ℝ E)
    (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (J i).space)
    (hJ : ∀ i, J i ≤ B ∧ J i ≤ K ∧ (J i).faces.Finite ∧ (gamma i).IsFinitePL)
    (hdis : Pairwise (fun i j => Disjoint (J i).space (J j).space))
    (hcover : (⋃ i, (J i).space) = B.space)
    (hfaces : ∀ s, s ∈ B.faces ↔ ∃ i, s ∈ (J i).faces) :
    ∃ r : Fin m → K.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∀ i D, r i = D ↔ J i ≤ K.edgeComponentComplex D) ∧
      ∀ D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent,
        (K.edgeComponentComplex D).faces.Finite ∧
        (∀ s ∈ (K.edgeComponentComplex D).faces,
          ∃ t ∈ (K.edgeComponentComplex D).faces, t.card = 3 ∧ s ⊆ t) ∧
        (∀ v ∈ (K.edgeComponentComplex D).vertices,
          IsConnected ((K.edgeComponentComplex D).link v).space) ∧
        IsPathConnected (K.edgeComponentComplex D).space ∧
        (∀ x ∈ (K.edgeComponentComplex D).space,
          connectedComponentIn K.space x = (K.edgeComponentComplex D).space) ∧
        (∀ i : {i : Fin m // r i = D}, J i.val ≤ K.edgeComponentComplex D ∧
          J i.val ≤ B ∧ (J i.val).faces.Finite ∧ (gamma i.val).IsFinitePL) ∧
        Pairwise (fun i j : {i : Fin m // r i = D} => Disjoint (J i.val).space (J j.val).space) ∧
        (⋃ i : {i : Fin m // r i = D}, (J i.val).space) =
          (K.edgeComponentComplex D).space ∩ B.space ∧
        (∀ s ∈ (K.edgeComponentComplex D).faces,
          s ∈ B.faces ↔ ∃ i : {i : Fin m // r i = D}, s ∈ (J i.val).faces) ∧
        ∀ s ∈ (K.edgeComponentComplex D).faces, s.card = 2 →
          {t : Finset E | t ∈ (K.edgeComponentComplex D).faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
            if ∃ i : {i : Fin m // r i = D}, s ∈ (J i.val).faces then 1 else 2 := by
  classical
  have hconn (i : Fin m) : IsConnected (J i).space :=
    (Dehn.Annuli.circle_incidence (J i) (hJ i).2.2.1 (gamma i) (hJ i).2.2.2).2.2.1
  obtain ⟨r, hr, hmem⟩ := Dehn.Annuli.exists_rim_component_assignment
    K hK J (fun i => (hJ i).2.1) hconn
  have hassign (i : Fin m) (D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent) :
      r i = D ↔ J i ≤ K.edgeComponentComplex D := by
    constructor
    · rintro rfl
      exact hr i
    · intro hiD
      obtain ⟨x, hx⟩ := (hconn i).nonempty
      exact (Dehn.Annuli.mem_component_of_assigned_rim_iff K (J i) (r i) D (hr i) hx).mp
        (space_subset_of_le hiD hx)
  refine ⟨r, hassign, ?_⟩
  intro D
  have hJD (i : {i : Fin m // r i = D}) : J i.val ≤ K.edgeComponentComplex D :=
    (hassign i.val D).mp i.property
  have hmarked (s : Finset E) (hs : s ∈ (K.edgeComponentComplex D).faces) :
      s ∈ B.faces ↔ ∃ i : {i : Fin m // r i = D}, s ∈ (J i.val).faces :=
    (hfaces s).trans (hmem D s hs)
  refine ⟨hK.subset (K.edgeComponentComplex_le D), ?_, ?_,
    K.edgeComponentComplex_isPathConnected D,
    fun _ hx => HamiltonIntervalTorus.edgeComponentComplex_connectedComponentIn K hK D hx,
    fun i => ⟨hJD i, (hJ i.val).1, (hJ i.val).2.2⟩, ?_, ?_, hmarked, ?_⟩
  · intro s hs
    obtain ⟨t, ht, htc, hst⟩ := hpure s hs.1
    exact ⟨t, K.edgeComponentComplex_coface D hs ht hst, htc, hst⟩
  · intro v hv
    rw [← faceLink_singleton_eq_link, K.edgeComponentComplex_vertex_link D hv,
      faceLink_singleton_eq_link]
    exact hlinks v (K.edgeComponentComplex_le D hv)
  · intro i j hij
    exact hdis (fun heq => hij (Subtype.ext heq))
  · ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact ⟨space_subset_of_le (hJD i) hi, space_subset_of_le (hJ i.val).1 hi⟩
    · rintro ⟨hxD, hxB⟩
      obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover.symm.subset hxB)
      have hiD : r i = D :=
        (Dehn.Annuli.mem_component_of_assigned_rim_iff K (J i) (r i) D (hr i) hxi).mp hxD
      exact mem_iUnion.mpr ⟨⟨i, hiD⟩, hxi⟩
  · intro s hs hsc
    rw [K.edgeComponentComplex_cofaces D hs 3, hcofaces s hs.1 hsc]
    simp only [hmarked s hs]

end Geometry.SimplicialComplex
