import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ConnectedSubsetComponent
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.RimSubcomplexes
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.BoundaryEulerBound

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76.Dehn.Annuli

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in
omit [FiniteDimensional ℝ E] in

theorem exists_rim_component_assignment
    {ι : Type*} (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (B : ι → SimplicialComplex ℝ E) (hBK : ∀ i, B i ≤ K)
    (hconn : ∀ i, IsConnected (B i).space) :
    ∃ r : ι → K.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∀ i, B i ≤ K.edgeComponentComplex (r i)) ∧
      ∀ C s, s ∈ (K.edgeComponentComplex C).faces →
        ((∃ i, s ∈ (B i).faces) ↔ ∃ i : {i // r i = C}, s ∈ (B i.val).faces) := by
  classical
  have H := fun i ↦ K.exists_edgeComponentComplex_of_isConnected hK (hconn i)
    (SimplicialComplex.space_subset_of_le (hBK i))
  choose r hr using H
  have hBr (i : ι) : B i ≤ K.edgeComponentComplex (r i) := by
    let : Fintype K.faces := hK.fintype
    let : Fintype (K.edgeComponentComplex (r i)).faces :=
      (hK.subset (K.edgeComponentComplex_le (r i))).fintype
    intro s hs
    apply K.face_mem_subcomplex_of_centroid _ (K.edgeComponentComplex_le _) (hBK i hs)
    exact hr i ((B i).convexHull_subset_space hs
      (Finset.centroid_mem_convexHull _ ((B i).nonempty_of_mem_faces hs)))
  refine ⟨r, hBr, ?_⟩
  intro C s hs
  constructor
  · rintro ⟨i, hi⟩
    have heq : r i = C := by
      by_contra hne
      obtain ⟨v, hv⟩ := (B i).nonempty_of_mem_faces hi
      exact disjoint_left.mp (K.pairwise_disjoint_edgeComponentComplex_space hne)
        ((K.edgeComponentComplex (r i)).subset_space (hBr i hi) hv)
        ((K.edgeComponentComplex C).subset_space hs hv)
    exact ⟨⟨i, heq⟩, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨i.val, hi⟩

open Classical in
omit [FiniteDimensional ℝ E] in

theorem mem_component_of_assigned_rim_iff
    (K B : SimplicialComplex ℝ E)
    (C D : K.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hBC : B ≤ K.edgeComponentComplex C) {x : E} (hx : x ∈ B.space) :
    x ∈ (K.edgeComponentComplex D).space ↔ C = D := by
  have hxC := SimplicialComplex.space_subset_of_le hBC hx
  constructor
  · intro hxD
    by_contra hne
    exact disjoint_left.mp (K.pairwise_disjoint_edgeComponentComplex_space hne) hxC hxD
  · rintro rfl
    exact hxC

open Classical in

theorem exists_component_boundary_euler_bounds
    {ι : Type*} [Finite ι] (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (B : ι → SimplicialComplex ℝ E) (hBK : ∀ i, B i ≤ K)
    (hdis : Pairwise (fun i j ↦ Disjoint (B i).space (B j).space))
    (gamma : ∀ i, sphere (0 : Fin 2 → ℝ) 1 ≃ₜ (B i).space)
    (hgamma : ∀ i, (gamma i).IsFinitePL)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
        if ∃ i, s ∈ (B i).faces then 1 else 2) :
    ∃ r : ι → K.vertexAbstractComplex.edgeGraph.ConnectedComponent,
      (∀ i, B i ≤ K.edgeComponentComplex (r i)) ∧
      ∀ C, (K.edgeComponentComplex C).surfaceEulerCount ≤
        2 - (Nat.card {i // r i = C} : ℤ) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hconn (i : ι) : IsConnected (B i).space := (circle_incidence (B i)
    (hK.subset (hBK i)) (gamma i) (hgamma i)).2.2.1
  obtain ⟨r, hr, hmem⟩ := exists_rim_component_assignment K hK B hBK hconn
  refine ⟨r, hr, ?_⟩
  intro C
  apply (K.edgeComponentComplex C).surfaceEulerCount_le_two_sub_boundary_circle_count
    (hK.subset (K.edgeComponentComplex_le C)) ?_
    (K.edgeComponentComplex_isPathConnected C).isConnected ?_
    (fun i : {i // r i = C} ↦ B i.val) ?_ ?_
    (fun i ↦ gamma i.val) (fun i ↦ hgamma i.val) ?_
  · intro s hs
    obtain ⟨t, ht, htc, hst⟩ := hpure s hs.1
    exact ⟨t, K.edgeComponentComplex_coface C hs ht hst, htc, hst⟩
  · intro v hv
    rw [← SimplicialComplex.faceLink_singleton_eq_link,
      K.edgeComponentComplex_vertex_link C hv,
      SimplicialComplex.faceLink_singleton_eq_link]
    exact hlinks v (K.edgeComponentComplex_le C hv)
  · intro i
    simpa only [i.property] using hr i.val
  · intro i j hij
    exact hdis (fun heq ↦ hij (Subtype.ext heq))
  · intro s hs hsc
    rw [K.edgeComponentComplex_cofaces C hs 3, hcofaces s hs.1 hsc, hmem C s hs]
    split_ifs <;> rfl

end PoincareConjecture.M76.Dehn.Annuli
