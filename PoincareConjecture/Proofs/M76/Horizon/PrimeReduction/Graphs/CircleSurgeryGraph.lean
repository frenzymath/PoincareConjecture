import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.ComponentDeletion
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonGeometricInputs

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

def circleSurgeryFamily {X κ : Type*} (S : κ → Set X) (i : κ) (new : Bool → Set X) :
    ({j : κ // j ≠ i} ⊕ Bool) → Set X :=
  Sum.elim (fun j => S j.val) new

theorem circleSurgeryFamily_iUnion {X κ : Type*}
    (S : κ → Set X) (i : κ) (new : Bool → Set X) :
    (⋃ j, circleSurgeryFamily S i new j) =
      (⋃ j : {j : κ // j ≠ i}, S j.val) ∪ (new true ∪ new false) := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    cases j with
    | inl j => exact Or.inl (mem_iUnion.mpr ⟨j, hj⟩)
    | inr b =>
      cases b
      · exact Or.inr (Or.inr hj)
      · exact Or.inr (Or.inl hj)
  · rintro (hx | hx | hx)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact mem_iUnion.mpr ⟨Sum.inl j, hj⟩
    · exact mem_iUnion.mpr ⟨Sum.inr true, hx⟩
    · exact mem_iUnion.mpr ⟨Sum.inr false, hx⟩

theorem circleSurgeryFamily_spheres
    {X ι κ : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3}
    (S : κ → Set X) (i : κ) (new : Bool → Set X)
    (sS : ∀ j, ChartwisePLSphere e (S j))
    (snew : ∀ b, ChartwisePLSphere e (new b)) :
    Nonempty (∀ j, ChartwisePLSphere e (circleSurgeryFamily S i new j)) := by
  refine ⟨?_⟩
  intro j
  cases j with
  | inl j => exact sS j.val
  | inr b => exact snew b

theorem circleSurgeryFamily_pairwise_disjoint {X κ : Type*}
    (S : κ → Set X) (i : κ) (new : Bool → Set X)
    (hS : Pairwise fun j k => Disjoint (S j) (S k))
    (hnew : Disjoint (new true) (new false))
    (hother : ∀ b j, j ≠ i → Disjoint (new b) (S j)) :
    Pairwise fun j k => Disjoint (circleSurgeryFamily S i new j)
      (circleSurgeryFamily S i new k) := by
  intro j k hjk
  cases j with
  | inl j =>
    cases k with
    | inl k => exact hS (fun h => hjk (congrArg Sum.inl (Subtype.ext h)))
    | inr b => exact (hother b j.val j.property).symm
  | inr b =>
    cases k with
    | inl j => exact hother b j.val j.property
    | inr c =>
      cases b <;> cases c
      · exact (hjk rfl).elim
      · exact hnew.symm
      · exact hnew
      · exact (hjk rfl).elim

theorem circleSurgeryFamily_index_card {κ : Type*} [Finite κ] (i : κ) :
    Nat.card ({j : κ // j ≠ i} ⊕ Bool) = Nat.card κ + 1 := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  have hpos : 0 < Fintype.card κ := Fintype.card_pos_iff.mpr ⟨i⟩
  rw [Nat.card_sum, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  have hrest := Fintype.card_subtype_compl (fun j : κ => j = i)
  simp only [Fintype.card_unique] at hrest
  rw [hrest]
  simp only [Fintype.card_bool]
  omega

theorem circleSurgeryFamily_disjoint_marked {X κ : Type*}
    (S : κ → Set X) (i : κ) (new : Bool → Set X) {Z : Set X}
    (hS : Disjoint (⋃ j, S j) Z) (hnew : ∀ b, Disjoint (new b) Z) :
    Disjoint (⋃ j, circleSurgeryFamily S i new j) Z := by
  apply disjoint_left.mpr
  intro x hx hxZ
  obtain ⟨j, hj⟩ := mem_iUnion.mp hx
  cases j with
  | inl j => exact disjoint_left.mp hS (mem_iUnion.mpr ⟨j.val, hj⟩) hxZ
  | inr b => exact disjoint_left.mp (hnew b) hj hxZ

theorem circleSurgeryFamily_sdiff {X κ : Type*}
    (S : κ → Set X) (i : κ) (new : Bool → Set X) {C : Set X}
    (hnew : (new true ∪ new false) \ C = S i \ C) :
    (⋃ j, circleSurgeryFamily S i new j) \ C = (⋃ j, S j) \ C := by
  rw [circleSurgeryFamily_iUnion, union_sdiff_distrib, hnew]
  apply Subset.antisymm
  · rintro x (⟨hx, hxC⟩ | ⟨hx, hxC⟩)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact ⟨mem_iUnion.mpr ⟨j.val, hj⟩, hxC⟩
    · exact ⟨mem_iUnion.mpr ⟨i, hx⟩, hxC⟩
  · rintro x ⟨hx, hxC⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    by_cases hji : j = i
    · exact Or.inr ⟨hji ▸ hj, hxC⟩
    · exact Or.inl ⟨mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩, hxC⟩

theorem circleSurgeryFamily_inter_eq {X κ : Type*}
    (S : κ → Set X) (i : κ) (new : Bool → Set X) {t : Set X}
    (hnew : (new true ∪ new false) ∩ t = S i ∩ t) :
    (⋃ j, circleSurgeryFamily S i new j) ∩ t = (⋃ j, S j) ∩ t := by
  have hnew' : (new true ∪ new false) \ tᶜ = S i \ tᶜ := by
    simpa only [sdiff_compl] using hnew
  simpa only [sdiff_compl] using circleSurgeryFamily_sdiff S i new hnew'

theorem circleSurgeryFamily_inter {X κ : Type*}
    (S : κ → Set X) (i : κ) (new : Bool → Set X) {t L O : Set X}
    (hLO : L ⊆ O) (hother : ∀ j, j ≠ i → Disjoint O (S j))
    (hnew : (new true ∪ new false) ∩ t = (S i ∩ t) \ L) :
    (⋃ j, circleSurgeryFamily S i new j) ∩ t = ((⋃ j, S j) ∩ t) \ L := by
  rw [circleSurgeryFamily_iUnion]
  apply Subset.antisymm
  · rintro x ⟨hx, hxt⟩
    rcases hx with hx | hx
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact ⟨⟨mem_iUnion.mpr ⟨j.val, hj⟩, hxt⟩,
        fun hxL => disjoint_left.mp (hother j.val j.property) (hLO hxL) hj⟩
    · have hh := hnew.subset ⟨hx, hxt⟩
      exact ⟨⟨mem_iUnion.mpr ⟨i, hh.1.1⟩, hh.1.2⟩, hh.2⟩
  · rintro x ⟨⟨hx, hxt⟩, hxL⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp hx
    by_cases hji : j = i
    · subst j
      exact ⟨Or.inr (hnew.symm.subset ⟨⟨hj, hxt⟩, hxL⟩).1, hxt⟩
    · exact ⟨Or.inl (mem_iUnion.mpr ⟨⟨j, hji⟩, hj⟩), hxt⟩

theorem circleSurgeryFamily_graph
    {X κ : Type*} [TopologicalSpace X]
    (S : κ → Set X) (i : κ) (new : Bool → Set X)
    (Q : OpenPartialHomeomorph X V3) (G : SimplicialComplex ℝ V3)
    (C : G.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hG : G.faces.Finite) {T : Set V3} {t O : Set X}
    (hGT : G.space ⊆ T ∩ Q.target)
    (hphysical : Q.symm '' G.space = (⋃ j, S j) ∩ t)
    (hdim : ∀ a ∈ G.faces, a.card ≤ 2)
    (hinterior : ∀ v : G.vertices, (v : V3) ∈ intrinsicInterior ℝ T →
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2)
    (hexterior : ∀ v : G.vertices, (v : V3) ∉ intrinsicInterior ℝ T →
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1)
    (hfinite : (G.space ∩ intrinsicFrontier ℝ T).Finite)
    (hCO : Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ O)
    (hother : ∀ j, j ≠ i → Disjoint O (S j))
    (hnew : (new true ∪ new false) ∩ t = (S i ∩ t) \
      (Q.symm '' C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)))) :
    let G' := G.deleteEdgeComponent C
    let S' := circleSurgeryFamily S i new
    G'.faces.Finite ∧ G'.space ⊆ T ∩ Q.target ∧
      (∀ a ∈ G'.faces, a.card ≤ 2) ∧
      Q.symm '' G'.space = (⋃ j, S' j) ∩ t ∧
      (∀ v : G'.vertices, (v : V3) ∈ intrinsicInterior ℝ T →
        (G'.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 2) ∧
      (∀ v : G'.vertices, (v : V3) ∉ intrinsicInterior ℝ T →
        (G'.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1) ∧
      (G'.space ∩ intrinsicFrontier ℝ T).Finite ∧
      (∀ v : G'.vertices, (G'.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty) ∧
      G'.faces.ncard < G.faces.ncard := by
  have hne (v : G.vertices) : (G.vertexAbstractComplex.edgeGraph.neighborSet v).Nonempty := by
    by_cases hv : (v : V3) ∈ intrinsicInterior ℝ T
    · exact nonempty_of_ncard_ne_zero (by rw [hinterior v hv]; decide)
    · exact nonempty_of_ncard_ne_zero (by rw [hexterior v hv]; decide)
  have hcomp : C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3)) ⊆ G.space := by
    rintro x ⟨v, w, hvw, hx⟩
    exact (G.actual_edgeGraph_segmentCarrier_eq_space hdim hne).subset
      ⟨v.val, w.val, hvw, hx⟩
  have hsub : (G.deleteEdgeComponent C).space ⊆ G.space := by
    rw [G.deleteEdgeComponent_space C hdim hne]
    exact sdiff_subset
  have hfamily := circleSurgeryFamily_inter S i new hCO hother hnew
  have himage : Q.symm '' (G.deleteEdgeComponent C).space =
      (⋃ j, circleSurgeryFamily S i new j) ∩ t := by
    rw [G.deleteEdgeComponent_space C hdim hne,
      (Q.symm.injOn.mono (hGT.trans inter_subset_right)).image_sdiff_subset hcomp,
      hphysical, hfamily]
  refine ⟨G.deleteEdgeComponent_finite C hG, hsub.trans hGT,
    G.deleteEdgeComponent_face_card_le C hdim, himage, ?_, ?_,
    hfinite.subset (inter_subset_inter_left _ hsub),
    G.deleteEdgeComponent_no_isolated_vertices C hne,
    G.deleteEdgeComponent_faces_ncard_lt C hG⟩
  · intro v hv
    rw [G.deleteEdgeComponent_ncard_neighborSet C v]
    exact hinterior ⟨v.val, G.deleteEdgeComponent_le C v.property⟩ hv
  · intro v hv
    rw [G.deleteEdgeComponent_ncard_neighborSet C v]
    exact hexterior ⟨v.val, G.deleteEdgeComponent_le C v.property⟩ hv

end PoincareConjecture.M76
