import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.Reduction.AdmissibleVertex











set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

section Update

variable {E : Type*} {n : ℕ}


def polygonReplaceVertex (p : Polygon E n) (k : Fin n) (x : E) : Polygon E n :=
  ⟨Function.update p.vertices k x⟩


theorem polygonReplaceVertex_apply_same (p : Polygon E n) (k : Fin n) (x : E) :
    polygonReplaceVertex p k x k = x := by
  simp [polygonReplaceVertex]


theorem polygonReplaceVertex_apply_of_ne (p : Polygon E n) (k : Fin n) (x : E)
    {j : Fin n} (hj : j ≠ k) : polygonReplaceVertex p k x j = p j := by
  exact Function.update_of_ne hj _ _


theorem polygonReplaceVertex_self (p : Polygon E n) (k : Fin n) :
    polygonReplaceVertex p k (p k) = p := by
  cases p
  simp [polygonReplaceVertex]

end Update

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ} {p : Polygon E n}



theorem IsSimplePolygon.vertex_mem_triangle_iff_of_admissible (hp : IsSimplePolygon p)
    (k : Fin n) (had : IsAdmissibleVertex p k) (j : Fin n) :
    p j ∈ polygonVertexTriangle p k ↔
      j = k ∨ j = (finRotate n).symm k ∨ j = finRotate n k := by
  constructor
  · intro hj
    have hC : p j ∈ polygonVertexTriangle p k ∩ p.boundary ℝ :=
      ⟨hj, polygon_vertex_mem_boundary p j⟩
    change polygonVertexTriangle p k ∩ p.boundary ℝ = _ at had
    rw [had] at hC
    rcases hC with hC | hC
    · have he : p j ∈ p.edgeSet ℝ ((finRotate n).symm k) := by
        rw [polygon_edgeSet_eq_segment, Equiv.apply_symm_apply, segment_symm]
        exact hC
      rcases (hp.vertex_mem_edgeSet_iff j _).mp he with hjp | hjk
      · exact Or.inr (Or.inl hjp)
      · exact Or.inl (by simpa only [Equiv.apply_symm_apply] using hjk)
    · exact ((hp.vertex_mem_edgeSet_iff j k).mp
        ((polygon_edgeSet_eq_segment p k).symm ▸ hC)).elim Or.inl (Or.inr ∘ Or.inr)
  · intro hj
    apply subset_convexHull ℝ _
    rcases hj with rfl | rfl | rfl <;> simp



theorem IsSimplePolygon.triangle_inter_edge_subset_of_admissible (hp : IsSimplePolygon p)
    (k : Fin n) (had : IsAdmissibleVertex p k) (i : Fin n)
    (hik : i ≠ k) (hip : i ≠ (finRotate n).symm k) :
    polygonVertexTriangle p k ∩ p.edgeSet ℝ i ⊆
      {p ((finRotate n).symm k), p (finRotate n k)} ∩ {p i, p (finRotate n i)} := by
  rintro z ⟨hzT, hzi⟩
  have hzk : z ≠ p k := by
    intro heq
    have hki := (hp.vertex_mem_edgeSet_iff k i).mp (heq ▸ hzi)
    rcases hki with hki | hki
    · exact hik hki.symm
    · apply hip
      simpa only [Equiv.symm_apply_apply] using (congrArg (finRotate n).symm hki).symm
  have hC : z ∈ polygonVertexTriangle p k ∩ p.boundary ℝ :=
    ⟨hzT, polygon_edgeSet_subset_boundary p i hzi⟩
  change polygonVertexTriangle p k ∩ p.boundary ℝ = _ at had
  rw [had] at hC
  rcases hC with hC | hC
  · have hzpred : z ∈ p.edgeSet ℝ ((finRotate n).symm k) := by
      rw [polygon_edgeSet_eq_segment, Equiv.apply_symm_apply, segment_symm]
      exact hC
    have hends := hp.edges_inter _ i hip.symm ⟨hzpred, hzi⟩
    rw [Equiv.apply_symm_apply] at hends
    exact ⟨Or.inl (hends.1.resolve_right hzk), hends.2⟩
  · have hends := hp.edges_inter k i hik.symm
      ⟨(polygon_edgeSet_eq_segment p k).symm ▸ hC, hzi⟩
    exact ⟨Or.inr (hends.1.resolve_left hzk), hends.2⟩



theorem IsSimplePolygon.isSimple_polygonReplaceVertex_of_admissible (hp : IsSimplePolygon p)
    (k : Fin n) (had : IsAdmissibleVertex p k) (x : E)
    (hxT : x ∈ polygonVertexTriangle p k)
    (hxa : x ≠ p ((finRotate n).symm k)) (hxb : x ≠ p (finRotate n k))
    (hinter : segment ℝ x (p ((finRotate n).symm k)) ∩
      segment ℝ x (p (finRotate n k)) = {x}) :
    IsSimplePolygon (polygonReplaceVertex p k x) := by
  let q := polygonReplaceVertex p k x
  have hpk : (finRotate n).symm k ≠ k := by
    intro h
    have hrot := congrArg (finRotate n) h
    rw [Equiv.apply_symm_apply] at hrot
    exact hp.hasNondegenerateEdges k (congrArg p hrot)
  have hsk : finRotate n k ≠ k :=
    fun h => hp.hasNondegenerateEdges k (congrArg p h.symm)
  have hqk : q k = x := polygonReplaceVertex_apply_same p k x
  have hqother (j : Fin n) (hj : j ≠ k) : q j = p j :=
    polygonReplaceVertex_apply_of_ne p k x hj
  have hqpred : q ((finRotate n).symm k) = p ((finRotate n).symm k) := hqother _ hpk
  have hqsucc : q (finRotate n k) = p (finRotate n k) := hqother _ hsk
  have hunchanged (i : Fin n) (hik : i ≠ k) (hip : i ≠ (finRotate n).symm k) :
      q i = p i ∧ q (finRotate n i) = p (finRotate n i) := by
    refine ⟨hqother i hik, hqother _ ?_⟩
    intro h
    apply hip
    simpa only [Equiv.symm_apply_apply] using congrArg (finRotate n).symm h
  have hqedge (i : Fin n) (hik : i ≠ k) (hip : i ≠ (finRotate n).symm k) :
      q.edgeSet ℝ i = p.edgeSet ℝ i := by
    rw [polygon_edgeSet_eq_segment, (hunchanged i hik hip).1,
      (hunchanged i hik hip).2, polygon_edgeSet_eq_segment]
  have hqedgepred : q.edgeSet ℝ ((finRotate n).symm k) =
      segment ℝ x (p ((finRotate n).symm k)) := by
    rw [polygon_edgeSet_eq_segment, Equiv.apply_symm_apply, hqpred, hqk, segment_symm]
  have hqedgek : q.edgeSet ℝ k = segment ℝ x (p (finRotate n k)) := by
    rw [polygon_edgeSet_eq_segment, hqk, hqsucc]
  have haT : p ((finRotate n).symm k) ∈ polygonVertexTriangle p k :=
    subset_convexHull ℝ _ (by simp)
  have hbT : p (finRotate n k) ∈ polygonVertexTriangle p k :=
    subset_convexHull ℝ _ (by simp)
  have hA : segment ℝ x (p ((finRotate n).symm k)) ⊆ polygonVertexTriangle p k :=
    (convex_convexHull ℝ _).segment_subset hxT haT
  have hB : segment ℝ x (p (finRotate n k)) ⊆ polygonVertexTriangle p k :=
    (convex_convexHull ℝ _).segment_subset hxT hbT
  have hxne (j : Fin n) (hj : j ≠ k) : x ≠ p j := by
    intro h
    have hcorner := (hp.vertex_mem_triangle_iff_of_admissible k had j).mp (h ▸ hxT)
    rcases hcorner with hcorner | hcorner | hcorner
    · exact hj hcorner
    · exact hxa (h.trans (congrArg p hcorner))
    · exact hxb (h.trans (congrArg p hcorner))
  have hincident (i j : Fin n) (hi : i = (finRotate n).symm k ∨ i = k)
      (hjk : j ≠ k) (hjp : j ≠ (finRotate n).symm k) :
      q.edgeSet ℝ i ∩ q.edgeSet ℝ j ⊆
        {q i, q (finRotate n i)} ∩ {q j, q (finRotate n j)} := by
    rcases hi with hi | hi
    · subst i
      rintro z ⟨hzA, hzj⟩
      rw [hqedgepred] at hzA
      rw [hqedge j hjk hjp] at hzj
      have hends := hp.triangle_inter_edge_subset_of_admissible k had j hjk hjp ⟨hA hzA, hzj⟩
      have hznb : z ≠ p (finRotate n k) := by
        intro h
        have hbA : p (finRotate n k) ∈ segment ℝ x (p ((finRotate n).symm k)) := h ▸ hzA
        have hbx : p (finRotate n k) ∈ ({x} : Set E) :=
          hinter ▸ ⟨hbA, right_mem_segment ℝ _ _⟩
        exact hxb (mem_singleton_iff.mp hbx).symm
      have hza := hends.1.resolve_right hznb
      refine ⟨Or.inl ?_, ?_⟩
      · rw [hqpred]
        exact hza
      · simpa only [(hunchanged j hjk hjp).1, (hunchanged j hjk hjp).2] using hends.2
    · subst i
      rintro z ⟨hzB, hzj⟩
      rw [hqedgek] at hzB
      rw [hqedge j hjk hjp] at hzj
      have hends := hp.triangle_inter_edge_subset_of_admissible k had j hjk hjp ⟨hB hzB, hzj⟩
      have hzna : z ≠ p ((finRotate n).symm k) := by
        intro h
        have haB : p ((finRotate n).symm k) ∈ segment ℝ x (p (finRotate n k)) := h ▸ hzB
        have hax : p ((finRotate n).symm k) ∈ ({x} : Set E) :=
          hinter ▸ ⟨right_mem_segment ℝ _ _, haB⟩
        exact hxa (mem_singleton_iff.mp hax).symm
      have hzb := hends.1.resolve_left hzna
      refine ⟨Or.inr ?_, ?_⟩
      · rw [hqsucc]
        exact hzb
      · simpa only [(hunchanged j hjk hjp).1, (hunchanged j hjk hjp).2] using hends.2
  refine ⟨hp.three_le, ?_, ?_⟩
  · intro i j hij
    by_cases hik : i = k
    · subst i
      by_cases hjk : j = k
      · exact hjk.symm
      · exact (hxne j hjk (hqk.symm.trans (hij.trans (hqother j hjk)))).elim
    · by_cases hjk : j = k
      · subst j
        exact (hxne i hik (hqk.symm.trans (hij.symm.trans (hqother i hik)))).elim
      · exact hp.vertices_injective ((hqother i hik).symm.trans (hij.trans (hqother j hjk)))
  · intro i j hij z hz
    change z ∈ {q i, q (finRotate n i)} ∩ {q j, q (finRotate n j)}
    change z ∈ q.edgeSet ℝ i ∩ q.edgeSet ℝ j at hz
    by_cases hi : i = (finRotate n).symm k ∨ i = k
    · by_cases hj : j = (finRotate n).symm k ∨ j = k
      · rcases hi with hi | hi <;> rcases hj with hj | hj
        · exact (hij (hi.trans hj.symm)).elim
        · subst i
          subst j
          have hzx : z ∈ ({x} : Set E) :=
            hinter ▸ (by simpa only [hqedgepred, hqedgek] using hz)
          change z = x at hzx
          simp only [Equiv.apply_symm_apply, hqpred, hqk, hqsucc]
          exact ⟨Or.inr hzx, Or.inl hzx⟩
        · subst i
          subst j
          have hswap : z ∈ q.edgeSet ℝ ((finRotate n).symm k) ∩ q.edgeSet ℝ k :=
            ⟨hz.2, hz.1⟩
          rw [hqedgepred, hqedgek] at hswap
          have hzx : z ∈ ({x} : Set E) := hinter ▸ hswap
          change z = x at hzx
          simp only [Equiv.apply_symm_apply, hqpred, hqk, hqsucc]
          exact ⟨Or.inl hzx, Or.inr hzx⟩
        · exact (hij (hi.trans hj.symm)).elim
      · exact hincident i j hi (not_or.mp hj).2 (not_or.mp hj).1 hz
    · by_cases hj : j = (finRotate n).symm k ∨ j = k
      · have h := hincident j i hj (not_or.mp hi).2 (not_or.mp hi).1 ⟨hz.2, hz.1⟩
        exact ⟨h.2, h.1⟩
      · have hi' := not_or.mp hi
        have hj' := not_or.mp hj
        rw [hqedge i hi'.2 hi'.1, hqedge j hj'.2 hj'.1] at hz
        simpa only [(hunchanged i hi'.2 hi'.1).1, (hunchanged i hi'.2 hi'.1).2,
          (hunchanged j hj'.2 hj'.1).1, (hunchanged j hj'.2 hj'.1).2] using
          hp.edges_inter i j hij hz

end Poincare.Manifold.Schoenflies.Plane
