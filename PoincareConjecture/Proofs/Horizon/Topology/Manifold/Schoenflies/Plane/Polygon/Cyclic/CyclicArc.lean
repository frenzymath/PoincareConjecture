import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.SimplePolygon

set_option autoImplicit false

open Set

namespace Poincare.Manifold.Schoenflies.Plane

variable {n : ℕ}

def cyclicArcIndex (k : Fin n) (m : ℕ) : Fin (m + 1) → Fin n :=
  fun i => (finRotate n)^[i.val] k

theorem cyclicArcIndex_zero (k : Fin n) (m : ℕ) : cyclicArcIndex k m 0 = k := rfl

theorem cyclicArcIndex_last (k : Fin n) (m : ℕ) :
    cyclicArcIndex k m (Fin.last m) = (finRotate n)^[m] k := rfl

theorem cyclicArcIndex_succ (k : Fin n) (m : ℕ) (i : Fin m) :
    cyclicArcIndex k m i.succ = finRotate n (cyclicArcIndex k m i.castSucc) := by
  exact Function.iterate_succ_apply' _ _ _

theorem cyclicArcIndex_injective (k : Fin n) {m : ℕ} (hm : m < n) :
    Function.Injective (cyclicArcIndex k m) := by
  let : NeZero n := k.neZero
  have hindex (i : Fin (m + 1)) :
      cyclicArcIndex k m i = k + (⟨i.val, by omega⟩ : Fin n) := by
    simpa only [cyclicArcIndex, finCycle_apply] using
      (congrFun (finCycle_eq_finRotate_iterate (k := (⟨i.val, by omega⟩ : Fin n))) k).symm
  intro i j hij
  rw [hindex, hindex] at hij
  have hval : (⟨i.val, by omega⟩ : Fin n) = ⟨j.val, by omega⟩ := add_left_cancel hij
  exact Fin.ext (congrArg (fun x : Fin n => x.val) hval)

def polygonArc {E : Type*} (p : Polygon E n) (k : Fin n) (m : ℕ) : Polygon E (m + 1) :=
  ⟨fun i => p (cyclicArcIndex k m i)⟩

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem polygonArc_edgeSet_castSucc (p : Polygon E n) (k : Fin n) (m : ℕ) (i : Fin m) :
    (polygonArc p k m).edgeSet ℝ i.castSucc =
      p.edgeSet ℝ (cyclicArcIndex k m i.castSucc) := by
  rw [polygon_edgeSet_eq_segment, polygon_edgeSet_eq_segment]
  change segment ℝ (p (cyclicArcIndex k m i.castSucc))
    (p (cyclicArcIndex k m (finRotate (m + 1) i.castSucc))) = _
  rw [show finRotate (m + 1) i.castSucc = i.succ from finRotate_of_lt i.isLt,
    cyclicArcIndex_succ]

theorem polygonArc_edgeSet_last (p : Polygon E n) (k : Fin n) (m : ℕ) :
    (polygonArc p k m).edgeSet ℝ (Fin.last m) =
      segment ℝ (p ((finRotate n)^[m] k)) (p k) := by
  rw [polygon_edgeSet_eq_segment]
  change segment ℝ (p (cyclicArcIndex k m (Fin.last m)))
    (p (cyclicArcIndex k m (finRotate (m + 1) (Fin.last m)))) = _
  rw [finRotate_last, cyclicArcIndex_zero, cyclicArcIndex_last]

theorem polygonArc_boundary (p : Polygon E n) (k : Fin n) (m : ℕ) :
    (polygonArc p k m).boundary ℝ =
      (⋃ i : Fin m, p.edgeSet ℝ (cyclicArcIndex k m i.castSucc)) ∪
        segment ℝ (p ((finRotate n)^[m] k)) (p k) := by
  apply subset_antisymm
  · intro x hx
    obtain ⟨i, hi⟩ := (polygon_mem_boundary_iff _ x).mp hx
    revert hi
    refine Fin.lastCases ?_ (fun j => ?_) i
    · intro hi
      exact Or.inr ((polygonArc_edgeSet_last p k m) ▸ hi)
    · intro hi
      exact Or.inl (mem_iUnion.mpr ⟨j, (polygonArc_edgeSet_castSucc p k m j) ▸ hi⟩)
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact polygon_edgeSet_subset_boundary _ i.castSucc
        ((polygonArc_edgeSet_castSucc p k m i).symm ▸ hi)
    · exact polygon_edgeSet_subset_boundary _ (Fin.last m)
        ((polygonArc_edgeSet_last p k m).symm ▸ hx)

theorem IsSimplePolygon.segment_inter_edge_subset_endpoints {p : Polygon E n}
    (hp : IsSimplePolygon p) (a b : Fin n)
    (hdiag : Disjoint (openSegment ℝ (p a) (p b)) (p.boundary ℝ)) (i : Fin n) :
    segment ℝ (p a) (p b) ∩ p.edgeSet ℝ i ⊆
      {p a, p b} ∩ {p i, p (finRotate n i)} := by
  rintro x ⟨hseg, hedge⟩
  have hend : x = p a ∨ x = p b := by
    rw [← insert_endpoints_openSegment] at hseg
    rcases hseg with ha | hb | hopen
    · exact Or.inl ha
    · exact Or.inr hb
    · exact (Set.disjoint_left.mp hdiag hopen
        (polygon_edgeSet_subset_boundary p i hedge)).elim
  refine ⟨hend, ?_⟩
  rcases hend with rfl | rfl
  · rcases (hp.vertex_mem_edgeSet_iff a i).mp hedge with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rcases (hp.vertex_mem_edgeSet_iff b i).mp hedge with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem IsSimplePolygon.isSimple_polygonArc {p : Polygon E n} (hp : IsSimplePolygon p)
    (k : Fin n) (m : ℕ) (hm2 : 2 ≤ m) (hm : m < n)
    (hdiag : Disjoint (openSegment ℝ (p k) (p ((finRotate n)^[m] k)))
      (p.boundary ℝ)) : IsSimplePolygon (polygonArc p k m) := by
  have hinj := cyclicArcIndex_injective k hm
  have hnext (i : Fin m) :
      (polygonArc p k m) (finRotate (m + 1) i.castSucc) =
        p (finRotate n (cyclicArcIndex k m i.castSucc)) := by
    change p (cyclicArcIndex k m (finRotate (m + 1) i.castSucc)) = _
    rw [show finRotate (m + 1) i.castSucc = i.succ from finRotate_of_lt i.isLt,
      cyclicArcIndex_succ]
  have hlast : (polygonArc p k m) (Fin.last m) = p ((finRotate n)^[m] k) := rfl
  have hzero : (polygonArc p k m) (finRotate (m + 1) (Fin.last m)) = p k := by
    rw [finRotate_last]
    rfl
  have hclose (i : Fin m) :
      (polygonArc p k m).edgeSet ℝ (Fin.last m) ∩
        (polygonArc p k m).edgeSet ℝ i.castSucc ⊆
      {(polygonArc p k m) (Fin.last m),
        (polygonArc p k m) (finRotate (m + 1) (Fin.last m))} ∩
      {(polygonArc p k m) i.castSucc,
        (polygonArc p k m) (finRotate (m + 1) i.castSucc)} := by
    rw [polygonArc_edgeSet_last, polygonArc_edgeSet_castSucc, hlast, hzero, hnext]
    exact hp.segment_inter_edge_subset_endpoints _ k
      (by rwa [openSegment_symm]) _
  refine ⟨by omega, hp.vertices_injective.comp hinj, ?_⟩
  intro i j
  refine Fin.lastCases ?_ (fun a => ?_) i
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · intro hne
      exact (hne rfl).elim
    · intro _
      exact hclose b
  · refine Fin.lastCases ?_ (fun b => ?_) j
    · intro _ x hx
      exact ⟨(hclose a ⟨hx.2, hx.1⟩).2, (hclose a ⟨hx.2, hx.1⟩).1⟩
    · intro hne
      rw [polygonArc_edgeSet_castSucc, polygonArc_edgeSet_castSucc, hnext, hnext]
      exact hp.edges_inter _ _ (fun hab => hne (hinj hab))

end Normed

end Poincare.Manifold.Schoenflies.Plane
