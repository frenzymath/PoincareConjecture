import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Collars.PolygonExteriorLocalCollar
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Collars.PolygonCollarUnionGeometry
import Mathlib.Topology.UnitInterval









set_option autoImplicit false

open Set Metric BrownCollar unitInterval

namespace Polygon

theorem exists_closed_exterior_collar_inside_with_frontier {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hPW : P.boundary ℝ ⊆ W) :
    ∃ c : C(P.boundary ℝ × I, ℝ × ℝ), Topology.IsEmbedding c ∧
      (∀ a : P.boundary ℝ, c (a, 0) = a) ∧
      (∀ z, c z ∈ W) ∧
      (∀ (a : P.boundary ℝ) (t : I), 0 < (t : ℝ) → c (a, t) ∉ closure P.inside) ∧
      (∀ (a : P.boundary ℝ) (t : I), c (a, t) ∈ P.boundary ℝ ↔ t = 0) ∧
      IsCompact (closure P.inside ∪ range c) ∧
      closure P.inside ∪ range c ⊆ closure P.inside ∪ W ∧
      closure P.inside ⊆ interior (closure P.inside ∪ range c) ∧
      frontier (closure P.inside ∪ range c) ⊆ range (fun a : P.boundary ℝ => c (a, 1)) := by
  classical
  let : CompactSpace (P.boundary ℝ) := isCompact_iff_compactSpace.mp P.isCompact_boundary
  obtain ⟨U, hU, _, H, hH⟩ := P.exists_exterior_full_collar hP hinj
  let d : C(P.boundary ℝ × Ico (0 : ℝ) 1, ℝ × ℝ) :=
    ⟨fun z => ((H z : Set.compl P.inside) : ℝ × ℝ),
      continuous_subtype_val.comp (continuous_subtype_val.comp H.continuous)⟩
  have hd (a : P.boundary ℝ) : d (collarBase a) = a :=
    congrArg (fun x : Set.compl P.inside => (x : ℝ × ℝ)) (hH a)
  have hdi : Function.Injective d := by
    intro z w h
    apply H.injective
    exact Subtype.ext (Subtype.ext h)
  let t0 : Ico (0 : ℝ) 1 := ⟨0, le_rfl, zero_lt_one⟩
  have hbase : (univ : Set (P.boundary ℝ)) ×ˢ {t0} ⊆ d ⁻¹' W := by
    rintro ⟨a, t⟩ ⟨_, ht⟩
    obtain rfl := mem_singleton_iff.mp ht
    change d (collarBase a) ∈ W
    rw [hd]
    exact hPW a.property
  obtain ⟨A, V, _, hV, hA, h0V, hAV⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set (P.boundary ℝ))) isCompact_singleton
    (hW.preimage d.continuous) hbase
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.mp hV t0 (h0V (mem_singleton t0))
  let ε := min r 1 / 2
  have hε : 0 < ε := half_pos (lt_min hr zero_lt_one)
  have hεr : ε < r := (half_lt_self (lt_min hr zero_lt_one)).trans_le (min_le_left r 1)
  have hε1 : ε < 1 := (half_lt_self (lt_min hr zero_lt_one)).trans_le (min_le_right r 1)
  let scale : I → Ico (0 : ℝ) 1 := fun t =>
    ⟨ε * (t : ℝ), mul_nonneg hε.le t.property.1,
      (mul_le_of_le_one_right hε.le t.property.2).trans_lt hε1⟩
  have hscale : Continuous scale := by fun_prop
  have hscale0 : scale 0 = t0 := Subtype.ext (mul_zero ε)
  have hscaleV (t : I) : scale t ∈ V := by
    apply hrV
    change dist (ε * (t : ℝ)) 0 < r
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hε.le t.property.1)]
    exact (mul_le_of_le_one_right hε.le t.property.2).trans_lt hεr
  let c : C(P.boundary ℝ × I, ℝ × ℝ) := d.comp
    ⟨fun z => (z.1, scale z.2), continuous_fst.prodMk (hscale.comp continuous_snd)⟩
  have hcbase (a : P.boundary ℝ) : c (a, 0) = a := by
    change d (a, scale 0) = a
    rw [hscale0]
    exact hd a
  have hci : Function.Injective c := by
    intro z w h
    have heq : (z.1, scale z.2) = (w.1, scale w.2) := hdi h
    have heq1 := congrArg Prod.fst heq
    refine Prod.ext heq1 ?_
    apply Subtype.ext
    exact (mul_left_cancel₀ hε.ne') (congrArg (fun z => (z.2 : ℝ)) heq)
  have hboundary (a : P.boundary ℝ) (t : I) : c (a, t) ∈ P.boundary ℝ ↔ t = 0 := by
    constructor
    · intro hb
      have heq : c (a, t) = c (⟨c (a, t), hb⟩, 0) :=
        (hcbase ⟨c (a, t), hb⟩).symm
      exact congrArg Prod.snd (hci heq)
    · rintro rfl
      rw [hcbase]
      exact a.property
  have hcW (z) : c z ∈ W := hAV ⟨hA (mem_univ z.1), hscaleV z.2⟩
  have hcside (a : P.boundary ℝ) (t : I) (ht : 0 < (t : ℝ)) :
      c (a, t) ∉ closure P.inside := by
    intro hc
    have hnot : c (a, t) ∉ P.inside := (H (a, scale t)).val.property
    have hb : c (a, t) ∈ frontier P.inside := ⟨hc, by
      rwa [(P.isOpen_inside hP hinj).interior_eq]⟩
    rw [P.frontier_inside hP hinj] at hb
    have hz := (hboundary a t).mp hb
    rw [hz] at ht
    exact (lt_irrefl (0 : ℝ)) ht
  let band : Set (P.boundary ℝ × Ico (0 : ℝ) 1) := {z | (z.2 : ℝ) < ε}
  let V : Set (Set.compl P.inside) := Subtype.val '' (H '' band)
  have hVopen : IsOpen V := hU.isOpenMap_subtype_val _
    (H.isOpenMap _ (isOpen_lt (by fun_prop) continuous_const))
  let O : Set (ℝ × ℝ) := P.inside ∪ (Subtype.val : Set.compl P.inside → ℝ × ℝ) '' V
  have hOopen : IsOpen O := (P.isOpen_inside hP hinj).union_image_open_complement hVopen
  have hband (a : P.boundary ℝ) (t : Ico (0 : ℝ) 1) (ht : (t : ℝ) < ε) :
      d (a, t) ∈ O := Or.inr ⟨(H (a, t)).val,
        ⟨H (a, t), ⟨(a, t), ht, rfl⟩, rfl⟩, rfl⟩
  have hBO : closure P.inside ⊆ O := by
    intro x hx
    by_cases hi : x ∈ P.inside
    · exact Or.inl hi
    · have hb : x ∈ P.boundary ℝ := by
        rw [← P.frontier_inside hP hinj, frontier, (P.isOpen_inside hP hinj).interior_eq]
        exact ⟨hx, hi⟩
      have h := hband ⟨x, hb⟩ t0 hε
      rwa [show d (⟨x, hb⟩, t0) = x from hd ⟨x, hb⟩] at h
  have hOE : O ⊆ closure P.inside ∪ range c := by
    rintro x (hx | ⟨v, ⟨u, ⟨⟨a, t⟩, ht, rfl⟩, rfl⟩, rfl⟩)
    · exact Or.inl (subset_closure hx)
    · let s : I := ⟨(t : ℝ) / ε, div_nonneg t.property.1 hε.le,
        (div_le_one hε).mpr ht.le⟩
      have hst : scale s = t := by
        apply Subtype.ext
        exact mul_div_cancel₀ (t : ℝ) hε.ne'
      refine Or.inr ⟨(a, s), ?_⟩
      change d (a, scale s) = d (a, t)
      rw [hst]
  have hcO (a : P.boundary ℝ) (t : I) (ht : (t : ℝ) < 1) : c (a, t) ∈ O := by
    apply hband
    change ε * (t : ℝ) < ε
    simpa only [mul_one] using mul_lt_mul_of_pos_left ht hε
  have hEc : IsCompact (closure P.inside ∪ range c) :=
    (P.isCompact_closure_inside hP hinj).union (isCompact_range c.continuous)
  have hOi : O ⊆ interior (closure P.inside ∪ range c) := interior_maximal hOE hOopen
  refine ⟨c, (c.continuous.isClosedEmbedding hci).isEmbedding, hcbase, hcW,
    hcside, hboundary, hEc, union_subset_union_right _ (by rintro x ⟨z, rfl⟩; exact hcW z),
    hBO.trans hOi, ?_⟩
  intro x hx
  rcases hEc.isClosed.frontier_subset hx with hxB | ⟨⟨a, t⟩, rfl⟩
  · exact False.elim (hx.2 (hOi (hBO hxB)))
  · by_cases ht : t = 1
    · exact ⟨a, by rw [ht]⟩
    · have ht' : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2
        (fun h => ht (Subtype.ext h))
      exact False.elim (hx.2 (hOi (hcO a t ht')))

theorem exists_closed_exterior_collar_inside {n : ℕ}
    (P : Polygon (ℝ × ℝ) (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P) {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hPW : P.boundary ℝ ⊆ W) :
    ∃ c : C(P.boundary ℝ × I, ℝ × ℝ), Topology.IsEmbedding c ∧
      (∀ a : P.boundary ℝ, c (a, 0) = a) ∧
      (∀ z, c z ∈ W) ∧
      (∀ (a : P.boundary ℝ) (t : I), 0 < (t : ℝ) → c (a, t) ∉ closure P.inside) ∧
      ∀ (a : P.boundary ℝ) (t : I), c (a, t) ∈ P.boundary ℝ ↔ t = 0 := by
  obtain ⟨c, hi, hb, hW, hs, hf, _⟩ :=
    P.exists_closed_exterior_collar_inside_with_frontier hP hinj hW hPW
  exact ⟨c, hi, hb, hW, hs, hf⟩

end Polygon
