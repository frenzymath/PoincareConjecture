import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcSubarc
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcClosure
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcPush
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.Admissible
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.TriangleRegion










set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]




theorem IsSimplePolygonalArc.consecutive_subarc_closed_region {n : ℕ}
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (hdim : Module.finrank ℝ E = 2) (a b : Fin (n + 2)) (hab : a ≠ b)
    (ha0 : a ≠ 0) (hal : a ≠ Fin.last (n + 1))
    (hb0 : b ≠ 0) (hbl : b ≠ Fin.last (n + 1))
    {k : ℕ} (hk : k + 1 = Nat.dist a.val b.val) (q : Polygon E (k + 2))
    (hvertices : ∀ j : Fin (k + 2), q j = polygonLinearParameter p
      (if a < b then (a.val : ℝ) + j.val else (a.val : ℝ) - j.val))
    (hclose : Disjoint (openSegment ℝ (p a) (p b)) (polygonArcBoundary p))
    (h0 : p 0 ∈ polygonExterior q)
    (hl : p (Fin.last (n + 1)) ∈ polygonExterior q) :
    IsSimplePolygon q ∧
      polygonArcBoundary q = polygonLinearParameter p ''
        Icc (min (a.val : ℝ) (b.val : ℝ)) (max (a.val : ℝ) (b.val : ℝ)) ∧
      q.boundary ℝ = polygonLinearParameter p ''
        Icc (min (a.val : ℝ) (b.val : ℝ)) (max (a.val : ℝ) (b.val : ℝ)) ∪
          segment ℝ (p a) (p b) ∧
      polygonLinearParameter p '' Ico 0 (min (a.val : ℝ) (b.val : ℝ)) ⊆
        polygonExterior q ∧
      polygonLinearParameter p '' Ioc (max (a.val : ℝ) (b.val : ℝ)) (n + 1 : ℕ) ⊆
        polygonExterior q ∧
      polygonArcBoundary p ∩ closure (polygonInterior q) = polygonArcBoundary q := by
  obtain ⟨k', q', hk', hq', hfirst, hlast, hvertices', _, hboundary', _⟩ :=
    hp.exists_consecutive_subarc a b hab
  have hkk : k' = k := by omega
  subst k'
  have heq : q' = q := by
    cases q' with
    | mk v =>
      cases q with
      | mk w =>
        congr 1
        funext j
        exact (hvertices' j).trans (hvertices j).symm
  subst q'
  let l : ℝ := min (a.val : ℝ) (b.val : ℝ)
  let u : ℝ := max (a.val : ℝ) (b.val : ℝ)
  let T := polygonLinearParameter p '' Icc l u
  have haR : (a.val : ℝ) < (n + 1 : ℕ) := by
    exact_mod_cast Fin.lt_last_iff_ne_last.mpr hal
  have hbR : (b.val : ℝ) < (n + 1 : ℕ) := by
    exact_mod_cast Fin.lt_last_iff_ne_last.mpr hbl
  have haPos : 0 < (a.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => ha0 (Fin.ext h))
  have hbPos : 0 < (b.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hb0 (Fin.ext h))
  have hlPos : 0 < l := lt_min haPos hbPos
  have huN : u < (n + 1 : ℕ) := max_lt haR hbR
  have hlu : l ≤ u := min_le_max
  have hinterval : Icc l u ⊆ Icc (0 : ℝ) (n + 1 : ℕ) := by
    intro t ht
    exact ⟨hlPos.le.trans ht.1, ht.2.trans huN.le⟩
  have hTsub : T ⊆ polygonArcBoundary p := by
    rw [← image_polygonLinearParameter_arc p]
    exact image_mono hinterval
  have hqclose : Disjoint (openSegment ℝ (q (Fin.last (k + 1))) (q 0))
      (polygonArcBoundary q) := by
    rw [hlast, hfirst, openSegment_symm, hboundary']
    exact hclose.mono_right hTsub
  obtain ⟨_, hq, hclosed⟩ := hq'.isSimplePolygon_of_closing_disjoint hqclose
  have hboundary : q.boundary ℝ = T ∪ segment ℝ (p a) (p b) := by
    rw [hclosed, hboundary', hlast, hfirst, segment_symm]
  have hpa : p a ∈ T :=
    ⟨a.val, ⟨min_le_left _ _, le_max_left _ _⟩, polygonLinearParameter_natVertex p a⟩
  have hpb : p b ∈ T :=
    ⟨b.val, ⟨min_le_right _ _, le_max_right _ _⟩, polygonLinearParameter_natVertex p b⟩
  have htail (S : Set ℝ) (hS : S ⊆ Icc (0 : ℝ) (n + 1 : ℕ))
      (hnot : ∀ t ∈ S, t ∉ Icc l u) :
      polygonLinearParameter p '' S ⊆ (q.boundary ℝ)ᶜ := by
    rintro x ⟨t, ht, rfl⟩ hx
    have htG : polygonLinearParameter p t ∈ polygonArcBoundary p := by
      rw [← image_polygonLinearParameter_arc p]
      exact ⟨t, hS ht, rfl⟩
    have htT : polygonLinearParameter p t ∉ T := by
      rintro ⟨s, hs, hst⟩
      have heq := hp.injOn_polygonLinearParameter (hinterval hs) (hS ht) hst
      exact hnot t ht (heq ▸ hs)
    rw [hboundary] at hx
    rcases hx with hx | hx
    · exact htT hx
    · rw [← insert_endpoints_openSegment] at hx
      rcases hx with ha | hb | hopen
      · exact htT (ha.symm ▸ hpa)
      · exact htT (hb.symm ▸ hpb)
      · exact Set.disjoint_left.mp hclose hopen htG
  have hleftDom : Ico (0 : ℝ) l ⊆ Icc (0 : ℝ) (n + 1 : ℕ) := by
    intro t ht
    exact ⟨ht.1, ht.2.le.trans (hlu.trans huN.le)⟩
  have hrightDom : Ioc u (n + 1 : ℕ) ⊆ Icc (0 : ℝ) (n + 1 : ℕ) := by
    intro t ht
    exact ⟨hlPos.le.trans (hlu.trans ht.1.le), ht.2⟩
  have hleftAvoid := htail (Ico 0 l) hleftDom (by
    intro t ht htu
    exact (not_lt_of_ge htu.1) ht.2)
  have hrightAvoid := htail (Ioc u (n + 1 : ℕ)) hrightDom (by
    intro t ht htu
    exact (not_lt_of_ge htu.2) ht.1)
  have hcont : Continuous (polygonLinearParameter p) := by
    have h : Continuous (fun x : Unit × ℝ => polygonLinearParameter p x.2) :=
      continuous_polygonLinearParameter (p := fun _ : Unit => p) (fun _ => continuous_const)
    exact h.comp (show Continuous (fun t : ℝ => ((), t)) from
      continuous_const.prodMk continuous_id)
  obtain ⟨hI, hO, _, _, hdis, hcover, _⟩ := hq.polygonRegions_spec hdim
  have hz : polygonLinearParameter p 0 = p 0 := by
    simpa only [Fin.val_zero, Nat.cast_zero] using polygonLinearParameter_natVertex p 0
  have hN : polygonLinearParameter p (n + 1 : ℕ) = p (Fin.last (n + 1)) :=
    polygonLinearParameter_natVertex p (Fin.last (n + 1))
  have hleft : polygonLinearParameter p '' Ico 0 l ⊆ polygonExterior q := by
    apply (isPreconnected_Ico.image _ hcont.continuousOn).subset_right_of_subset_union
      hI hO hdis (by rw [hcover]; exact hleftAvoid)
    exact ⟨p 0, ⟨0, ⟨le_rfl, hlPos⟩, hz⟩, h0⟩
  have hright : polygonLinearParameter p '' Ioc u (n + 1 : ℕ) ⊆
      polygonExterior q := by
    apply (isPreconnected_Ioc.image _ hcont.continuousOn).subset_right_of_subset_union
      hI hO hdis (by rw [hcover]; exact hrightAvoid)
    exact ⟨p (Fin.last (n + 1)), ⟨(n + 1 : ℕ), ⟨huN, le_rfl⟩, hN⟩, hl⟩
  refine ⟨hq, hboundary', hboundary, hleft, hright, ?_⟩
  rw [hboundary']
  apply subset_antisymm
  · rintro x ⟨hxG, hxI⟩
    rw [← image_polygonLinearParameter_arc p] at hxG
    obtain ⟨t, ht, rfl⟩ := hxG
    by_cases htl : t < l
    · have hh := hleft ⟨t, ⟨ht.1, htl⟩, rfl⟩
      rw [hq.polygonExterior_eq_compl_closure_interior hdim] at hh
      exact (hh hxI).elim
    · by_cases htu : u < t
      · have hh := hright ⟨t, ⟨htu, ht.2⟩, rfl⟩
        rw [hq.polygonExterior_eq_compl_closure_interior hdim] at hh
        exact (hh hxI).elim
      · exact ⟨t, ⟨le_of_not_gt htl, le_of_not_gt htu⟩, rfl⟩
  · intro x hx
    refine ⟨hTsub hx, ?_⟩
    rw [hq.closure_polygonInterior hdim, hboundary]
    exact Or.inr (Or.inl hx)




theorem IsSimplePolygonalArc.exists_admissible_between_of_visible_subarc {n : ℕ}
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (hdim : Module.finrank ℝ E = 2) (a b : Fin (n + 2)) (hab : a ≠ b)
    (ha0 : a ≠ 0) (hal : a ≠ Fin.last (n + 1))
    (hb0 : b ≠ 0) (hbl : b ≠ Fin.last (n + 1))
    {k : ℕ} (hk : k + 1 = Nat.dist a.val b.val) (q : Polygon E (k + 2))
    (hvertices : ∀ j : Fin (k + 2), q j = polygonLinearParameter p
      (if a < b then (a.val : ℝ) + j.val else (a.val : ℝ) - j.val))
    (hclose : Disjoint (openSegment ℝ (p a) (p b)) (polygonArcBoundary p))
    (h0 : p 0 ∈ polygonExterior q)
    (hl : p (Fin.last (n + 1)) ∈ polygonExterior q) :
    ∃ i : Fin (n + 2), min a.val b.val < i.val ∧ i.val < max a.val b.val ∧
      IsAdmissibleArcVertex p i ∧
      polygonVertexTriangle p i ⊆ closure (polygonInterior q) := by
  obtain ⟨hq, _, _, _, _, hcontact⟩ := hp.consecutive_subarc_closed_region hdim a b hab
    ha0 hal hb0 hbl hk q hvertices hclose h0 hl
  have hinc (h : a < b) : a.val + (k + 1) = b.val := by
    rw [Nat.dist_eq_sub_of_le (show a.val ≤ b.val from h.le)] at hk
    omega
  have hdec (h : ¬ a < b) : b.val + (k + 1) = a.val := by
    rw [Nat.dist_eq_sub_of_le_right (show b.val ≤ a.val from le_of_not_gt h)] at hk
    omega
  let f : Fin (k + 2) → Fin (n + 2) := fun j =>
    ⟨if a < b then a.val + j.val else a.val - j.val, by
      split_ifs with h
      · have := hinc h
        omega
      · have := hdec h
        omega⟩
  have hqf (j : Fin (k + 2)) : q j = p (f j) := by
    rw [hvertices j, ← polygonLinearParameter_natVertex p (f j)]
    congr 1
    by_cases h : a < b
    · simp only [f, if_pos h, Nat.cast_add]
    · have hj : j.val ≤ a.val := by have := hdec h; omega
      simp only [f, if_neg h, Nat.cast_sub hj]
  have hinner (j : Fin (k + 2)) (hj0 : j ≠ 0) (hjl : j ≠ Fin.last (k + 1)) :
      min a.val b.val < (f j).val ∧ (f j).val < max a.val b.val ∧
      f j ≠ 0 ∧ f j ≠ Fin.last (n + 1) ∧
      polygonVertexTriangle q j = polygonVertexTriangle p (f j) ∧
      segment ℝ (q j) (q ((finRotate (k + 2)).symm j)) ∪
          segment ℝ (q j) (q (finRotate (k + 2) j)) =
        segment ℝ (p (f j)) (p ((finRotate (n + 2)).symm (f j))) ∪
          segment ℝ (p (f j)) (p (finRotate (n + 2) (f j))) := by
    have hjpos : 0 < j.val := Nat.pos_of_ne_zero (fun h => hj0 (Fin.ext h))
    have hjlt : j.val < k + 1 := Fin.lt_last_iff_ne_last.mpr hjl
    have hbetween : min a.val b.val < (f j).val ∧ (f j).val < max a.val b.val := by
      by_cases h : a < b
      · have := hinc h
        simp only [f, if_pos h]
        constructor <;> omega
      · have hba : b.val ≤ a.val := le_of_not_gt h
        have := hdec h
        simp only [f, if_neg h, min_eq_right hba, max_eq_left hba]
        constructor <;> omega
    have hi0 : f j ≠ 0 := by
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_zero] at hv
      omega
    have hil : f j ≠ Fin.last (n + 1) := by
      have ha : a.val < n + 1 := Fin.lt_last_iff_ne_last.mpr hal
      have hb : b.val < n + 1 := Fin.lt_last_iff_ne_last.mpr hbl
      intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_last] at hv
      have := max_lt ha hb
      omega
    have hjp := coe_finRotate_symm_of_ne_zero hj0
    have hjs := coe_finRotate_of_ne_last hjl
    have hip := coe_finRotate_symm_of_ne_zero hi0
    have his := coe_finRotate_of_ne_last hil
    by_cases h : a < b
    · have hpred : f ((finRotate (k + 2)).symm j) =
          (finRotate (n + 2)).symm (f j) := by
        apply Fin.ext
        rw [hip]
        simp only [f, if_pos h, hjp]
        omega
      have hsucc : f (finRotate (k + 2) j) = finRotate (n + 2) (f j) := by
        apply Fin.ext
        rw [his]
        simp only [f, if_pos h, hjs]
        omega
      refine ⟨hbetween.1, hbetween.2, hi0, hil, ?_, ?_⟩
      · simp only [polygonVertexTriangle, hqf, hpred, hsucc]
      · simp only [hqf, hpred, hsucc]
    · have hpred : f ((finRotate (k + 2)).symm j) = finRotate (n + 2) (f j) := by
        apply Fin.ext
        rw [his]
        simp only [f, if_neg h, hjp]
        have := hdec h
        omega
      have hsucc : f (finRotate (k + 2) j) = (finRotate (n + 2)).symm (f j) := by
        apply Fin.ext
        rw [hip]
        simp only [f, if_neg h, hjs]
        have := hdec h
        omega
      refine ⟨hbetween.1, hbetween.2, hi0, hil, ?_, ?_⟩
      · simp only [polygonVertexTriangle, hqf, hpred, hsucc]
        congr 1
        rw [pair_comm]
      · simp only [hqf, hpred, hsucc]
        exact union_comm _ _
  by_cases hlarge : 3 < k + 2
  · obtain ⟨j, hjl, hj0, had, hT⟩ :=
      hq.exists_admissible_vertex_away_edge hdim hlarge (Fin.last (k + 1))
    rw [finRotate_last] at hj0
    obtain ⟨hlo, hhi, hi0, hil, hTeq, hSeg⟩ := hinner j hj0 hjl
    have hT' : polygonVertexTriangle p (f j) ⊆ closure (polygonInterior q) := hTeq ▸ hT
    refine ⟨f j, hlo, hhi, ⟨hi0, hil, ?_⟩, hT'⟩
    apply subset_antisymm _ (polygonArcIncidentEdges_subset_triangle_inter_boundary p _ hi0 hil)
    rintro x ⟨hxT, hxG⟩
    have hxarc : x ∈ polygonArcBoundary q := hcontact ▸ ⟨hxG, hT' hxT⟩
    obtain ⟨e, he⟩ := mem_iUnion.mp hxarc
    have hxq : x ∈ polygonVertexTriangle q j ∩ q.boundary ℝ :=
      ⟨hTeq.symm ▸ hxT, polygon_edgeSet_subset_boundary q e.castSucc he⟩
    rw [had, hSeg] at hxq
    exact hxq
  · have hkone : k = 1 := by have := hq.three_le; omega
    subst k
    obtain ⟨hlo, hhi, hi0, hil, hTeq, hSeg⟩ :=
      hinner (1 : Fin 3) (by decide) (by decide)
    have hpred : (finRotate 3).symm (1 : Fin 3) = 0 := by decide
    have hsucc : finRotate 3 (1 : Fin 3) = 2 := by decide
    have hrange : range q = {q 1, q 0, q 2} := by
      ext x
      constructor
      · rintro ⟨j, rfl⟩
        fin_cases j <;> simp
      · rintro (rfl | rfl | rfl)
        · exact ⟨1, rfl⟩
        · exact ⟨0, rfl⟩
        · exact ⟨2, rfl⟩
    have hqt : polygonVertexTriangle q (1 : Fin 3) = closure (polygonInterior q) := by
      rw [hq.triangle_closure_polygonInterior hdim, hrange]
      simp only [polygonVertexTriangle, hpred, hsucc]
    have hqarc : polygonArcBoundary q =
        segment ℝ (q 1) (q ((finRotate 3).symm 1)) ∪
          segment ℝ (q 1) (q (finRotate 3 1)) := by
      rw [hpred, hsucc]
      apply subset_antisymm
      · rintro x hx
        obtain ⟨e, he⟩ := mem_iUnion.mp hx
        fin_cases e
        · left
          rw [polygon_arcEdge_eq_segment] at he
          exact (segment_symm ℝ (q 0) (q 1)) ▸ he
        · right
          rw [polygon_arcEdge_eq_segment] at he
          exact he
      · rintro x (hx | hx)
        · apply polygon_arcEdge_subset_boundary q (0 : Fin 2)
          rw [polygon_arcEdge_eq_segment, segment_symm]
          exact hx
        · apply polygon_arcEdge_subset_boundary q (1 : Fin 2)
          rw [polygon_arcEdge_eq_segment]
          exact hx
    have hTi : polygonVertexTriangle p (f 1) = closure (polygonInterior q) :=
      hTeq.symm.trans hqt
    refine ⟨f 1, hlo, hhi, ⟨hi0, hil, ?_⟩, hTi.le⟩
    rw [hTi, inter_comm, hcontact, hqarc, hSeg]

end PoincareConjecture.M25.Topology3D
