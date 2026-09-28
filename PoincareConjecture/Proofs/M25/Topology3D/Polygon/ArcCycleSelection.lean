import PoincareConjecture.Proofs.M25.Topology3D.Polygon.ArcInsideMatching










set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem vertex_mem_closed_parameter_subarc_iff {n : ℕ}
    {p : Polygon E (n + 2)} (hp : IsSimplePolygonalArc p)
    (a b w : Fin (n + 2)) :
    p w ∈ polygonLinearParameter p ''
      Icc (min (a.val : ℝ) (b.val : ℝ)) (max (a.val : ℝ) (b.val : ℝ)) ↔
      min a.val b.val ≤ w.val ∧ w.val ≤ max a.val b.val := by
  have hbound (j : Fin (n + 2)) : (j.val : ℝ) ∈ Icc (0 : ℝ) (n + 1 : ℕ) :=
    ⟨Nat.cast_nonneg _, by exact_mod_cast (show j.val ≤ n + 1 by omega)⟩
  constructor
  · rintro ⟨t, ht, he⟩
    have ht' : t ∈ Icc (0 : ℝ) (n + 1 : ℕ) :=
      ⟨(le_min (hbound a).1 (hbound b).1).trans ht.1,
        ht.2.trans (max_le (hbound a).2 (hbound b).2)⟩
    have htw := hp.injOn_polygonLinearParameter ht' (hbound w)
      (he.trans (polygonLinearParameter_natVertex p w).symm)
    rw [htw] at ht
    exact ⟨by exact_mod_cast ht.1, by exact_mod_cast ht.2⟩
  · intro hw
    refine ⟨w.val, ?_, polygonLinearParameter_natVertex p w⟩
    exact ⟨by exact_mod_cast hw.1, by exact_mod_cast hw.2⟩



theorem IsSimplePolygonalArc.exists_cycle_good_subarc [FiniteDimensional ℝ E]
    {n m : ℕ} {p : Polygon E (n + 2)} {r : Polygon E m}
    (hp : IsSimplePolygonalArc p) (hr : IsSimplePolygon r)
    (hdim : Module.finrank ℝ E = 2) (c : Fin m ↪ Fin (n + 2))
    (hc : ∀ i, r i = p (c i))
    (hint : ∀ i, c i ≠ 0 ∧ c i ≠ Fin.last (n + 1))
    (hcontact : r.boundary ℝ ∩ polygonArcBoundary p = range r)
    (hfirst : p 0 ∈ polygonExterior r)
    (hlast : p (Fin.last (n + 1)) ∈ polygonExterior r)
    (u : Fin (n + 2)) (hu0 : u ≠ 0) (hulast : u ≠ Fin.last (n + 1))
    (havoid : ∀ i, c i ≠ (finRotate (n + 2)).symm u ∧ c i ≠ finRotate (n + 2) u)
    (hvis : ∀ i, Disjoint (openSegment ℝ (p (c i)) (p (c (finRotate m i))))
      (polygonArcBoundary p))
    (hcross : ∀ i, ∃ ε : ℝ, 0 < ε ∧ ∃ W A B : Set E,
      IsOpen W ∧ r i ∈ W ∧ IsPreconnected A ∧ IsPreconnected B ∧
      A ∪ B = W \ r.boundary ℝ ∧
      (∀ t ∈ Ioo 0 ε, AffineMap.lineMap (r i)
        (p ((finRotate (n + 2)).symm (c i))) t ∈ A) ∧
      (∀ t ∈ Ioo 0 ε, AffineMap.lineMap (r i)
        (p (finRotate (n + 2) (c i))) t ∈ B)) :
    ∃ i : Fin m, ∃ k : ℕ, ∃ q : Polygon E (k + 2),
      let a := c i
      let b := c (finRotate m i)
      let T := polygonLinearParameter p '' Icc
        (min (a.val : ℝ) (b.val : ℝ)) (max (a.val : ℝ) (b.val : ℝ))
      let S := polygonLinearParameter p '' Ioo
        (min (a.val : ℝ) (b.val : ℝ)) (max (a.val : ℝ) (b.val : ℝ))
      a ≠ b ∧ k + 1 = Nat.dist a.val b.val ∧ IsSimplePolygonalArc q ∧
      q 0 = p a ∧ q (Fin.last (k + 1)) = p b ∧
      (∀ j : Fin (k + 2), q j = polygonLinearParameter p
        (if a < b then (a.val : ℝ) + j.val else (a.val : ℝ) - j.val)) ∧
      polygonArcBoundary q = T ∧ polygonArcBoundary q \ {p a, p b} = S ∧
      S ⊆ polygonInterior r ∧ T ∩ r.boundary ℝ = {p a, p b} ∧
      p u ∉ T ∧ p ((finRotate (n + 2)).symm u) ∉ T ∧
      p (finRotate (n + 2) u) ∉ T ∧
      Disjoint (openSegment ℝ (p a) (p b)) (polygonArcBoundary p) := by
  classical
  obtain ⟨M, hM, _, hfour, hregion, hq, hdisjoint, _, _⟩ :=
    hp.exists_inside_noninterlacing_matching hr hdim c hc hint hcontact hfirst hlast hcross
  let T := fun i => polygonLinearParameter p '' Icc
    (min ((c i).val : ℝ) ((c (M i)).val : ℝ))
    (max ((c i).val : ℝ) ((c (M i)).val : ℝ))
  obtain ⟨a, b, ha, hb, hab⟩ := hM.exists_two_cyclic_adjacent hfour
  have hba : b ≠ a := fun h => Set.disjoint_left.mp hab (Or.inl h) (Or.inl rfl)
  have hbm : b ≠ M a := fun h =>
    Set.disjoint_left.mp hab (Or.inr (h.trans ha)) (Or.inl rfl)
  have htwo : Disjoint (T a) (T b) := hdisjoint a b hba hbm
  have hchoose : ∃ i, M i = finRotate m i ∧ p u ∉ T i := by
    by_cases hu : p u ∈ T a
    · exact ⟨b, hb, fun hv => Set.disjoint_left.mp htwo hu hv⟩
    · exact ⟨a, ha, hu⟩
  obtain ⟨i, hi, hu⟩ := hchoose
  obtain ⟨ip, is, hipu, hisu, hpred, hsucc, _⟩ :=
    exists_arc_incident_edge_indices u hu0 hulast
  have hpval : ((finRotate (n + 2)).symm u).val + 1 = u.val := by
    rw [← hpred, ← hipu]
    rfl
  have hsval : u.val + 1 = (finRotate (n + 2) u).val := by
    rw [← hsucc, ← hisu]
    rfl
  have hexclude (w : Fin (n + 2))
      (hwa : c i ≠ w) (hwb : c (M i) ≠ w)
      (hw : w.val + 1 = u.val ∨ u.val + 1 = w.val) : p w ∉ T i := by
    intro hwT
    have hwi := (vertex_mem_closed_parameter_subarc_iff hp (c i) (c (M i)) w).mp hwT
    have hwan : (c i).val ≠ w.val := fun h => hwa (Fin.ext h)
    have hwbn : (c (M i)).val ≠ w.val := fun h => hwb (Fin.ext h)
    apply hu
    apply (vertex_mem_closed_parameter_subarc_iff hp (c i) (c (M i)) u).mpr
    omega
  have hpnot := hexclude _ (havoid i).1 (havoid (M i)).1 (Or.inl hpval)
  have hsnot := hexclude _ (havoid i).2 (havoid (M i)).2 (Or.inr hsval)
  have hne : c i ≠ c (M i) := fun h => hM.ne_self i (c.injective h).symm
  obtain ⟨k, q, hlen, hsimple, hzero, hlastq, hvertices, hboundary, hopen, _⟩ := hq i
  have hreg := hregion i
  dsimp only [T] at hu hpnot hsnot
  simp only [hi, hc] at hlen hzero hlastq hvertices hboundary hopen hreg hu hpnot hsnot hne
  exact ⟨i, k, q, hne, hlen, hsimple, hzero, hlastq, hvertices, hboundary, hopen,
    hreg.1, hreg.2, hu, hpnot, hsnot, hvis i⟩

end PoincareConjecture.M25.Topology3D
