import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Polygons.TriangleEdgeSection
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.TwoCofaceCarrierGerm
import PoincareConjecture.Proofs.M76.Mathlib.PositiveFaceCenterAtPoint











set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
private theorem exists_signed_edge_vertices
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    (hs2 : s.card = 2) (A : E →ᵃ[ℝ] ℝ) {p : E}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hpzero : A p = 0) (hne : ∃ v ∈ s, A v ≠ 0) :
    ∃ u v : E, u ≠ v ∧ s = {u, v} ∧ A u < 0 ∧ 0 < A v ∧
      p = A.zeroCrossing u v := by
  classical
  obtain ⟨u, v, huv, hsuv⟩ := Finset.card_eq_two.mp hs2
  obtain ⟨w, hw, hsum, hval⟩ :=
    (K.indep hs).exists_positive_weights_of_mem_intrinsicInterior hp
  have hwu := hw u (hsuv.symm ▸ Finset.mem_insert_self _ _)
  have hwv := hw v (hsuv.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hsum' : w u + w v = 1 := by simpa only [hsuv, Finset.sum_pair huv] using hsum
  have hline : AffineMap.lineMap u v (w v) = p := by
    rw [AffineMap.lineMap_apply_module, show 1 - w v = w u by linarith]
    simpa only [hsuv, Finset.sum_pair huv] using hval
  have hbalance : w u * A u + w v * A v = 0 := by
    have h := congrArg A hline
    rw [A.apply_lineMap, AffineMap.lineMap_apply_module,
      show 1 - w v = w u by linarith, hpzero] at h
    simpa only [smul_eq_mul] using h
  have hn : A u ≠ 0 ∨ A v ≠ 0 := by
    obtain ⟨z, hz, hzero⟩ := hne
    simp only [hsuv, Finset.mem_insert, Finset.mem_singleton] at hz
    exact hz.elim (fun h => Or.inl (h ▸ hzero)) (fun h => Or.inr (h ▸ hzero))
  have hpSpan : p ∈ affineSpan ℝ ({u, v} : Set E) := by
    rw [← Finset.coe_pair, ← hsuv]
    exact convexHull_subset_affineSpan _ (intrinsicInterior_subset hp)
  by_cases hu : A u < 0
  · have hv : 0 < A v := by
      by_contra h
      have h0 := mul_nonpos_of_nonneg_of_nonpos hwv.le (le_of_not_gt h)
      have h1 := mul_neg_of_pos_of_neg hwu hu
      linarith
    exact ⟨u, v, huv, hsuv, hu, hv,
      A.eq_zeroCrossing_of_mem_affineSpan (hu.trans hv).ne hpSpan hpzero⟩
  · have hv : A v < 0 := by
      by_contra h
      have hu0 : 0 ≤ A u := le_of_not_gt hu
      have hv0 : 0 ≤ A v := le_of_not_gt h
      rcases hn with hn | hn
      · have h1 := mul_pos hwu (lt_of_le_of_ne hu0 (Ne.symm hn))
        have h0 := mul_nonneg hwv.le hv0
        linarith
      · have h1 := mul_pos hwv (lt_of_le_of_ne hv0 (Ne.symm hn))
        have h0 := mul_nonneg hwu.le hu0
        linarith
    have hu' : 0 < A u := by
      by_contra h
      have h0 := mul_nonpos_of_nonneg_of_nonpos hwu.le (le_of_not_gt h)
      have h1 := mul_neg_of_pos_of_neg hwv hv
      linarith
    refine ⟨v, u, huv.symm, hsuv.trans (Finset.pair_comm _ _), hv, hu', ?_⟩
    exact A.eq_zeroCrossing_of_mem_affineSpan (hv.trans hu').ne
      (by simpa only [pair_comm] using hpSpan) hpzero



theorem exists_transverse_edge_pair_segments
    (K : SimplicialComplex ℝ E) {s a b : Finset E}
    (hs : s ∈ K.faces) (hs2 : s.card = 2)
    (ha : a ∈ K.faces) (hb : b ∈ K.faces) (ha3 : a.card = 3) (hb3 : b.card = 3)
    (hsa : s ⊆ a) (hsb : s ⊆ b) (hab : a ≠ b)
    (A : E →ᵃ[ℝ] ℝ) {p : E}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hpzero : A p = 0) (hne : ∃ v ∈ s, A v ≠ 0) :
    ∃ u v : E, u ≠ p ∧ v ≠ p ∧
      convexHull ℝ (a : Set E) ∩ {x | A x = 0} = segment ℝ p u ∧
      convexHull ℝ (b : Set E) ∩ {x | A x = 0} = segment ℝ p v ∧
      segment ℝ p u ∩ segment ℝ p v = {p} := by
  classical
  obtain ⟨u, v, _, hsuv, hu, hv, hpCross⟩ :=
    K.exists_signed_edge_vertices hs hs2 A hp hpzero hne
  have hsection (t : Finset E) (ht : t ∈ K.faces) (ht3 : t.card = 3) (hst : s ⊆ t) :
      ∃ z : E, z ≠ p ∧ convexHull ℝ (t : Set E) ∩ {x | A x = 0} = segment ℝ p z := by
    obtain ⟨w, hws, hwt⟩ := Finset.exists_eq_insert_iff.mpr ⟨hst, by omega⟩
    have hwspan : w ∉ affineSpan ℝ (s : Set E) := by
      intro hw
      have hwt' : w ∈ t := hwt ▸ Finset.mem_insert_self w s
      have himage : Subtype.val '' {x : t | (x : E) ∈ s} = (s : Set E) := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, hst hx⟩, hx, rfl⟩
      exact hws ((K.indep ht).mem_affineSpan_iff ⟨w, hwt'⟩
        {x : t | (x : E) ∈ s} |>.mp (himage.symm ▸ hw))
    rw [hsuv, Finset.coe_pair] at hwspan
    obtain ⟨z, hz, hslice⟩ := A.exists_triangle_edge_zero_segment hu hv hwspan
    refine ⟨z, hpCross.symm ▸ hz, ?_⟩
    rw [← hwt, Finset.coe_insert, hsuv, Finset.coe_pair, hpCross]
    exact hslice
  obtain ⟨z, hz, hza⟩ := hsection a ha ha3 hsa
  obtain ⟨w, hw, hwb⟩ := hsection b hb hb3 hsb
  have habs : a ∩ b = s := by
    have hle : (a ∩ b).card ≤ 2 := by
      by_contra hn
      have he : a ∩ b = a :=
        Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
      have hab' : a ⊆ b := he ▸ Finset.inter_subset_right
      exact hab (Finset.eq_of_subset_of_card_le hab' (by omega))
    exact (Finset.eq_of_subset_of_card_le (Finset.subset_inter hsa hsb) (by omega)).symm
  have hedge : convexHull ℝ (s : Set E) ∩ {x | A x = 0} = {p} := by
    rw [hsuv, Finset.coe_pair, A.convexHull_pair_inter_zero hu hv, ← hpCross]
  refine ⟨z, w, hz, hw, hza, hwb, Subset.antisymm ?_ ?_⟩
  · rintro y ⟨hya, hyb⟩
    have hya' := hza.symm.subset hya
    have hyb' := hwb.symm.subset hyb
    apply hedge.subset
    refine ⟨?_, hya'.2⟩
    rw [← habs, Finset.coe_inter, ← K.convexHull_inter_convexHull ha hb]
    exact ⟨hya'.1, hyb'.1⟩
  · rintro y rfl
    exact ⟨left_mem_segment ℝ y z, left_mem_segment ℝ y w⟩



theorem exists_transverse_edge_two_segment_germ
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) {s a b : Finset E}
    (hs : s ∈ K.faces) (hs2 : s.card = 2)
    (ha : a ∈ K.faces) (hb : b ∈ K.faces) (ha3 : a.card = 3) (hb3 : b.card = 3)
    (hsa : s ⊆ a) (hsb : s ⊆ b) (hab : a ≠ b)
    (hcofaces : ∀ t ∈ K.faces, s ⊆ t → t ⊆ a ∨ t ⊆ b)
    (A : E →ᵃ[ℝ] ℝ) {p : E}
    (hp : p ∈ intrinsicInterior ℝ (convexHull ℝ (s : Set E)))
    (hpzero : A p = 0) (hne : ∃ v ∈ s, A v ≠ 0) :
    ∃ u v : E, u ≠ p ∧ v ≠ p ∧ segment ℝ p u ∩ segment ℝ p v = {p} ∧
      ∀ᶠ x in 𝓝 p, x ∈ K.space ∩ {y | A y = 0} ↔
        x ∈ segment ℝ p u ∪ segment ℝ p v := by
  obtain ⟨u, v, hu, hv, husa, hvsb, hinter⟩ :=
    K.exists_transverse_edge_pair_segments hs hs2 ha hb ha3 hb3 hsa hsb hab A hp hpzero hne
  obtain ⟨U, hU, hpU, hlocal⟩ := K.exists_open_two_coface_carrier_germ hK hs ha hb hcofaces hp
  refine ⟨u, v, hu, hv, hinter, ?_⟩
  filter_upwards [hU.mem_nhds hpU] with x hx
  rw [← husa, ← hvsb]
  have h := hlocal x hx
  simp only [mem_inter_iff, mem_union] at h ⊢
  tauto

end Geometry.SimplicialComplex
