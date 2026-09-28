import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalBridgeBoundarySamples
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalBoundaryOrientationConsumer
import PoincareConjecture.Proofs.M76.Mathlib.SimplexExtremeFaces

set_option autoImplicit false

open Set Geometry Classical

namespace PoincareConjecture.M76.OriginalTriangleCopies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in

theorem finite_vertex_numbering (L : SimplicialComplex ℝ E) (hL : L.faces.Finite) :
    ∃ number : E → ℕ, InjOn number L.vertices := by
  let : Fintype L.vertices := (L.finite_vertices_of_finite_faces hL).fintype
  let label : L.vertices ↪ ℕ := (Fintype.equivFin L.vertices).toEmbedding.trans
    ⟨Fin.val, Fin.val_injective⟩
  let v : L.vertices ↪ E := Function.Embedding.subtype _
  let number : E → ℕ := Function.extend v label (fun _ ↦ 0)
  have hnumber (x : L.vertices) : number x = label x := v.injective.extend_apply _ _ x
  refine ⟨number, ?_⟩
  intro x hx y hy he
  have he' : label ⟨x, hx⟩ = label ⟨y, hy⟩ := by
    rw [← hnumber, ← hnumber]
    exact he
  exact congrArg Subtype.val (label.injective he')

theorem unitSquareSide_lineMap (i : Fin 4) (r s t : ℝ) :
    unitSquareSide i (AffineMap.lineMap r s t) =
      AffineMap.lineMap (unitSquareSide i r) (unitSquareSide i s) t := by
  fin_cases i <;> ext <;> simp [unitSquareSide, AffineMap.lineMap_apply_module] <;> ring

theorem unitSquareSide_mem_openSegment_iff (i : Fin 4) (q r s : ℝ) (hrs : r < s) :
    unitSquareSide i q ∈ openSegment ℝ (unitSquareSide i r) (unitSquareSide i s) ↔
      q ∈ Ioo r s := by
  rw [← openSegment_eq_Ioo hrs, openSegment_eq_image_lineMap, openSegment_eq_image_lineMap]
  constructor
  · rintro ⟨t, ht, he⟩
    exact ⟨t, ht, unitSquareSide_injective i ((unitSquareSide_lineMap i r s t).trans he)⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, ht, (unitSquareSide_lineMap i r s t).symm⟩

theorem refined_boundary_edge_endpoints_in_original_face
    (K : SimplicialComplex ℝ E) (L : SimplicialComplex ℝ (ℝ × ℝ))
    (F : (ℝ × ℝ) → E) (hF : L.AffineOnFaces F)
    {t : Finset (ℝ × ℝ)} (ht : t ∈ L.faces)
    {T e : Finset E} (hT : T ∈ K.faces) (heT : e ⊆ T)
    (hmap : MapsTo F (convexHull ℝ (t : Set (ℝ × ℝ))) (convexHull ℝ (T : Set E)))
    {a b z : ℝ × ℝ} (ha : a ∈ t) (hb : b ∈ t)
    (hz : z ∈ openSegment ℝ a b) (hze : F z ∈ convexHull ℝ (e : Set E)) :
    F a ∈ convexHull ℝ (e : Set E) ∧ F b ∈ convexHull ℝ (e : Set E) := by
  obtain ⟨G, hG⟩ := hF t ht
  have ha' : a ∈ convexHull ℝ (t : Set (ℝ × ℝ)) := subset_convexHull ℝ _ ha
  have hb' : b ∈ convexHull ℝ (t : Set (ℝ × ℝ)) := subset_convexHull ℝ _ hb
  have hz' : z ∈ convexHull ℝ (t : Set (ℝ × ℝ)) :=
    (convex_convexHull ℝ _).segment_subset ha' hb' (openSegment_subset_segment ℝ a b hz)
  have hseg : F z ∈ openSegment ℝ (F a) (F b) := by
    rw [hG hz', hG ha', hG hb']
    rw [openSegment_eq_image_lineMap] at hz ⊢
    obtain ⟨r, hr, rfl⟩ := hz
    exact ⟨r, hr, (G.toAffineMap.apply_lineMap a b r).symm⟩
  have hext := (K.indep hT).isExtreme_convexHull_finset_subset heT
  exact ⟨hext.left_mem_of_mem_openSegment (hmap ha') (hmap hb') hze hseg,
    hext.right_mem_of_mem_openSegment (hmap ha') (hmap hb') hze hseg⟩

private theorem coordinate_eq_of_strict_combination_zero
    {a b r s : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hr : 0 < r) (hs : 0 < s)
    (h : r * a + s * b = 0) : a = 0 ∧ b = 0 := by
  have hra : r * a = 0 := le_antisymm (by nlinarith [mul_nonneg hs.le hb])
    (mul_nonneg hr.le ha)
  have hsb : s * b = 0 := by linarith
  exact ⟨(mul_eq_zero.mp hra).resolve_left hr.ne', (mul_eq_zero.mp hsb).resolve_left hs.ne'⟩

theorem unitSquare_edge_on_sample_side
    {a b z : ℝ × ℝ} (ha : a ∈ PeriodicSquare.squareCarrier 1)
    (hb : b ∈ PeriodicSquare.squareCarrier 1) (hz : z ∈ openSegment ℝ a b)
    (i : Fin 4) (q : ℝ) (hzq : z = unitSquareSide i q) :
    ∃ r s : ℝ, r ∈ Icc (0 : ℝ) 1 ∧ s ∈ Icc (0 : ℝ) 1 ∧
      a = unitSquareSide i r ∧ b = unitSquareSide i s := by
  change (0 ≤ a.1 ∧ a.1 ≤ 1) ∧ (0 ≤ a.2 ∧ a.2 ≤ 1) at ha
  change (0 ≤ b.1 ∧ b.1 ≤ 1) ∧ (0 ≤ b.2 ∧ b.2 ≤ 1) at hb
  obtain ⟨u, v, hu, hv, huv, hval⟩ := hz
  have hc1 : u * a.1 + v * b.1 = (unitSquareSide i q).1 := by
    simpa using congrArg Prod.fst (hval.trans hzq)
  have hc2 : u * a.2 + v * b.2 = (unitSquareSide i q).2 := by
    simpa using congrArg Prod.snd (hval.trans hzq)
  fin_cases i
  · have he := coordinate_eq_of_strict_combination_zero ha.2.1 hb.2.1 hu hv hc2
    exact ⟨a.1, b.1, ha.1, hb.1, by ext <;> simp [unitSquareSide, he.1],
      by ext <;> simp [unitSquareSide, he.2]⟩
  · have hz0 : u * (1 - a.1) + v * (1 - b.1) = 0 := by
      change u * a.1 + v * b.1 = 1 at hc1
      nlinarith
    obtain ⟨he1, he2⟩ := coordinate_eq_of_strict_combination_zero
      (sub_nonneg.mpr ha.1.2) (sub_nonneg.mpr hb.1.2) hu hv hz0
    have he1 : a.1 = 1 := by linarith
    have he2 : b.1 = 1 := by linarith
    exact ⟨a.2, b.2, ha.2, hb.2, by ext <;> simp [unitSquareSide, he1],
      by ext <;> simp [unitSquareSide, he2]⟩
  · have hz0 : u * (1 - a.2) + v * (1 - b.2) = 0 := by
      change u * a.2 + v * b.2 = 1 at hc2
      nlinarith
    obtain ⟨he1, he2⟩ := coordinate_eq_of_strict_combination_zero
      (sub_nonneg.mpr ha.2.2) (sub_nonneg.mpr hb.2.2) hu hv hz0
    have he1 : a.2 = 1 := by linarith
    have he2 : b.2 = 1 := by linarith
    exact ⟨1 - a.1, 1 - b.1, ⟨by linarith [ha.1.2], by linarith [ha.1.1]⟩,
      ⟨by linarith [hb.1.2], by linarith [hb.1.1]⟩,
      by ext <;> simp [unitSquareSide, he1], by ext <;> simp [unitSquareSide, he2]⟩
  · have he := coordinate_eq_of_strict_combination_zero ha.1.1 hb.1.1 hu hv hc1
    exact ⟨1 - a.2, 1 - b.2, ⟨by linarith [ha.2.2], by linarith [ha.2.1]⟩,
      ⟨by linarith [hb.2.2], by linarith [hb.2.1]⟩,
      by ext <;> simp [unitSquareSide, he.1], by ext <;> simp [unitSquareSide, he.2]⟩

theorem exists_ordered_square_sample_edge
    (L : SimplicialComplex ℝ (ℝ × ℝ)) (hL : L.faces.Finite)
    (hLs : L.space = PeriodicSquare.squareCarrier 1)
    {z : ℝ × ℝ} (hz : z ∈ frontier L.space) (hzv : z ∉ L.vertices)
    (i : Fin 4) (q : ℝ) (hzq : z = unitSquareSide i q) :
    ∃ (r s : ℝ) (t : Finset (ℝ × ℝ)),
      r ∈ Icc (0 : ℝ) 1 ∧ s ∈ Icc (0 : ℝ) 1 ∧ r < s ∧
      ({unitSquareSide i r, unitSquareSide i s} : Finset (ℝ × ℝ)) ∈
        (L.frontierSubcomplex L.space).faces ∧
      z ∈ openSegment ℝ (unitSquareSide i r) (unitSquareSide i s) ∧
      t ∈ L.faces ∧ t.card = 3 ∧
      ({unitSquareSide i r, unitSquareSide i s} : Finset (ℝ × ℝ)) ⊆ t := by
  obtain ⟨a, b, t, hab, he, _, _, hzab, ht, htc, het⟩ :=
    L.square_nonvertex_boundary_edge_coface hL hLs hz hzv
  have ha : a ∈ PeriodicSquare.squareCarrier 1 :=
    hLs ▸ L.subset_space he.1 (by simp)
  have hb : b ∈ PeriodicSquare.squareCarrier 1 :=
    hLs ▸ L.subset_space he.1 (by simp)
  obtain ⟨r, s, hr, hs, har, hbs⟩ := unitSquare_edge_on_sample_side ha hb hzab i q hzq
  have hrs : r ≠ s := fun h ↦ hab (har.trans (h ▸ hbs.symm))
  rw [har, hbs] at he hzab het
  rcases lt_or_gt_of_ne hrs with h | h
  · exact ⟨r, s, t, hr, hs, h, he, hzab, ht, htc, het⟩
  · refine ⟨s, r, t, hs, hr, h, ?_, ?_, ht, htc, ?_⟩
    · simpa only [Finset.pair_comm] using he
    · simpa only [openSegment_symm] using hzab
    · simpa only [Finset.pair_comm] using het

end PoincareConjecture.M76.OriginalTriangleCopies
