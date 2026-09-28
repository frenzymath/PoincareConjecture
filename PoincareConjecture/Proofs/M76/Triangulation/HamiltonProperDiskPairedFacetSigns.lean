import PoincareConjecture.Proofs.M76.Triangulation.HamiltonProperDiskFacetDeterminant
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialFacetInterior
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineInjectivity

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_affineEquiv_of_injective_full_simplex
    (K : SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = Module.finrank ℝ E + 1)
    (a : E →ᵃ[ℝ] E) (ha : InjOn a (convexHull ℝ (s : Set E))) :
    ∃ A : E ≃ᵃ[ℝ] E, A.toAffineMap = a := by
  classical
  let b := (K.indep hs).affineBasisOfCard hcard
  have hspan : affineSpan ℝ (s : Set E) = ⊤ := by
    simpa only [b, AffineIndependent.range_affineBasisOfCard] using b.tot
  have hsne : (s : Set E).Nonempty := by
    exact Finset.coe_nonempty.mpr (Finset.card_pos.mp (by omega))
  have hinj := a.injOn_affineSpan_of_injOn_convex
    (convex_convexHull ℝ _) hsne.convexHull ha
  rw [affineSpan_convexHull, hspan] at hinj
  have hfull : Function.Injective a := fun x y h => hinj (by trivial) (by trivial) h
  have hl : Function.Injective a.linear := a.linear_injective_iff.mpr hfull
  have hb : Function.Bijective a := a.linear_bijective_iff.mp
    ⟨hl, LinearMap.injective_iff_surjective.mp hl⟩
  exact ⟨AffineEquiv.ofBijective hb, rfl⟩

theorem det_mul_pos_of_actual_paired_facet
    (K : SimplicialComplex ℝ E) (hdim : 0 < Module.finrank ℝ E)
    {s t u : Finset E} (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hscard : s.card = Module.finrank ℝ E)
    (htcard : t.card = Module.finrank ℝ E + 1)
    (hucard : u.card = Module.finrank ℝ E + 1)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    {f : E → E} (hf : InjOn f K.space)
    (A B : E ≃ᵃ[ℝ] E)
    (hA : EqOn A f (convexHull ℝ (t : Set E)))
    (hB : EqOn B f (convexHull ℝ (u : Set E))) :
    0 < LinearMap.det (A.linear : E →ₗ[ℝ] E) *
      LinearMap.det (B.linear : E →ₗ[ℝ] E) := by
  classical
  obtain ⟨p, hps, hpt⟩ := Finset.exists_eq_insert_iff.mpr
    (And.intro hst (show s.card + 1 = t.card by omega))
  obtain ⟨q, hqs, hqu⟩ := Finset.exists_eq_insert_iff.mpr
    (And.intro hsu (show s.card + 1 = u.card by omega))
  have hpq : p ≠ q := by
    intro he
    apply htu
    rw [← hpt, ← hqu, he]
  have hpmem : p ∈ t := by rw [← hpt]; exact Finset.mem_insert_self p s
  let i : t := ⟨p, hpmem⟩
  let b := (K.indep ht).affineBasisOfCard htcard
  have hsne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨r, hrs⟩ := hsne
  let j : t := ⟨r, hst hrs⟩
  have hij : i ≠ j := by
    intro h
    have hpr : p = r := congrArg Subtype.val h
    exact hps (hpr.symm ▸ hrs)
  have hfimage : b '' {k : t | k ≠ i} = (s : Set E) := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      change (k : E) ∈ s
      have hkp : (k : E) ≠ p := fun h => hk (Subtype.ext h)
      have hkt := (Finset.ext_iff.mp hpt (k : E)).mpr k.property
      exact (Finset.mem_insert.mp hkt).resolve_left hkp
    · intro hy
      refine ⟨⟨y, hst hy⟩, ?_, rfl⟩
      intro h
      have he : y = p := congrArg Subtype.val h
      exact hps (he ▸ (show y ∈ s from hy))
  have hrange : range b = (t : Set E) :=
    (K.indep ht).range_affineBasisOfCard htcard
  have hreplace : range (Function.update b i q) = (u : Set E) := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      by_cases hki : k = i
      · subst k
        rw [Function.update_self, ← hqu]
        exact Finset.mem_insert_self q s
      · rw [Function.update_of_ne hki]
        have hks : b k ∈ (s : Set E) := by
          rw [← hfimage]
          exact mem_image_of_mem b hki
        exact hsu hks
    · intro hy
      rw [← hqu] at hy
      rcases Finset.mem_insert.mp hy with he | hys
      · exact ⟨i, by simpa only [Function.update_self] using he.symm⟩
      · change y ∈ (s : Set E) at hys
        rw [← hfimage] at hys
        obtain ⟨k, hk, rfl⟩ := hys
        exact ⟨k, Function.update_of_ne hk q b⟩
  have hspanU : affineSpan ℝ (u : Set E) = ⊤ := by
    simpa using ((K.indep hu).affineBasisOfCard hucard).tot
  have hfull : affineSpan ℝ (range (Function.update b i q)) = ⊤ := by
    rw [hreplace]
    exact hspanU
  have hinterFaces : t ∩ u = s := by
    ext y
    simp only [← hpt, ← hqu, Finset.mem_inter, Finset.mem_insert]
    aesop
  obtain ⟨x, hxs⟩ := Set.Nonempty.intrinsicInterior
    (convex_convexHull ℝ (s : Set E)) (Finset.coe_nonempty.mpr ⟨r, hrs⟩).convexHull
  have hximage : x ∈ intrinsicInterior ℝ (convexHull ℝ (b '' {k : t | k ≠ i})) := by
    rwa [hfimage]
  have hxi : b.coord i x = 0 := b.coord_eq_zero_of_mem_affineSpan_image
    (s := {k : t | k ≠ i}) (by simp)
    (convexHull_subset_affineSpan _ (intrinsicInterior_subset hximage))
  have hxpos : ∀ k, k ≠ i → 0 < b.coord k x := fun k hk =>
    b.coord_pos_of_mem_intrinsicInterior_convexHull_image hximage hk
  have hcommon (y : E) (hy : y ∈ convexHull ℝ (t : Set E) ∩
      convexHull ℝ (u : Set E)) : b.coord i y = 0 := by
    have hys := K.inter_subset_convexHull ht hu hy
    rw [← Finset.coe_inter, hinterFaces, ← hfimage] at hys
    exact b.coord_eq_zero_of_mem_affineSpan_image (s := {k : t | k ≠ i}) (by simp)
      (convexHull_subset_affineSpan _ hys)
  have hqneg : b.coord i q < 0 :=
    b.coord_neg_of_common_facet_intersection i q x
      (b.coord_ne_zero_of_affineSpan_update_eq_top i q hfull) hxi hxpos
      (fun y hy => hcommon y (by simpa only [hrange, hreplace] using hy))
  have hagree (k : t) (hk : k ≠ i) : B (b k) = A (b k) := by
    have hks : b k ∈ (s : Set E) := by rw [← hfimage]; exact mem_image_of_mem b hk
    exact (hB (subset_convexHull ℝ _ (hsu hks))).trans
      (hA (subset_convexHull ℝ _ (hst hks))).symm
  let C : E ≃ᵃ[ℝ] E := B.trans A.symm
  have hCfix (k : t) (hk : k ≠ i) : C (b k) = b k := by
    change A.symm (B (b k)) = b k
    rw [hagree k hk, A.symm_apply_apply]
  have himageRange : range (Function.update b i (C q)) = C '' (u : Set E) := by
    rw [← hreplace, ← range_comp]
    congr 1
    funext k
    by_cases hki : k = i
    · subst k
      simp only [Function.update_self, Function.comp_apply]
    · simp only [Function.update_of_ne hki, Function.comp_apply, hCfix k hki]
  have hfullImage : affineSpan ℝ (range (Function.update b i (C q))) = ⊤ := by
    rw [himageRange]
    exact C.toAffineMap.span_eq_top_of_surjective C.surjective hspanU
  have hcommonImage (y : E) (hy : y ∈ convexHull ℝ (range b) ∩
      convexHull ℝ (range (Function.update b i (C q)))) : b.coord i y = 0 := by
    rw [hrange, himageRange] at hy
    change y ∈ convexHull ℝ (t : Set E) ∩
      convexHull ℝ (C.toAffineMap '' (u : Set E)) at hy
    rw [← C.toAffineMap.image_convexHull] at hy
    obtain ⟨z, hz, hzy⟩ := hy.2
    have hAyBz : A y = B z := by
      rw [← hzy]
      change A (A.symm (B z)) = B z
      exact A.apply_symm_apply _
    have hfyz : f y = f z := (hA hy.1).symm.trans (hAyBz.trans (hB hz))
    have hyz : y = z := hf (K.convexHull_subset_space ht hy.1)
      (K.convexHull_subset_space hu hz) hfyz
    exact hcommon y ⟨hy.1, hyz.symm ▸ hz⟩
  have hqImage : b.coord i (A.symm (B q)) < 0 :=
    b.coord_neg_of_common_facet_intersection i (C q) x
      (b.coord_ne_zero_of_affineSpan_update_eq_top i (C q) hfullImage)
      hxi hxpos hcommonImage
  exact same_det_sign_of_opposite_facet_coordinates b i j hij A B hagree q hqneg hqImage

end PoincareConjecture.M76.HamiltonIndexOne
