import PoincareConjecture.Proofs.M76.Wall.Mathlib.LocalAffineDeterminantSign
import PoincareConjecture.Proofs.M76.Wall.Mathlib.PLTransitionFacetOrientation
import PoincareConjecture.Proofs.M76.Mathlib.FiniteCarrierFaceInteriors











set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

private theorem exists_common_full_interiors
    (K L : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hL : L.faces.Finite)
    {U : Set E} (hU : IsOpen U) (hne : U.Nonempty)
    (hUK : U ⊆ K.space) (hUL : U ⊆ L.space) :
    ∃ (t : K.FullFaceIn U) (u : L.FullFaceIn U),
      (U ∩ (interior (convexHull ℝ (t.val : Set E)) ∩
        interior (convexHull ℝ (u.val : Set E)))).Nonempty := by
  classical
  let S : Set (Finset E) :=
    {s | (s ∈ K.faces ∨ s ∈ L.faces) ∧ affineSpan ℝ (s : Set E) ≠ ⊤}
  have hS : S.Finite := (hK.union hL).subset (fun _ hs => hs.1)
  let : Finite S := hS.to_subtype
  let A : S → AffineSubspace ℝ E := fun s => affineSpan ℝ (s.val : Set E)
  obtain ⟨y, hyU, hyA⟩ :=
    (AffineSubspace.dense_compl_iUnion A (fun s => s.property.2)).inter_open_nonempty U hU hne
  obtain ⟨t, ht, hyt⟩ := K.exists_face_intrinsicInterior_of_finite hK (hUK hyU)
  obtain ⟨u, hu, hyu⟩ := L.exists_face_intrinsicInterior_of_finite hL (hUL hyU)
  have htspan : affineSpan ℝ (t : Set E) = ⊤ := by
    by_contra hn
    exact hyA (mem_iUnion.mpr
      ⟨⟨t, Or.inl ht, hn⟩, convexHull_subset_affineSpan _ (intrinsicInterior_subset hyt)⟩)
  have huspan : affineSpan ℝ (u : Set E) = ⊤ := by
    by_contra hn
    exact hyA (mem_iUnion.mpr
      ⟨⟨u, Or.inr hu, hn⟩, convexHull_subset_affineSpan _ (intrinsicInterior_subset hyu)⟩)
  have htc : t.card = Module.finrank ℝ E + 1 := by
    have hs : affineSpan ℝ (range ((↑) : t → E)) = ⊤ := by
      have hrange : range ((↑) : t → E) = (t : Set E) := by ext x; simp
      rw [hrange]
      exact htspan
    simpa using (K.indep ht).affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hs
  have huc : u.card = Module.finrank ℝ E + 1 := by
    have hs : affineSpan ℝ (range ((↑) : u → E)) = ⊤ := by
      have hrange : range ((↑) : u → E) = (u : Set E) := by ext x; simp
      rw [hrange]
      exact huspan
    simpa using (L.indep hu).affineSpan_eq_top_iff_card_eq_finrank_add_one.mp hs
  have hytint : y ∈ interior (convexHull ℝ (t : Set E)) := by
    let b := (K.indep ht).affineBasisOfCard htc
    have h : y ∈ interior (convexHull ℝ (range b)) :=
      b.mem_interior_convexHull_of_mem_intrinsicInterior (by simpa [b] using hyt)
    simpa [b] using h
  have hyuint : y ∈ interior (convexHull ℝ (u : Set E)) := by
    let b := (L.indep hu).affineBasisOfCard huc
    have h : y ∈ interior (convexHull ℝ (range b)) :=
      b.mem_interior_convexHull_of_mem_intrinsicInterior (by simpa [b] using hyu)
    simpa [b] using h
  exact ⟨⟨t, ht, htc, y, intrinsicInterior_subset hyt, hyU⟩,
    ⟨u, hu, huc, y, intrinsicInterior_subset hyu, hyU⟩, y, hyU, hytint, hyuint⟩





theorem AffineOnFaces.det_mul_pos_of_eqOn_convex_open
    {K L : SimplicialComplex ℝ E} {f g : E → E}
    (hf : K.AffineOnFaces f) (hg : L.AffineOnFaces g)
    (hi : InjOn f K.space) (hj : InjOn g L.space)
    (hK : K.faces.Finite) (hL : L.faces.Finite)
    {U : Set E} (hU : IsOpen U) (hcv : Convex ℝ U) (hne : U.Nonempty)
    (hUK : U ⊆ K.space) (hUL : U ⊆ L.space) (hfg : EqOn f g U)
    (t : K.FullFaceIn U) (u : L.FullFaceIn U) (A B : E →ᴬ[ℝ] E)
    (hA : EqOn f A (convexHull ℝ (t.val : Set E)))
    (hB : EqOn g B (convexHull ℝ (u.val : Set E))) :
    LinearMap.det A.toAffineMap.linear ≠ 0 ∧
      LinearMap.det B.toAffineMap.linear ≠ 0 ∧
      0 < LinearMap.det A.toAffineMap.linear * LinearMap.det B.toAffineMap.linear := by
  obtain ⟨v, w, hmeet⟩ := exists_common_full_interiors K L hK hL hU hne hUK hUL
  obtain ⟨C, hC⟩ := hf v.val v.property.1
  obtain ⟨D, hD⟩ := hg w.val w.property.1
  have hCD : C = D := by
    apply ContinuousAffineMap.toAffineMap_injective
    apply AffineMap.ext_on ((hU.inter (isOpen_interior.inter isOpen_interior)).affineSpan_eq_top
      hmeet)
    intro x hx
    exact (hC (interior_subset hx.2.1)).symm.trans
      ((hfg hx.1).trans (hD (interior_subset hx.2.2)))
  subst D
  have hAC := hf.det_mul_pos_on_convex_open hi hK hU hcv hne hUK t v A C hA hC
  have hCB := hg.det_mul_pos_on_convex_open hj hL hU hcv hne hUL w u C B hD hB
  refine ⟨hAC.1, hCB.2.1, ?_⟩
  rcases mul_pos_iff.mp hAC.2.2 with ⟨ha, hc⟩ | ⟨ha, hc⟩
  · rcases mul_pos_iff.mp hCB.2.2 with ⟨_, hb⟩ | ⟨hc', _⟩
    · exact mul_pos ha hb
    · exact (lt_asymm hc hc').elim
  · rcases mul_pos_iff.mp hCB.2.2 with ⟨hc', _⟩ | ⟨_, hb⟩
    · exact (lt_asymm hc hc').elim
    · exact mul_pos_of_neg_of_neg ha hb

end Geometry.SimplicialComplex

namespace Geometry





theorem exists_finite_convex_sign_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (h : OpenPartialHomeomorph E E) (hh : h ∈ piecewiseAffineGroupoid E)
    {x : E} (hx : x ∈ h.source) :
    ∃ K : SimplicialComplex ℝ E,
      K.faces.Finite ∧ x ∈ interior K.space ∧ K.space ⊆ h.source ∧
      K.AffineOnFaces h ∧ InjOn h K.space ∧
      ∃ r : ℝ, 0 < r ∧ ball x r ⊆ K.space ∧
        ∀ (t u : K.FullFaceIn (ball x r)) (A B : E →ᴬ[ℝ] E),
          EqOn h A (convexHull ℝ (t.val : Set E)) →
          EqOn h B (convexHull ℝ (u.val : Set E)) →
          LinearMap.det A.toAffineMap.linear ≠ 0 ∧
            LinearMap.det B.toAffineMap.linear ≠ 0 ∧
            0 < LinearMap.det A.toAffineMap.linear * LinearMap.det B.toAffineMap.linear := by
  obtain ⟨K, hK, hxK, hsource, hf, hi, _⟩ :=
    exists_finite_paired_facet_orientation h hh hx
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxK)
  refine ⟨K, hK, hxK, hsource, hf, hi, r, hr, hball, ?_⟩
  intro t u A B hA hB
  exact hf.det_mul_pos_on_convex_open hi hK isOpen_ball (convex_ball x r)
    ⟨x, mem_ball_self hr⟩ hball t u A B hA hB

end Geometry
