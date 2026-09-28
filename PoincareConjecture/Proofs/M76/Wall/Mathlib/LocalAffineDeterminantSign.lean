import PoincareConjecture.Proofs.M76.Wall.Mathlib.ConvexFullFacetConnectivity
import PoincareConjecture.Proofs.M76.Wall.Mathlib.PairedFacetOrientation










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {K : SimplicialComplex ℝ E} {f : E → E}

private theorem det_ne_zero_of_full_face
    (hi : InjOn f K.space) {t : Finset E} (ht : t ∈ K.faces)
    (htc : t.card = Module.finrank ℝ E + 1) (A : E →ᴬ[ℝ] E)
    (hA : EqOn f A (convexHull ℝ (t : Set E))) :
    LinearMap.det A.toAffineMap.linear ≠ 0 := by
  let b := (K.indep ht).affineBasisOfCard htc
  have hspan : affineSpan ℝ (t : Set E) = ⊤ := by
    simpa [b] using b.tot
  have hAinj : Function.Injective A := by
    have hhull : InjOn A (convexHull ℝ (t : Set E)) := by
      intro x hx y hy hxy
      exact hi (K.convexHull_subset_space ht hx) (K.convexHull_subset_space ht hy)
        ((hA hx).trans (hxy.trans (hA hy).symm))
    have hall := A.toAffineMap.injOn_affineSpan_of_injOn_convex
      (convex_convexHull ℝ (t : Set E))
      (Finset.coe_nonempty.mpr (K.nonempty_of_mem_faces ht)).convexHull hhull
    rw [affineSpan_convexHull, hspan] at hall
    exact fun x y hxy => hall (by simp) (by simp) hxy
  have hlinear : Function.Injective A.toAffineMap.linear :=
    A.toAffineMap.linear_injective_iff.mpr hAinj
  intro hzero
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero) (LinearMap.ker_eq_bot.mpr hlinear)

private theorem eq_of_eqOn_full_face
    {t : Finset E} (ht : t ∈ K.faces)
    (htc : t.card = Module.finrank ℝ E + 1) (A B : E →ᴬ[ℝ] E)
    (hA : EqOn f A (convexHull ℝ (t : Set E)))
    (hB : EqOn f B (convexHull ℝ (t : Set E))) : A = B := by
  let b := (K.indep ht).affineBasisOfCard htc
  have hspan : affineSpan ℝ (t : Set E) = ⊤ := by
    simpa [b] using b.tot
  apply ContinuousAffineMap.toAffineMap_injective
  apply AffineMap.ext_on hspan
  intro x hx
  exact (hA (subset_convexHull ℝ _ hx)).symm.trans (hB (subset_convexHull ℝ _ hx))





theorem AffineOnFaces.det_mul_pos_on_convex_open
    (hf : K.AffineOnFaces f) (hi : InjOn f K.space) (hK : K.faces.Finite)
    {U : Set E} (hU : IsOpen U) (hcv : Convex ℝ U) (hne : U.Nonempty)
    (hUK : U ⊆ K.space) (t u : K.FullFaceIn U) (A B : E →ᴬ[ℝ] E)
    (hA : EqOn f A (convexHull ℝ (t.val : Set E)))
    (hB : EqOn f B (convexHull ℝ (u.val : Set E))) :
    LinearMap.det A.toAffineMap.linear ≠ 0 ∧
      LinearMap.det B.toAffineMap.linear ≠ 0 ∧
      0 < LinearMap.det A.toAffineMap.linear * LinearMap.det B.toAffineMap.linear := by
  classical
  choose C hC using fun v : K.FullFaceIn U => hf v.val v.property.1
  have hn (v : K.FullFaceIn U) : LinearMap.det (C v).toAffineMap.linear ≠ 0 :=
    det_ne_zero_of_full_face hi v.property.1 v.property.2.1 (C v) (hC v)
  have hadj {v w : K.FullFaceIn U} (hvw : (K.fullFacetGraph U).Adj v w) :
      (0 < LinearMap.det (C v).toAffineMap.linear ↔
        0 < LinearMap.det (C w).toAffineMap.linear) := by
    obtain ⟨hvwne, s, hs, hsc, hsv, hsw, _⟩ := hvw
    have hneval : v.val ≠ w.val := fun he => hvwne (Subtype.ext he)
    have hp := (hf.det_mul_pos_of_paired_facet hi hs v.property.1 w.property.1
      hsc v.property.2.1 w.property.2.1 hsv hsw hneval (C v) (C w) (hC v) (hC w)).2.2
    rcases mul_pos_iff.mp hp with ⟨hv, hw⟩ | ⟨hv, hw⟩
    · exact iff_of_true hv hw
    · exact iff_of_false (not_lt_of_ge hv.le) (not_lt_of_ge hw.le)
  have hwalk {v w : K.FullFaceIn U} (p : (K.fullFacetGraph U).Walk v w) :
      (0 < LinearMap.det (C v).toAffineMap.linear ↔
        0 < LinearMap.det (C w).toAffineMap.linear) := by
    induction p with
    | nil => rfl
    | cons h _ ih => exact (hadj h).trans ih
  obtain ⟨p⟩ := (K.fullFacetGraph_connected hK hU hcv hne hUK).preconnected t u
  have heqA := eq_of_eqOn_full_face t.property.1 t.property.2.1 A (C t) hA (hC t)
  have heqB := eq_of_eqOn_full_face u.property.1 u.property.2.1 B (C u) hB (hC u)
  rw [heqA, heqB]
  refine ⟨hn t, hn u, ?_⟩
  by_cases htpos : 0 < LinearMap.det (C t).toAffineMap.linear
  · exact mul_pos htpos ((hwalk p).mp htpos)
  · have hunot : ¬0 < LinearMap.det (C u).toAffineMap.linear :=
      fun hu => htpos ((hwalk p).mpr hu)
    exact mul_pos_of_neg_of_neg ((lt_or_gt_of_ne (hn t)).resolve_right htpos)
      ((lt_or_gt_of_ne (hn u)).resolve_right hunot)

end Geometry.SimplicialComplex
