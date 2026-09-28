import PoincareConjecture.Proofs.M76.Wall.Mathlib.AffineFacetDeterminant
import PoincareConjecture.Proofs.M76.Mathlib.PairedFacetChartSigns
import PoincareConjecture.Proofs.M76.Mathlib.FullSimplexBasis
import PoincareConjecture.Proofs.M76.Mathlib.ConvexAffineInjectivity
import Mathlib.Analysis.Normed.Module.FiniteDimension










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {K : SimplicialComplex ℝ E} {f : E → E}




theorem AffineOnFaces.det_mul_pos_of_paired_facet
    (hf : K.AffineOnFaces f) (hi : InjOn f K.space)
    {s t u : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hsc : s.card = Module.finrank ℝ E)
    (htc : t.card = Module.finrank ℝ E + 1)
    (huc : u.card = Module.finrank ℝ E + 1)
    (hst : s ⊆ t) (hsu : s ⊆ u) (htu : t ≠ u)
    (A B : E →ᴬ[ℝ] E)
    (hA : EqOn f A (convexHull ℝ (t : Set E)))
    (hB : EqOn f B (convexHull ℝ (u : Set E))) :
    LinearMap.det A.toAffineMap.linear ≠ 0 ∧
      LinearMap.det B.toAffineMap.linear ≠ 0 ∧
      0 < LinearMap.det A.toAffineMap.linear * LinearMap.det B.toAffineMap.linear := by
  classical
  obtain ⟨p, hpS, hpt⟩ := Finset.exists_eq_insert_iff.mpr ⟨hst, by omega⟩
  have hpT : p ∈ t := by rw [← hpt]; exact Finset.mem_insert_self p s
  obtain ⟨q, hqS⟩ := K.nonempty_of_mem_faces hs
  let b : AffineBasis t ℝ E := (K.indep ht).affineBasisOfCard htc
  let i : t := ⟨p, hpT⟩
  let j : t := ⟨q, hst hqS⟩
  have hij : i ≠ j := by
    intro h
    have hpq : p = q := congrArg Subtype.val h
    exact hpS (hpq.symm ▸ hqS)
  let ell := b.coord i
  have hzero (x : E) (hx : x ∈ s) : ell x = 0 := by
    change b.coord i (b ⟨x, hst hx⟩) = 0
    apply b.coord_apply_ne
    intro h
    have hpx : p = x := congrArg Subtype.val h
    exact hpS (hpx.symm ▸ hx)
  have hell : ell.linear ≠ 0 := by
    intro h
    have hv := ell.linearMap_vsub (b i) (b j)
    rw [h, LinearMap.zero_apply] at hv
    have hi1 : ell (b i) = 1 := b.coord_apply_eq i
    have hj0 : ell (b j) = 0 := b.coord_apply_ne hij
    rw [hi1, hj0] at hv
    norm_num at hv
  have hspan : affineSpan ℝ (t : Set E) = ⊤ := by
    have hrange : Set.range b = (t : Set E) := Subtype.range_coe
    simpa only [hrange] using b.tot
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
  have hdetA : LinearMap.det A.toAffineMap.linear ≠ 0 := by
    intro h
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h) (LinearMap.ker_eq_bot.mpr hlinear)
  have hAsurj : Function.Surjective A :=
    A.toAffineMap.linear_surjective_iff.mp (LinearMap.surjective_of_injective hlinear)
  let e : E ≃ᵃ[ℝ] E := AffineEquiv.ofBijective (φ := A.toAffineMap) ⟨hAinj, hAsurj⟩
  let inverse : E →ᴬ[ℝ] E :=
    ⟨e.symm.toAffineMap, e.symm.toAffineMap.continuous_of_finiteDimensional⟩
  let g : E → E := inverse ∘ f
  let T : E →ᵃ[ℝ] E := e.symm.toAffineMap.comp B.toAffineMap
  have hg : K.AffineOnFaces g := hf.postcomp inverse
  have hginj : InjOn g K.space := fun x hx y hy hxy => hi hx hy (e.symm.injective hxy)
  have hgt {x : E} (hx : x ∈ convexHull ℝ (t : Set E)) : g x = x := by
    change e.symm (f x) = x
    rw [hA hx]
    exact e.symm_apply_apply x
  have hgu {x : E} (hx : x ∈ convexHull ℝ (u : Set E)) : g x = T x := by
    change e.symm (f x) = e.symm (B x)
    rw [hB hx]
  have hfixS (x : E) (hx : x ∈ s) : T x = x := by
    rw [← hgu (subset_convexHull ℝ _ (hsu hx))]
    exact hgt (subset_convexHull ℝ _ (hst hx))
  have hfix (k : t) (hki : k ≠ i) : T (b k) = b k := by
    have hk : k.val ∈ insert p s := hpt.symm ▸ k.property
    rcases Finset.mem_insert.mp hk with hk | hk
    · exact (hki (Subtype.ext hk)).elim
    · exact hfixS k.val hk
  let c := ell (T (b i))
  have hscaleMap : ell.comp T = c • ell := by
    apply AffineMap.ext_on b.tot
    rintro _ ⟨k, rfl⟩
    change ell (T (b k)) = c * ell (b k)
    by_cases hki : k = i
    · subst k
      rw [show ell (b i) = 1 from b.coord_apply_eq i, mul_one]
    · rw [hfix k hki, show ell (b k) = 0 from b.coord_apply_ne (Ne.symm hki), mul_zero]
  have hscale (x : E) : ell (T x) = c * ell x :=
    congrArg (fun L : E →ᵃ[ℝ] ℝ => L x) hscaleMap
  have hsource := K.opposite_centroid_signs_of_paired_facet
    hs ht hu hsc htc huc hst hsu htu ell hell hzero
  have himage := hg.opposite_centroid_signs hginj
    hs ht hu hsc htc huc hst hsu htu ell hell (by
      intro x hx
      rw [hgt (subset_convexHull ℝ _ (hst hx)), hzero x hx])
  rw [hgt (t.centroid_mem_convexHull (K.nonempty_of_mem_faces ht)),
    hgu (u.centroid_mem_convexHull (K.nonempty_of_mem_faces hu)), hscale] at himage
  have hc : 0 < c := by
    rcases hsource with ⟨htneg, hupos⟩ | ⟨htpos, huneg⟩
    · rcases himage with ⟨_, hprod⟩ | ⟨htpos, _⟩
      · exact (mul_pos_iff_of_pos_right hupos).mp hprod
      · exact (not_lt_of_ge htneg.le htpos).elim
    · rcases himage with ⟨htneg, _⟩ | ⟨_, hprod⟩
      · exact (not_lt_of_ge htneg.le htpos).elim
      · by_contra hnot
        have hnonneg := mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hnot) huneg.le
        exact (not_lt_of_ge hnonneg hprod).elim
  have hdetT : 0 < LinearMap.det T.linear := by
    rw [b.det_linear_eq_coord_of_fix_facet i j hij T hfix]
    exact hc
  have hcomp : A.toAffineMap.comp T = B.toAffineMap := by
    ext x
    change e (e.symm (B x)) = B x
    exact e.apply_symm_apply (B x)
  have hcompLinear : A.toAffineMap.linear.comp T.linear = B.toAffineMap.linear :=
    congrArg AffineMap.linear hcomp
  have hdet : LinearMap.det A.toAffineMap.linear * LinearMap.det T.linear =
      LinearMap.det B.toAffineMap.linear := by
    rw [← LinearMap.det_comp, hcompLinear]
  have hproduct : 0 < LinearMap.det A.toAffineMap.linear *
      LinearMap.det B.toAffineMap.linear := by
    rw [← hdet, ← mul_assoc]
    exact mul_pos (mul_self_pos.mpr hdetA) hdetT
  refine ⟨hdetA, ?_, hproduct⟩
  intro hdetB
  rw [hdetB, mul_zero] at hproduct
  exact (lt_irrefl 0) hproduct

end Geometry.SimplicialComplex
