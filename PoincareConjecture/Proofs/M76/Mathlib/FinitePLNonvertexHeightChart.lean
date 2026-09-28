import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHeightShear
import PoincareConjecture.Proofs.M76.Mathlib.FiniteFaceStarNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.LocallyFinitePolyhedralPatches












set_option autoImplicit false

open Set Geometry Metric

namespace Geometry.SimplicialComplex







theorem exists_nonvertex_height_chart_preserving_affine
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → ℝ} (hf : K.AffineOnFaces f) {x : E}
    (hx : x ∈ interior K.space) (hreg : ∀ v ∈ K.vertices, f v ≠ f x)
    (B : SimplicialComplex ℝ E) (hBK : B ≤ K) (hxB : x ∈ B.space)
    (psi : E →ᴬ[ℝ] ℝ) (hpsi : ∀ y ∈ B.space, psi y = psi x) :
    ∃ (ell : E →ᴬ[ℝ] ℝ) (w : E) (H : OpenPartialHomeomorph E E),
      ell.contLinear w = 1 ∧ psi.contLinear w = 0 ∧ x ∈ H.source ∧ H x = x ∧
      H.source ⊆ interior K.space ∧ H.target ⊆ interior K.space ∧
      H ∈ piecewiseAffineGroupoid E ∧
      (∀ y ∈ H.source, ell (H y) = f y) ∧
      (∀ y, psi (H y) = psi y) ∧ ∀ y, psi (H.symm y) = psi y := by
  classical
  obtain ⟨s, hsK, hxs, hsmin, V, hV, hxV, hVstar⟩ :=
    K.exists_minimal_faceStar_neighborhood_of_finite hK ⟨x, interior_subset hx⟩
  obtain ⟨sB, hsB, hxsB⟩ := mem_space_iff.mp hxB
  have hsBsub : s ⊆ sB := hsmin sB (hBK hsB) hxsB
  have hspsi (y : E) (hy : y ∈ s) : psi y = psi x :=
    hpsi y (B.convexHull_subset_space hsB (subset_convexHull ℝ _ (hsBsub hy)))
  obtain ⟨O, hO, hOV⟩ := isOpen_induced_iff.mp hV
  have hxO : x ∈ O := by
    have hx' := hxV
    rw [← hOV] at hx'
    exact hx'
  have hOstar : interior K.space ∩ O ⊆ (K.closedFaceStar s).space := by
    intro y hy
    apply hVstar
    refine ⟨⟨y, interior_subset hy.1⟩, ?_, rfl⟩
    rw [← hOV]
    exact hy.2
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (isOpen_interior.inter hO) x ⟨hx, hxO⟩
  obtain ⟨ell, hell⟩ := hf s hsK
  have hsreg (v : E) (hv : v ∈ s) : f v ≠ f x :=
    hreg v (K.down_closed hsK (Finset.singleton_subset_iff.mpr hv)
      (Finset.singleton_nonempty v))
  have hlow : ∃ v ∈ s, f v < f x := by
    by_contra h
    push_neg at h
    have hgen : (s : Set E) ⊆ ell ⁻¹' Ioi (f x) := by
      intro v hv
      change f x < ell v
      rw [← hell (subset_convexHull ℝ _ hv)]
      exact lt_of_le_of_ne (h v hv) (hsreg v hv).symm
    have hbad : f x < ell x := convexHull_min hgen
      ((convex_Ioi (f x)).affine_preimage ell.toAffineMap) hxs
    rw [← hell hxs] at hbad
    exact (lt_irrefl (f x)) hbad
  have hhigh : ∃ u ∈ s, f x < f u := by
    by_contra h
    push_neg at h
    have hgen : (s : Set E) ⊆ ell ⁻¹' Iio (f x) := by
      intro u hu
      change ell u < f x
      rw [← hell (subset_convexHull ℝ _ hu)]
      exact lt_of_le_of_ne (h u hu) (hsreg u hu)
    have hbad : ell x < f x := convexHull_min hgen
      ((convex_Iio (f x)).affine_preimage ell.toAffineMap) hxs
    rw [← hell hxs] at hbad
    exact (lt_irrefl (f x)) hbad
  obtain ⟨v, hvs, hv⟩ := hlow
  obtain ⟨u, hus, hu⟩ := hhigh
  have hgap : f u - f v ≠ 0 := sub_ne_zero.mpr (ne_of_gt (hv.trans hu))
  let w : E := (f u - f v)⁻¹ • (u - v)
  have hpsiw : psi.contLinear w = 0 := by
    have hlin : psi.contLinear (u - v) = psi u - psi v := by
      simpa only [vsub_eq_sub] using psi.contLinear_map_vsub u v
    dsimp only [w]
    rw [map_smul, hlin, hspsi u hus, hspsi v hvs, sub_self, smul_zero]
  have hslope (a : E →ᴬ[ℝ] ℝ) (hau : a u = f u) (hav : a v = f v) :
      a.contLinear w = 1 := by
    have hlin : a.contLinear (u - v) = a u - a v := by
      simpa only [vsub_eq_sub] using a.contLinear_map_vsub u v
    dsimp only [w]
    rw [map_smul, hlin, hau, hav]
    change (f u - f v)⁻¹ * (f u - f v) = 1
    exact inv_mul_cancel₀ hgap
  let I := {t : Finset E | t ∈ K.faces ∧ s ⊆ t}
  have hI : {t : Finset E | t ∈ K.faces ∧ s ⊆ t}.Finite := hK.subset fun _ ht => ht.1
  let : Fintype I := hI.fintype
  choose A hA using fun t : I => hf t.val t.property.1
  have hcommon (t : I) : (A t).contLinear w = 1 := hslope (A t)
    (hA t (subset_convexHull ℝ _ (t.property.2 hus))).symm
    (hA t (subset_convexHull ℝ _ (t.property.2 hvs))).symm
  have hselect : ∀ y ∈ ball x r, ∃ t : I, f y = A t y := by
    intro y hy
    obtain ⟨t, ht, hyt⟩ := mem_space_iff.mp (hOstar (hball hy))
    let T : I := ⟨s ∪ t, ht.2, Finset.subset_union_left⟩
    exact ⟨T, hA T (convexHull_mono
      (show (t : Set E) ⊆ (s ∪ t : Finset E) from Finset.subset_union_right) hyt)⟩
  have hPL : LocallyPiecewiseAffineOn f (ball x r) := by
    let : Fintype K.faces := hK.fintype
    have hlocal := hf.locallyPiecewiseAffineOn_of_locallyFinite
      (locallyFinite_of_finite (fun t : K.faces => convexHull ℝ (t.val : Set E)))
    exact hlocal.mono isOpen_ball (hball.trans inter_subset_left)
  have hellw : ell.contLinear w = 1 := hslope ell
    (hell (subset_convexHull ℝ _ hus)).symm
    (hell (subset_convexHull ℝ _ hvs)).symm
  obtain ⟨H, hxH, hHx, hHB, hHtB, hHPL, hHform, hHinv, hheight⟩ :=
    OpenPartialHomeomorph.exists_finite_affine_height_shear hPL (convex_ball x r)
      A w hcommon hselect ell hellw (mem_ball_self hr) (hell hxs)
  refine ⟨ell, w, H, hellw, hpsiw, hxH, hHx,
    hHB.trans (hball.trans inter_subset_left), hHtB.trans (hball.trans inter_subset_left),
    hHPL, hheight, ?_, ?_⟩
  · intro y
    rw [hHform]
    change psi ((f y - ell y) • w +ᵥ y) = psi y
    simp only [ContinuousAffineMap.map_vadd, map_smul, hpsiw, smul_zero, zero_vadd]
  · intro y
    rw [hHinv]
    change psi (-(f y - ell y) • w +ᵥ y) = psi y
    simp only [ContinuousAffineMap.map_vadd, map_smul, hpsiw, smul_zero, zero_vadd]






theorem exists_nonvertex_height_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → ℝ} (hf : K.AffineOnFaces f) {x : E}
    (hx : x ∈ interior K.space) (hreg : ∀ v ∈ K.vertices, f v ≠ f x) :
    ∃ (ell : E →ᴬ[ℝ] ℝ) (w : E) (H : OpenPartialHomeomorph E E),
      ell.contLinear w = 1 ∧ x ∈ H.source ∧ H x = x ∧
      H.source ⊆ interior K.space ∧ H.target ⊆ interior K.space ∧
      H ∈ piecewiseAffineGroupoid E ∧
      ∀ y ∈ H.source, ell (H y) = f y := by
  obtain ⟨ell, w, H, hellw, _, hxH, hHx, hHs, hHt, hHPL, hheight, _, _⟩ :=
    K.exists_nonvertex_height_chart_preserving_affine hK hf hx hreg K le_rfl
      (interior_subset hx) 0 (fun _ _ => rfl)
  exact ⟨ell, w, H, hellw, hxH, hHx, hHs, hHt, hHPL, hheight⟩

end Geometry.SimplicialComplex
