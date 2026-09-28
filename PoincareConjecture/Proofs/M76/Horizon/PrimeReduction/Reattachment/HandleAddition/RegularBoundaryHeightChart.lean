import PoincareConjecture.Proofs.M76.Mathlib.FiniteAffineHeightShear
import PoincareConjecture.Proofs.M76.Mathlib.FiniteFaceStarNeighborhood
import PoincareConjecture.Proofs.M76.Mathlib.LocallyFinitePolyhedralPatches
import PoincareConjecture.Proofs.M76.Mathlib.AffineLevelSubcomplex
import PoincareConjecture.Proofs.M76.Mathlib.ConnectedComplexGraph










set_option autoImplicit false

open Set Geometry Metric

namespace Geometry.SimplicialComplex







theorem exists_nonvertex_height_chart_preserving_affine_map
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → ℝ} (hf : K.AffineOnFaces f) {x : E}
    (hx : x ∈ interior K.space) (hreg : ∀ v ∈ K.vertices, f v ≠ f x)
    (B : SimplicialComplex ℝ E) (hBK : B ≤ K) (hxB : x ∈ B.space)
    (psi : E →ᴬ[ℝ] F) (hpsi : ∀ y ∈ B.space, psi y = psi x) :
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
    push Not at h
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
    push Not at h
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


private theorem exists_affine_height_frame_preserving_first
    (ell : ((ℝ × ℝ) × ℝ) →ᴬ[ℝ] ℝ) (w : (ℝ × ℝ) × ℝ)
    (hw : ell.contLinear w = 1) (hwfirst : w.1 = 0) (t : ℝ) :
    ∃ F : ((ℝ × ℝ) × ℝ) ≃ᴬ[ℝ] ((ℝ × ℝ) × ℝ),
      ∀ z,F z = (z.1,ell z-t) := by
  let L := (LinearMap.fst ℝ (ℝ × ℝ) ℝ).prod ell.toAffineMap.linear
  have hsurj : Function.Surjective L := by
    rintro ⟨q,r⟩
    refine ⟨(q,0) + (r-ell.contLinear (q,0)) • w,?_⟩
    apply Prod.ext
    · change q + (r-ell.contLinear (q,0)) • w.1 = q
      rw [hwfirst,smul_zero,add_zero]
    · change ell.contLinear ((q,0) + (r-ell.contLinear (q,0)) • w) = r
      rw [map_add,map_smul,hw]
      change ell.contLinear (q,0) + (r-ell.contLinear (q,0))*1 = r
      ring
  let B := (LinearEquiv.ofBijective L
    ⟨LinearMap.injective_iff_surjective.mpr hsurj,hsurj⟩).toContinuousLinearEquiv.toContinuousAffineEquiv
  let F := B.trans (ContinuousAffineEquiv.constVAdd ℝ ((ℝ × ℝ) × ℝ) ((0,0),ell 0-t))
  refine ⟨F,?_⟩
  intro z
  apply Prod.ext
  · change (0 : ℝ × ℝ) + z.1 = z.1
    exact zero_add _
  · change ell 0-t + ell.contLinear z = ell z-t
    have h := ell.contLinear_map_vsub z 0
    simp only [vsub_eq_sub,sub_zero] at h
    rw [h]
    ring




theorem exists_nonvertex_height_chart_preserving_two_planes
    (K : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (hK : K.faces.Finite)
    {f : ((ℝ × ℝ) × ℝ) → ℝ} (hf : K.AffineOnFaces f) {x : (ℝ × ℝ) × ℝ}
    (hx : x ∈ interior K.space) (hreg : ∀ v ∈ K.vertices,f v ≠ f x)
    (B : SimplicialComplex ℝ ((ℝ × ℝ) × ℝ)) (hBK : B ≤ K) (hxB : x ∈ B.space)
    (hzero : ∀ z ∈ B.space,z.1 = 0) :
    ∃ H : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) ((ℝ × ℝ) × ℝ),
      x ∈ H.source ∧ H x = 0 ∧ H.source ⊆ interior K.space ∧
      H ∈ piecewiseAffineGroupoid ((ℝ × ℝ) × ℝ) ∧
      (∀ z ∈ H.source,(H z).1 = z.1) ∧
      ∀ z ∈ H.source,(H z).2 = f z-f x := by
  let psi := (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).toContinuousAffineMap
  obtain ⟨ell,w,T,hellw,hpsiw,hxT,hTx,hTs,_,hT,hheight,hpsi,_⟩ :=
    K.exists_nonvertex_height_chart_preserving_affine_map hK hf hx hreg B hBK hxB psi
      (fun z hz => (hzero z hz).trans (hzero x hxB).symm)
  obtain ⟨F,hF⟩ := exists_affine_height_frame_preserving_first ell w hellw hpsiw (f x)
  let H := T.trans F.toHomeomorph.toOpenPartialHomeomorph
  have hHs : H.source = T.source := by
    change T.source ∩ T ⁻¹' univ = T.source
    simp
  have hvalue (z) : H z = ((T z).1,ell (T z)-f x) := hF (T z)
  refine ⟨H,hHs.symm.subset hxT,?_,hHs.subset.trans hTs,?_,?_,?_⟩
  · rw [hvalue,hTx,hzero x hxB]
    have he := hheight x hxT
    rw [hTx] at he
    simp [he]
  · exact (piecewiseAffineGroupoid _).trans hT
      ⟨locallyPiecewiseAffineOn_affine F.toContinuousAffineMap isOpen_univ,
        locallyPiecewiseAffineOn_affine F.symm.toContinuousAffineMap isOpen_univ⟩
  · intro z _
    rw [hvalue]
    exact hpsi z
  · intro z hz
    rw [hvalue,hheight z (hHs.subset hz)]



theorem exists_regular_height_charts_preserving_two_planes
    {f : ((ℝ × ℝ) × ℝ) → ℝ} {U : Set ((ℝ × ℝ) × ℝ)}
    (hf : LocallyPiecewiseAffineOn f U) {x : (ℝ × ℝ) × ℝ} (hx : x ∈ U) :
    ∃ (V : Set ((ℝ × ℝ) × ℝ)) (W : Set ℝ),
      IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ W.Finite ∧
      ∀ y ∈ V, y.1 = 0 → f y ∉ W →
        ∃ H : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) ((ℝ × ℝ) × ℝ),
          y ∈ H.source ∧ H y = 0 ∧ H.source ⊆ V ∧
          H ∈ piecewiseAffineGroupoid ((ℝ × ℝ) × ℝ) ∧
          (∀ z ∈ H.source,(H z).1 = z.1) ∧
          ∀ z ∈ H.source,(H z).2 = f z-f y := by
  classical
  let a := ((LinearMap.fst ℝ ℝ ℝ).comp
    (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).toAffineMap
  let b := ((LinearMap.snd ℝ ℝ ℝ).comp
    (LinearMap.fst ℝ (ℝ × ℝ) ℝ)).toAffineMap
  obtain ⟨K,hK,hxK,hKU,hfK⟩ := hf x hx
  let N := hK.toFinset.sup Finset.card
  have hN (s) (hs : s ∈ K.faces) : s.card ≤ N+1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ N)
  obtain ⟨L,hL,hLK,_,halign⟩ :=
    K.exists_subdivision_respectsAffineHyperplanes hK hN {a,b}
  have ha : L.RespectsAffineHyperplane a := halign a (by simp)
  have hb : L.RespectsAffineHyperplane b := halign b (by simp)
  let A := L.affineZeroSubcomplex a
  let B := A.affineZeroSubcomplex b
  have hAL : A ≤ L := fun _ hs => hs.1
  have hBA : B ≤ A := fun _ hs => hs.1
  have hAs : A.space = L.space ∩ {z | a z = 0} := L.affineZeroSubcomplex_space a ha
  have hBs : B.space = A.space ∩ {z | b z = 0} :=
    A.affineZeroSubcomplex_space b (fun s hs => hb s (hAL hs))
  refine ⟨interior L.space,f '' L.vertices,isOpen_interior,?_,?_,
    (L.finite_vertices_of_finite_faces hL).image f,?_⟩
  · rwa [hLK.space_eq]
  · rw [hLK.space_eq]
    exact interior_subset.trans hKU
  · intro y hy hyzero hyW
    have hyB : y ∈ B.space := by
      rw [hBs,hAs]
      exact ⟨⟨interior_subset hy,congrArg Prod.fst hyzero⟩,congrArg Prod.snd hyzero⟩
    have hBzero (z) (hz : z ∈ B.space) : z.1 = 0 := by
      rw [hBs,hAs] at hz
      exact Prod.ext hz.1.2 hz.2
    exact L.exists_nonvertex_height_chart_preserving_two_planes hL
      (hLK.affineOnFaces hfK) hy (fun v hv h => hyW ⟨v,hv,h⟩)
      B (fun s hs => hAL (hBA hs)) hyB hBzero

end Geometry.SimplicialComplex

