import PoincareConjecture.Proofs.M76.Dehn.OriginalBranchCoordinates
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartLevelFacePosition
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineLevelPreservation
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierMarkedChartMotion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SupportedChartMotionMargin
import PoincareConjecture.Proofs.M76.Wall.CutDiskProjection

set_option autoImplicit false

open Set Geometry unitInterval

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

theorem Step.exists_boundary_surface_face_motion
    {s t : Stage e S f r C} (step : Step s t)
    (K K₀ K₁ : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (hK₀ : K₀ ≤ K₁) (hK₁ : K₁ ≤ K)
    {face : Finset V} (hfaceK : face ∈ K.faces)
    (hsource : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    {R Fmark W : Set M} (hF : Fmark = frontier R ∩ W)
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hfrontier : MapsTo j K₁.space (frontier (t.projection ⁻¹' R)))
    (Q : OpenPartialHomeomorph t.Carrier E)
    (B : OpenPartialHomeomorph s.Carrier E)
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid E)
    (hB : ∀ k, (s.charts k).symm.trans B ∈ piecewiseAffineGroupoid E)
    (htarget : Q.target = B.target)
    (hval : ∀ y, Q y = B (step.projection (step.inclusion y)))
    (hmaps : MapsTo (step.projection ∘ step.inclusion) Q.source B.source)
    (hmark : Q.source ⊆ t.projection ⁻¹' W)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hcv : Convex ℝ J.space)
    (hJQ : J.space ⊆ Q.target)
    (hface : ∀ x ∈ convexHull ℝ (face : Set V),
      j x ∈ Q.source ∧ Q (j x) ∈ interior J.space)
    (hmodel : B.source ⊆ interior (s.projection ⁻¹' R) ∨
      ∃ ell : E →ᴬ[ℝ] ℝ, ell.toAffineMap.linear ≠ 0 ∧
        (∀ y ∈ B.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ ell (B y)) ∧
        ∀ y ∈ B.source, y ∈ frontier (s.projection ⁻¹' R) ↔ ell (B y) = 0)
    (U : K.faces → Set t.Carrier) (hU : ∀ τ, IsOpen (U τ))
    (hretain : ∀ τ : K.faces, MapsTo j (convexHull ℝ (τ.val : Set V)) (U τ)) :
    ∃ (ell : E →ᴬ[ℝ] ℝ) (A : AffineSubspace ℝ E)
      (P P₀ : SimplicialComplex ℝ E) (L : K₀.faces → SimplicialComplex ℝ E) (ε : ℝ),
      ell.toAffineMap.linear ≠ 0 ∧ (A : Set E) = {z | ell z = 0} ∧
      A.direction = ell.toAffineMap.linear.ker ∧ 0 < ε ∧
      P.faces.Finite ∧ P₀.faces.Finite ∧
      P.space = Q '' (j '' K₁.space ∩ Q.source) ∩ J.space ∧
      P₀.space = Q '' (j '' K₀.space ∩ Q.source) ∩ J.space ∧
      P₀.space ⊆ P.space ∧ P.space ⊆ J.space ∧
      P.space ∩ frontier J.space ⊆ P₀.space ∧ P.space ⊆ A ∧
      (∀ τ : K₀.faces, (L τ).faces.Finite ∧
        (L τ).space = B '' (((step.projection ∘ step.inclusion) ∘ j) ''
          convexHull ℝ (τ.val : Set V) ∩ B.source) ∩ J.space ∧
        (∀ a ∈ (L τ).faces, a.card ≤ τ.val.card) ∧ (L τ).space ⊆ A) ∧
      ∃ R₀ T T₀ : SimplicialComplex ℝ E,
        R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ T ≤ R₀ ∧ T.space = P.space ∧
        T₀ ≤ T ∧ T₀.space = P₀.space ∧
        (∀ a ∈ T.faces, (∀ v ∈ a, v ∈ T₀.vertices) → a ∈ T₀.faces) ∧
        ∃ H : PLCarrierMotion J.space P₀.space ε,
          R₀.AffineOnFaces (H.map 1) ∧
          (∀ a z, ell (H.map a z) = ell z) ∧
          (∃ V : SimplicialComplex ℝ E,
            V.faces.Finite ∧ V.space = H.map 1 '' P.space) ∧
          (∀ τ a, a ∈ T.faces → a ∉ T₀.faces → ∀ b, b ∈ (L τ).faces →
            affineSpan ℝ (H.map 1 '' (a : Set E) ∪ (b : Set E)) = A ∨
              Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (a : Set E))))
                (convexHull ℝ (b : Set E))) ∧
          ∃ G : I → t.Carrier ≃ₜ t.Carrier,
            Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
            Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
            (∀ x, G 0 x = x) ∧
            (∀ a, EqOn (G a) (Q.symm ∘ H.map a ∘ Q) Q.source) ∧
            (∀ a, EqOn (G a) id (Q.symm '' J.space)ᶜ) ∧
            (∀ a, EqOn (G a) id (j '' K₀.space)) ∧
            (∀ a, (G a) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R ∧
              (G a) ⁻¹' frontier (t.projection ⁻¹' R) = frontier (t.projection ⁻¹' R) ∧
              (G a) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
            (∀ a k l, (t.charts k).symm.trans
              ((G a).toOpenPartialHomeomorph.trans (t.charts l)) ∈
                piecewiseAffineGroupoid E) ∧
            (∀ a k l, (t.charts k).symm.trans
              ((G a).symm.toOpenPartialHomeomorph.trans (t.charts l)) ∈
                piecewiseAffineGroupoid E) ∧
            ∀ a τ, MapsTo (G a ∘ j) (convexHull ℝ (τ.val : Set V)) (U τ) := by
  classical
  let : Finite K.faces := hK.to_subtype
  have hlowerfront (x : V) (hx : x ∈ K₁.space) :
      step.projection (step.inclusion (j x)) ∈ frontier (s.projection ⁻¹' R) := by
    have hxfront := hfrontier hx
    rw [step.frontier_preimage R] at hxfront
    exact hxfront
  have hboundary : ∃ ell : E →ᴬ[ℝ] ℝ, ell.toAffineMap.linear ≠ 0 ∧
      (∀ y ∈ B.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ ell (B y)) ∧
      ∀ y ∈ B.source, y ∈ frontier (s.projection ⁻¹' R) ↔ ell (B y) = 0 := by
    rcases hmodel with hinside | hboundary
    · obtain ⟨x, hx⟩ := K.nonempty_of_mem_faces hfaceK
      have hxσ : x ∈ convexHull ℝ (face : Set V) := subset_convexHull ℝ _ hx
      have hxK₁ : x ∈ K₁.space := hsource.symm.subset (Or.inr hxσ)
      exact False.elim ((hlowerfront x hxK₁).2 (hinside (hmaps (hface x hxσ).1)))
    · exact hboundary
  obtain ⟨ell, hell, hhalf, hfront⟩ := hboundary
  obtain ⟨A, hAs, hAdir⟩ := ell.toAffineMap.exists_zero_level_affineSubspace hell
  have hsourceA : ∀ x ∈ K₁.space, j x ∈ Q.source → Q (j x) ∈ A := by
    intro x hx hxQ
    change Q (j x) ∈ (A : Set E)
    rw [hAs]
    change ell (Q (j x)) = 0
    rw [hval]
    exact (hfront _ (hmaps hxQ)).mp (hlowerfront x hx)
  have htargetA : ∀ x ∈ K₀.space,
      step.projection (step.inclusion (j x)) ∈ B.source →
        B (step.projection (step.inclusion (j x))) ∈ A := by
    intro x hx hxB
    change B (step.projection (step.inclusion (j x))) ∈ (A : Set E)
    rw [hAs]
    exact (hfront _ hxB).mp
      (hlowerfront x (SimplicialComplex.space_subset_of_le hK₀ hx))
  let Z (τ : K.faces) : Set t.Carrier := j '' convexHull ℝ (τ.val : Set V)
  have hZ (τ : K.faces) : IsCompact (Z τ) :=
    (τ.val.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (hj.continuousOn.mono (K.convexHull_subset_space τ.property))
  obtain ⟨ε, hε, hmargin⟩ := Q.symm.exists_supported_motion_margin
    (J.isCompact_space_of_finite hJ) hJQ Z U hZ hU
    (fun τ => by rintro _ ⟨x, hx, rfl⟩; exact hretain τ hx)
  have hproj : PolyhedralPLInCharts s.charts
      ((step.projection ∘ step.inclusion) ∘ j) K.space :=
    hj.project step.chartIndex (step.projection.continuous.comp step.inclusion.continuous)
      step.chart_source (fun k x _ => congrFun (step.chart_forward k) x)
  obtain ⟨P, P₀, L, hP, hP₀, hPs, hP₀s, hP₀P, hPJ, hPfront, hPA, hL,
    R₀, T, T₀, hR₀, hR₀J, hT, hTs, hT₀, hT₀s, hfull,
    H, hHaff, hHdir, hHimage, hHfaces⟩ :=
    exists_original_level_face_coordinate_position K K₀ K₁ hK hK₀ hK₁ hj hproj face hsource
      Q B hQ hB J hJ hcv hJQ (hJQ.trans htarget.subset)
      (fun x hx _ => (hface x hx).2) A hsourceA htargetA hε
  have hheight (a : I) (z : E) : ell (H.map a z) = ell z := by
    apply (H.map a).affine_height_eq_of_displacement_mem_ker ell.toAffineMap
    intro y
    rw [← hAdir]
    exact hHdir a y
  have hupper : ∀ z ∈ Q.target, Q.symm z ∈ t.projection ⁻¹' R ↔ 0 ≤ ell z := by
    intro z hz
    rw [step.region_preimage R]
    change step.projection (step.inclusion (Q.symm z)) ∈ s.projection ⁻¹' R ↔ _
    calc
      step.projection (step.inclusion (Q.symm z)) ∈ s.projection ⁻¹' R ↔
          0 ≤ ell (B (step.projection (step.inclusion (Q.symm z)))) :=
        hhalf _ (hmaps (Q.map_target hz))
      _ ↔ 0 ≤ ell z := by rw [← hval, Q.right_inv hz]
  have hFup : t.projection ⁻¹' Fmark =
      frontier (t.projection ⁻¹' R) ∩ t.projection ⁻¹' W := by
    rw [hF, preimage_inter, t.frontier_region R]
  have hsupport : Q.symm '' J.space ⊆ t.projection ⁻¹' W := by
    rintro _ ⟨z, hz, rfl⟩
    exact hmark (Q.map_target (hJQ hz))
  obtain ⟨G, hG, hGinv, hzero, hGQ, hGout, hprotected, _, _,
    hGregion, hGPL, hGinvPL⟩ :=
    H.exists_marked_chart_motion J hJ Q.symm hJQ (hP₀P.trans (hPJ.trans hJQ))
      t.charts t.compatible hQ hupper
      (fun a z => by change 0 ≤ ell (H.map a z) ↔ 0 ≤ ell z; rw [hheight]) hFup hsupport
  have hformula (a : I) : EqOn (G a) (Q.symm ∘ H.map a ∘ Q) Q.source := hGQ a
  have hprefix (a : I) : EqOn (G a) id (j '' K₀.space) :=
    Q.symm.eqOn_of_fixed_clipped_carrier hJQ hP₀s (hprotected a) (hGout a)
  have hkeep (a : I) (τ : K.faces) :
      MapsTo (G a ∘ j) (convexHull ℝ (τ.val : Set V)) (U τ) := by
    intro x hx
    exact hmargin (H.map a) (G a) (hformula a) (hGout a)
      (fun z _ => H.small a z) τ (mem_image_of_mem j hx)
  exact ⟨ell, A, P, P₀, L, ε, hell, hAs, hAdir, hε,
    hP, hP₀, hPs, hP₀s, hP₀P, hPJ, hPfront, hPA, hL,
    R₀, T, T₀, hR₀, hR₀J, hT, hTs, hT₀, hT₀s, hfull,
    H, hHaff, hheight, hHimage, hHfaces,
    G, hG, hGinv, hzero, hformula, hGout, hprefix, hGregion, hGPL, hGinvPL, hkeep⟩

end Geometry.OriginalPLTower
