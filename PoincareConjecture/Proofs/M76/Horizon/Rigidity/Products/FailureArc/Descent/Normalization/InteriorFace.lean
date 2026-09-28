import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.InteriorCarrier
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartFacePosition
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierInteriorChartMotion
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






theorem Step.exists_interior_surface_face_motion
    {s t : Stage e S f r C} (step : Step s t)
    (K K₀ K₁ : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (hK₀ : K₀ ≤ K₁) (hK₁ : K₁ ≤ K)
    {face : Finset V} (hfaceK : face ∈ K.faces)
    (hsource : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    {boundary : Set V} (hrim : boundary ⊆ K₀.space)
    {R Fmark : Set M} (hF : Fmark ⊆ frontier R)
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (hjR : MapsTo j K.space (t.projection ⁻¹' R))
    (hproper : ∀ x ∈ K.space,
      j x ∈ frontier (t.projection ⁻¹' R) ↔ x ∈ boundary)
    (Q : OpenPartialHomeomorph t.Carrier E)
    (B : OpenPartialHomeomorph s.Carrier E)
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid E)
    (hB : ∀ k, (s.charts k).symm.trans B ∈ piecewiseAffineGroupoid E)
    (htarget : Q.target = B.target)
    (hval : ∀ y, Q y = B (step.projection (step.inclusion y)))
    (hmaps : MapsTo (step.projection ∘ step.inclusion) Q.source B.source)
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
    ∃ (Jrel P P₀ : SimplicialComplex ℝ E)
      (L : K₀.faces → SimplicialComplex ℝ E) (ε : ℝ),
      Jrel.faces.Finite ∧ Convex ℝ Jrel.space ∧ Jrel.space ⊆ J.space ∧
      (∀ x ∈ convexHull ℝ (face : Set V),
        x ∉ K₀.space → Q (j x) ∈ interior Jrel.space) ∧ 0 < ε ∧
      P.faces.Finite ∧ P₀.faces.Finite ∧
      P.space = Q '' (j '' K₁.space ∩ Q.source) ∩ Jrel.space ∧
      P₀.space = Q '' (j '' K₀.space ∩ Q.source) ∩ Jrel.space ∧
      P₀.space ⊆ P.space ∧ P.space ⊆ Jrel.space ∧
      P.space ∩ frontier Jrel.space ⊆ P₀.space ∧
      (∀ τ : K₀.faces, (L τ).faces.Finite ∧
        (L τ).space = B '' (((step.projection ∘ step.inclusion) ∘ j) ''
          convexHull ℝ (τ.val : Set V) ∩ B.source) ∩ Jrel.space ∧
        ∀ a ∈ (L τ).faces, a.card ≤ τ.val.card) ∧
      ∃ R₀ T T₀ : SimplicialComplex ℝ E,
        R₀.faces.Finite ∧ R₀.IsSubdivision Jrel ∧ T ≤ R₀ ∧ T.space = P.space ∧
        T₀ ≤ T ∧ T₀.space = P₀.space ∧
        (∀ a ∈ T.faces, (∀ v ∈ a, v ∈ T₀.vertices) → a ∈ T₀.faces) ∧
        ∃ H : PLCarrierMotion Jrel.space P₀.space ε,
          R₀.AffineOnFaces (H.map 1) ∧
          (∃ V : SimplicialComplex ℝ E,
            V.faces.Finite ∧ V.space = H.map 1 '' P.space) ∧
          (∀ τ a, a ∈ T.faces → a ∉ T₀.faces → ∀ b, b ∈ (L τ).faces →
            affineSpan ℝ (H.map 1 '' (a : Set E) ∪ (b : Set E)) = ⊤ ∨
              Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (a : Set E))))
                (convexHull ℝ (b : Set E))) ∧
          ∃ G : I → t.Carrier ≃ₜ t.Carrier,
            Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
            Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
            (∀ x, G 0 x = x) ∧
            (∀ a, EqOn (G a) (Q.symm ∘ H.map a ∘ Q) Q.source) ∧
            (∀ a, EqOn (G a) id (Q.symm '' Jrel.space)ᶜ) ∧
            (∀ a, EqOn (G a) id (j '' K₀.space)) ∧
            (∀ a, EqOn (G a) id (frontier (t.projection ⁻¹' R))) ∧
            (∀ a, (G a) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R ∧
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
  obtain ⟨Jrel, hJrel, hrelcv, hrelJ, hfree, hrelmodel⟩ :=
    step.exists_interior_surface_face_carrier K K₀ hfaceK hrim hjR hproper Q B hval hmaps
      J hJ hcv hface hmodel
  have hrelQ : Jrel.space ⊆ Q.target := hrelJ.trans hJQ
  have hrelB : Jrel.space ⊆ B.target := hrelQ.trans htarget.subset
  let A (τ : K.faces) : Set t.Carrier := j '' convexHull ℝ (τ.val : Set V)
  have hA (τ : K.faces) : IsCompact (A τ) :=
    (τ.val.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (hj.continuousOn.mono (K.convexHull_subset_space τ.property))
  obtain ⟨ε, hε, hmargin⟩ := Q.symm.exists_supported_motion_margin
    (Jrel.isCompact_space_of_finite hJrel) hrelQ A U hA hU
    (fun τ => by rintro _ ⟨x, hx, rfl⟩; exact hretain τ hx)
  have hproj : PolyhedralPLInCharts s.charts
      ((step.projection ∘ step.inclusion) ∘ j) K.space :=
    hj.project step.chartIndex (step.projection.continuous.comp step.inclusion.continuous)
      step.chart_source (fun k x _ => congrFun (step.chart_forward k) x)
  obtain ⟨P, P₀, L, hP, hP₀, hPs, hP₀s, hP₀P, hPJ, hfront, hL,
    R₀, T, T₀, hR₀, hR₀J, hT, hTs, hT₀, hT₀s, hfull,
    H, hHaff, hHimage, hHfaces⟩ :=
    exists_original_face_coordinate_position K K₀ K₁ hK hK₀ hK₁ hj hproj face hsource
      Q B hQ hB Jrel hJrel hrelcv hrelQ hrelB hfree hε
  have huppermodel : Q.source ⊆ interior (t.projection ⁻¹' R) ∨
      ∃ ell : E →ᴬ[ℝ] ℝ, ell.toAffineMap.linear ≠ 0 ∧
        Jrel.space ⊆ {z | 0 ≤ ell z} ∧
        ∀ z ∈ Q.target, Q.symm z ∈ t.projection ⁻¹' R ↔ 0 ≤ ell z := by
    rcases hrelmodel with ⟨_, hinside⟩ | ⟨ell, hell, hJs, hhalf, _⟩
    · exact Or.inl hinside
    · refine Or.inr ⟨ell, hell, hJs.subset.trans inter_subset_right, ?_⟩
      intro z hz
      simpa only [Q.right_inv hz] using hhalf (Q.symm z) (Q.map_target hz)
  have hFup : t.projection ⁻¹' Fmark ⊆ frontier (t.projection ⁻¹' R) := by
    rw [t.frontier_region R]
    exact preimage_mono hF
  obtain ⟨G, hG, hGinv, hzero, hGQ, hGout, hprotected, _, _,
    hGfront, hGregion, hGPL, hGinvPL⟩ :=
    H.exists_interior_chart_motion Jrel hJrel Q.symm hrelQ
      (hP₀P.trans (hPJ.trans hrelQ)) t.charts t.compatible hQ hFup huppermodel
  have hformula (a : I) : EqOn (G a) (Q.symm ∘ H.map a ∘ Q) Q.source :=
    hGQ a
  have hprefix (a : I) : EqOn (G a) id (j '' K₀.space) :=
    Q.symm.eqOn_of_fixed_clipped_carrier hrelQ hP₀s (hprotected a) (hGout a)
  have hkeep (a : I) (τ : K.faces) :
      MapsTo (G a ∘ j) (convexHull ℝ (τ.val : Set V)) (U τ) := by
    intro x hx
    exact hmargin (H.map a) (G a) (hformula a) (hGout a)
      (fun z _ => H.small a z) τ (mem_image_of_mem j hx)
  exact ⟨Jrel, P, P₀, L, ε, hJrel, hrelcv, hrelJ, hfree, hε,
    hP, hP₀, hPs, hP₀s, hP₀P, hPJ, hfront, hL,
    R₀, T, T₀, hR₀, hR₀J, hT, hTs, hT₀, hT₀s, hfull,
    H, hHaff, hHimage, hHfaces, G, hG, hGinv, hzero, hformula, hGout,
    hprefix, hGfront, hGregion, hGPL, hGinvPL, hkeep⟩

end Geometry.OriginalPLTower
