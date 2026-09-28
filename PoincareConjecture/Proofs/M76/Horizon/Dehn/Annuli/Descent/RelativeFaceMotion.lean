import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.InteriorWindows
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartFacePosition
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PLCarrierInteriorChartMotion
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SupportedChartMotionMargin












set_option autoImplicit false

open Set Geometry Topology unitInterval

namespace Geometry.OriginalPLTower

variable {U E V M ι : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M E} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C}




theorem Step.exists_relative_interior_face_motion (step : Step s t)
    (K K₀ K₁ : SimplicialComplex ℝ V) (hK : K.faces.Finite)
    (hK₀ : K₀ ≤ K₁) (hK₁ : K₁ ≤ K)
    {j : V → t.Carrier} (hj : PolyhedralPLInCharts t.charts j K.space)
    (face : Finset V) (hsource : K₁.space = K₀.space ∪ convexHull ℝ (face : Set V))
    (Q : OpenPartialHomeomorph t.Carrier E) (B : OpenPartialHomeomorph s.Carrier E)
    (hQ : ∀ k, (t.charts k).symm.trans Q ∈ piecewiseAffineGroupoid E)
    (hB : ∀ k, (s.charts k).symm.trans B ∈ piecewiseAffineGroupoid E)
    (J : SimplicialComplex ℝ E) (hJ : J.faces.Finite) (hcv : Convex ℝ J.space)
    (hJQ : J.space ⊆ Q.target) (hJB : J.space ⊆ B.target)
    (hfree : ∀ x ∈ convexHull ℝ (face : Set V),
      x ∉ K₀.space → Q (j x) ∈ interior J.space)
    (R Fmark : Set M) (hF : Fmark ⊆ frontier R)
    (hinside : Q.source ⊆ interior (t.projection ⁻¹' R))
    (A : Set V) (havoid : Disjoint Q.source (j '' A))
    (N : K.faces → Set t.Carrier) (hN : ∀ a, IsOpen (N a))
    (hretain : ∀ a : K.faces, MapsTo j (convexHull ℝ (a.val : Set V)) (N a)) :
    ∃ (P P₀ : SimplicialComplex ℝ E) (L : K₀.faces → SimplicialComplex ℝ E) (ε : ℝ),
      P.faces.Finite ∧ P₀.faces.Finite ∧ 0 < ε ∧
      P.space = Q '' (j '' K₁.space ∩ Q.source) ∩ J.space ∧
      P₀.space = Q '' (j '' K₀.space ∩ Q.source) ∩ J.space ∧
      (∀ a : K₀.faces, (L a).faces.Finite ∧
        (L a).space = B '' (((step.projection ∘ step.inclusion) ∘ j) ''
          convexHull ℝ (a.val : Set V) ∩ B.source) ∩ J.space ∧
        ∀ b ∈ (L a).faces, b.card ≤ a.val.card) ∧
      ∃ (K' T T₀ : SimplicialComplex ℝ E) (H : PLCarrierMotion J.space P₀.space ε),
        K'.faces.Finite ∧ K'.IsSubdivision J ∧ T ≤ K' ∧ T.space = P.space ∧
        T₀ ≤ T ∧ T₀.space = P₀.space ∧
        (∀ a ∈ T.faces, (∀ v ∈ a, v ∈ T₀.vertices) → a ∈ T₀.faces) ∧
        K'.AffineOnFaces (H.map 1) ∧
        (∃ J' : SimplicialComplex ℝ E, J'.faces.Finite ∧ J'.space = H.map 1 '' P.space) ∧
        (∀ a b, b ∈ T.faces → b ∉ T₀.faces → ∀ c, c ∈ (L a).faces →
          affineSpan ℝ (H.map 1 '' (b : Set E) ∪ (c : Set E)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (b : Set E))))
              (convexHull ℝ (c : Set E))) ∧
        ∃ G : I → t.Carrier ≃ₜ t.Carrier,
          Continuous (fun z : I × t.Carrier ↦ G z.1 z.2) ∧
          Continuous (fun z : I × t.Carrier ↦ (G z.1).symm z.2) ∧
          (∀ x, G 0 x = x) ∧
          (∀ u, EqOn (G u) (Q.symm ∘ H.map u ∘ Q) Q.source) ∧
          (∀ u, EqOn (G u) id (Q.symm '' J.space)ᶜ) ∧
          (∀ u, EqOn (G u) id (j '' K₀.space)) ∧
          (∀ u, EqOn (G u) id (j '' A)) ∧
          (∀ u, EqOn (G u) id (frontier (t.projection ⁻¹' R))) ∧
          (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R ∧
            (G u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
          (∀ u k l, (t.charts k).symm.trans
            ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid E) ∧
          (∀ u k l, (t.charts k).symm.trans
            ((G u).symm.toOpenPartialHomeomorph.trans (t.charts l)) ∈
              piecewiseAffineGroupoid E) ∧
          ∀ u a, MapsTo (G u ∘ j) (convexHull ℝ (a.val : Set V)) (N a) := by
  classical
  let : Finite K.faces := hK.to_subtype
  let D (a : K.faces) := j '' convexHull ℝ (a.val : Set V)
  have hD (a : K.faces) : IsCompact (D a) :=
    (a.val.finite_toSet.isCompact_convexHull ℝ).image_of_continuousOn
      (hj.continuousOn.mono (K.convexHull_subset_space a.property))
  obtain ⟨ε, hε, hmargin⟩ := Q.symm.exists_supported_motion_margin
    (J.isCompact_space_of_finite hJ) hJQ D N hD hN
    (fun a ↦ by rintro _ ⟨x, hx, rfl⟩; exact hretain a hx)
  have hp : PolyhedralPLInCharts s.charts
      ((step.projection ∘ step.inclusion) ∘ j) K.space :=
    hj.project step.chartIndex (step.projection.continuous.comp step.inclusion.continuous)
      step.chart_source (fun k x _ ↦ congrFun (step.chart_forward k) x)
  obtain ⟨P, P₀, L, hP, hP₀, hPs, hP₀s, hP₀P, hPJ, _, hL,
    K', T, T₀, hK', hK'J, hT, hTs, hT₀, hT₀s, hfull, H, hHaff, hHimage, hHfaces⟩ :=
    exists_original_face_coordinate_position K K₀ K₁ hK hK₀ hK₁ hj hp face hsource
      Q B hQ hB J hJ hcv hJQ hJB hfree hε
  have hFup : t.projection ⁻¹' Fmark ⊆ frontier (t.projection ⁻¹' R) := by
    rw [t.frontier_region R]
    exact preimage_mono hF
  obtain ⟨G, hG, hGinv, hzero, hformula, hout, hprotected, _, _,
    hfront, hregion, hGPL, hGinvPL⟩ :=
    H.exists_interior_chart_motion J hJ Q.symm hJQ
      (hP₀P.trans (hPJ.trans hJQ)) t.charts t.compatible hQ hFup (Or.inl hinside)
  have hprefix (u : I) : EqOn (G u) id (j '' K₀.space) :=
    Q.symm.eqOn_of_fixed_clipped_carrier hJQ hP₀s (hprotected u) (hout u)
  have hcollar (u : I) : EqOn (G u) id (j '' A) := by
    intro x hx
    apply hout u
    rintro ⟨z, hz, rfl⟩
    exact disjoint_left.mp havoid (Q.map_target (hJQ hz)) hx
  refine ⟨P, P₀, L, ε, hP, hP₀, hε, hPs, hP₀s, hL,
    K', T, T₀, H, hK', hK'J, hT, hTs, hT₀, hT₀s, hfull, hHaff, hHimage, hHfaces,
    G, hG, hGinv, hzero, hformula, hout, hprefix, hcollar, hfront, hregion, hGPL, hGinvPL, ?_⟩
  intro u a x hx
  exact hmargin (H.map u) (G u) (hformula u) (hout u)
    (fun z _ ↦ H.small u z) a (mem_image_of_mem j hx)

end Geometry.OriginalPLTower
