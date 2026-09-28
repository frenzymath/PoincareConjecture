import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartPrefixCarriers
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartFaceImage
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.AffineLevelPolyhedronPosition

set_option autoImplicit false

open Set

namespace Geometry

theorem exists_original_level_face_coordinate_position
    {E F X Y ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    {e : ι → OpenPartialHomeomorph X F} {d : κ → OpenPartialHomeomorph Y F}
    (K K₀ K₁ : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hK₀ : K₀ ≤ K₁) (hK₁ : K₁ ≤ K)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    {h : E → Y} (hh : PolyhedralPLInCharts d h K.space)
    (σ : Finset E) (hsource : K₁.space = K₀.space ∪ convexHull ℝ (σ : Set E))
    (Q : OpenPartialHomeomorph X F) (B : OpenPartialHomeomorph Y F)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid F)
    (hB : ∀ i, (d i).symm.trans B ∈ piecewiseAffineGroupoid F)
    (J : SimplicialComplex ℝ F) (hJ : J.faces.Finite) (hcv : Convex ℝ J.space)
    (hJQ : J.space ⊆ Q.target) (hJB : J.space ⊆ B.target)
    (hfree : ∀ x ∈ convexHull ℝ (σ : Set E),
      x ∉ K₀.space → Q (f x) ∈ interior J.space)
    (A : AffineSubspace ℝ F)
    (hsourceA : ∀ x ∈ K₁.space, f x ∈ Q.source → Q (f x) ∈ A)
    (htargetA : ∀ x ∈ K₀.space, h x ∈ B.source → B (h x) ∈ A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (P P₀ : SimplicialComplex ℝ F) (L : K₀.faces → SimplicialComplex ℝ F),
      P.faces.Finite ∧ P₀.faces.Finite ∧
      P.space = Q '' (f '' K₁.space ∩ Q.source) ∩ J.space ∧
      P₀.space = Q '' (f '' K₀.space ∩ Q.source) ∩ J.space ∧
      P₀.space ⊆ P.space ∧ P.space ⊆ J.space ∧
      P.space ∩ frontier J.space ⊆ P₀.space ∧ P.space ⊆ A ∧
      (∀ τ : K₀.faces, (L τ).faces.Finite ∧
        (L τ).space = B '' (h '' convexHull ℝ (τ.val : Set E) ∩ B.source) ∩ J.space ∧
        (∀ a ∈ (L τ).faces, a.card ≤ τ.val.card) ∧ (L τ).space ⊆ A) ∧
      ∃ R T T₀ : SimplicialComplex ℝ F,
        R.faces.Finite ∧ R.IsSubdivision J ∧ T ≤ R ∧ T.space = P.space ∧
        T₀ ≤ T ∧ T₀.space = P₀.space ∧
        (∀ a ∈ T.faces, (∀ v ∈ a, v ∈ T₀.vertices) → a ∈ T₀.faces) ∧
        ∃ H : PLCarrierMotion J.space P₀.space ε,
          R.AffineOnFaces (H.map 1) ∧
          (∀ t x, H.map t x - x ∈ A.direction) ∧
          (∃ V : SimplicialComplex ℝ F,
            V.faces.Finite ∧ V.space = H.map 1 '' P.space) ∧
          ∀ τ a, a ∈ T.faces → a ∉ T₀.faces → ∀ b, b ∈ (L τ).faces →
            affineSpan ℝ (H.map 1 '' (a : Set F) ∪ (b : Set F)) = A ∨
              Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (a : Set F))))
                (convexHull ℝ (b : Set F)) := by
  have hK₁fin : K₁.faces.Finite := hK.subset hK₁
  have hK₀fin : K₀.faces.Finite := hK₁fin.subset hK₀
  let : Finite K₀.faces := hK₀fin.to_subtype
  have hf₁ := hf.restrict_finite K₁ hK₁fin (SimplicialComplex.space_subset_of_le hK₁)
  obtain ⟨P, P₀, hP, hP₀, hPs, hP₀s, hP₀P, hPJ, hfront⟩ :=
    hf₁.exists_prefix_face_chart_carriers K₁ K₀ hK₁fin hK₀ hsource Q hQ J hJ hJQ hfree
  have hPA : P.space ⊆ A := by
    intro z hz
    obtain ⟨⟨y, ⟨⟨x, hx, rfl⟩, hfx⟩, rfl⟩, _⟩ := hPs.subset hz
    exact hsourceA x hx hfx
  choose L hL hLs hLdim using fun τ : K₀.faces =>
    hh.exists_finite_face_chart_image K hK (hK₁ (hK₀ τ.property)) B hB J hJ hJB
  have hLA (τ : K₀.faces) : (L τ).space ⊆ A := by
    intro z hz
    obtain ⟨⟨y, ⟨⟨x, hx, rfl⟩, hhx⟩, rfl⟩, _⟩ := (hLs τ).subset hz
    exact htargetA x (K₀.convexHull_subset_space τ.property hx) hhx
  obtain ⟨R, T, T₀, hR, hRJ, hT, hTs, hT₀, hT₀s, hfull,
    H, hHaff, hHdir, hHimage, hHfaces⟩ :=
    J.exists_protected_affine_level_polyhedron_position P P₀ hJ hP hP₀ hcv hP₀P hPJ
      hfront A hPA L hL hLA hε
  exact ⟨P, P₀, L, hP, hP₀, hPs, hP₀s, hP₀P, hPJ, hfront, hPA,
    fun τ => ⟨hL τ, hLs τ, hLdim τ, hLA τ⟩,
    R, T, T₀, hR, hRJ, hT, hTs, hT₀, hT₀s, hfull,
    H, hHaff, hHdir, hHimage, hHfaces⟩

end Geometry
