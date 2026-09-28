import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartFaceImage
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineCoverFaceBounds
import PoincareConjecture.Proofs.M76.PrimeReduction.AffineContactFiniteness









set_option autoImplicit false

open Set

namespace Geometry




theorem PolyhedralPLInCharts.exists_finite_chart_image_of_face_card_le
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X F}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    {d : ℕ} (hcard : ∀ σ ∈ K.faces, σ.card ≤ d + 1)
    (Q : OpenPartialHomeomorph X F)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid F)
    (J : SimplicialComplex ℝ F) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) :
    ∃ L : SimplicialComplex ℝ F, L.faces.Finite ∧
      L.space = Q '' (f '' K.space ∩ Q.source) ∩ J.space ∧
      ∀ τ ∈ L.faces, τ.card ≤ d + 1 := by
  classical
  obtain ⟨L, hL, hLs⟩ := hf.exists_finite_chart_image_intersection K hK Q hQ J hJ hJQ
  have hfaces (σ : K.faces) :=
    hf.exists_finite_face_chart_image K hK σ.property Q hQ J hJ hJQ
  choose A hA hAs hAc using hfaces
  let : Fintype K.faces := hK.fintype
  let T : Finset (AffineSubspace ℝ F) := Finset.univ.biUnion fun σ : K.faces =>
    (hA σ).toFinset.image fun τ : Finset F => affineSpan ℝ (τ : Set F)
  have hdim : ∀ B ∈ T, Module.finrank ℝ B.direction ≤ d := by
    intro B hB
    obtain ⟨σ, _, hσ⟩ := Finset.mem_biUnion.mp hB
    obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.mp hσ
    have hτA : τ ∈ (A σ).faces := (hA σ).mem_toFinset.mp hτ
    exact finrank_affineSpan_finset_le ((A σ).nonempty_of_mem_faces hτA)
      ((hAc σ τ hτA).trans (hcard σ σ.property))
  have hcover : ∀ z ∈ L.space, ∃ B ∈ T, z ∈ B := by
    intro z hz
    obtain ⟨⟨y, ⟨⟨x, hx, hxy⟩, hyQ⟩, hyz⟩, hzJ⟩ := hLs.subset hz
    obtain ⟨σ, hσ, hxσ⟩ := SimplicialComplex.mem_space_iff.mp hx
    let a : K.faces := ⟨σ, hσ⟩
    have hzA : z ∈ (A a).space := (hAs a).symm.subset
      ⟨⟨y, ⟨⟨x, hxσ, hxy⟩, hyQ⟩, hyz⟩, hzJ⟩
    obtain ⟨τ, hτ, hzτ⟩ := SimplicialComplex.mem_space_iff.mp hzA
    refine ⟨affineSpan ℝ (τ : Set F), ?_, convexHull_subset_affineSpan _ hzτ⟩
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨τ, (hA a).mem_toFinset.mpr hτ, rfl⟩⟩
  exact ⟨L, hL, hLs, fun _ hτ => L.face_card_le_of_finite_affine_cover T hdim hcover hτ⟩

end Geometry
