import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteChartImageIntersection

set_option autoImplicit false

open Set

namespace Geometry

theorem PolyhedralPLInCharts.exists_prefix_face_chart_carriers
    {E F X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X F}
    (K K₀ : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hK₀ : K₀ ≤ K)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    {S : Set E} (hsource : K.space = K₀.space ∪ S)
    (Q : OpenPartialHomeomorph X F)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid F)
    (J : SimplicialComplex ℝ F) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target)
    (hfree : ∀ x ∈ S, x ∉ K₀.space → Q (f x) ∈ interior J.space) :
    ∃ P P₀ : SimplicialComplex ℝ F,
      P.faces.Finite ∧ P₀.faces.Finite ∧
      P.space = Q '' (f '' K.space ∩ Q.source) ∩ J.space ∧
      P₀.space = Q '' (f '' K₀.space ∩ Q.source) ∩ J.space ∧
      P₀.space ⊆ P.space ∧ P.space ⊆ J.space ∧
      P.space ∩ frontier J.space ⊆ P₀.space := by
  have hK₀K : K₀.space ⊆ K.space := SimplicialComplex.space_subset_of_le hK₀
  have hK₀fin : K₀.faces.Finite := hK.subset hK₀
  have hf₀ := hf.restrict_finite K₀ hK₀fin hK₀K
  obtain ⟨P, hP, hPs⟩ := hf.exists_finite_chart_image_intersection K hK Q hQ J hJ hJQ
  obtain ⟨P₀, hP₀, hP₀s⟩ :=
    hf₀.exists_finite_chart_image_intersection K₀ hK₀fin Q hQ J hJ hJQ
  refine ⟨P, P₀, hP, hP₀, hPs, hP₀s, ?_, hPs.subset.trans inter_subset_right, ?_⟩
  · rw [hP₀s, hPs]
    exact inter_subset_inter_left _ (image_mono (inter_subset_inter_left _
      (image_mono hK₀K)))
  · intro z hz
    obtain ⟨⟨y, ⟨⟨x, hx, rfl⟩, hfx⟩, rfl⟩, hzJ⟩ := hPs.subset hz.1
    have hx₀ : x ∈ K₀.space := by
      by_contra hn
      have hxS : x ∈ S := (hsource.subset hx).resolve_left hn
      exact hz.2.2 (hfree x hxS hn)
    exact hP₀s.symm.subset ⟨⟨f x, ⟨mem_image_of_mem f hx₀, hfx⟩, rfl⟩, hzJ⟩

end Geometry

namespace OpenPartialHomeomorph

theorem eqOn_of_fixed_clipped_carrier
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (Q : OpenPartialHomeomorph E X) {C P : Set E} {T : Set X} {g : X → X}
    (hCQ : C ⊆ Q.source)
    (hP : P = Q.symm '' (T ∩ Q.target) ∩ C)
    (hfixed : EqOn g id (Q '' P)) (hout : EqOn g id (Q '' C)ᶜ) :
    EqOn g id T := by
  intro x hx
  by_cases hxC : x ∈ Q '' C
  · obtain ⟨z, hz, rfl⟩ := hxC
    have hzP : z ∈ P := hP.symm.subset
      ⟨⟨Q z, ⟨hx, Q.map_source (hCQ hz)⟩, Q.left_inv (hCQ hz)⟩, hz⟩
    exact hfixed (mem_image_of_mem Q hzP)
  · exact hout hxC

end OpenPartialHomeomorph
