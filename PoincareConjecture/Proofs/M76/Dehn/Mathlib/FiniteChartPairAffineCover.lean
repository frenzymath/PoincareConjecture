import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteClippedChartInverse
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.FiniteAffineCoverTransport
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic

set_option autoImplicit false

open Set

namespace Geometry

theorem PolyhedralPLInCharts.exists_finite_paired_chart_cover
    {E E' F X Y ι κ : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    {e : ι → OpenPartialHomeomorph X F} {e' : κ → OpenPartialHomeomorph Y F}
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (L : SimplicialComplex ℝ E') (hL : L.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space) (hfi : InjOn f K.space)
    {g : E' → Y} (hg : PolyhedralPLInCharts e' g L.space) (hgi : InjOn g L.space)
    (Q : OpenPartialHomeomorph X F)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid F)
    (B : OpenPartialHomeomorph Y F)
    (hB : ∀ i, (e' i).symm.trans B ∈ piecewiseAffineGroupoid F)
    (J : SimplicialComplex ℝ F) (hJ : J.faces.Finite)
    (hJQ : J.space ⊆ Q.target) (hJB : J.space ⊆ B.target)
    {C : Set F} (hCJ : C ⊆ J.space) (T : Finset (AffineSubspace ℝ F)) {d : ℕ}
    (hd : ∀ A ∈ T, Module.finrank ℝ A.direction ≤ d)
    (hcover : ∀ w ∈ C, ∃ A ∈ T, w ∈ A) :
    ∃ U : Finset (AffineSubspace ℝ (E × E')),
      (∀ A ∈ U, Module.finrank ℝ A.direction ≤ d) ∧
      ∀ x ∈ K.space, ∀ y ∈ L.space,
        f x ∈ Q.source → g y ∈ B.source → Q (f x) = B (g y) → Q (f x) ∈ C →
        ∃ A ∈ U, (x, y) ∈ A := by
  obtain ⟨I₁, a, hI₁, hI₁s, ha, _, _, hal⟩ :=
    hf.exists_finite_clipped_chart_inverse K hK hfi Q hQ J hJ hJQ
  obtain ⟨I₂, b, hI₂, hI₂s, hb, _, _, hbl⟩ :=
    hg.exists_finite_clipped_chart_inverse L hL hgi B hB J hJ hJB
  obtain ⟨N, hN, hNs⟩ := I₁.exists_finite_triangulation_inter I₂ hI₁ hI₂
  have haN := ha.restrict N hN (hNs.subset.trans inter_subset_left)
  have hbN := hb.restrict N hN (hNs.subset.trans inter_subset_right)
  obtain ⟨U, hU, hUc⟩ := (haN.prod_mk hbN).exists_finite_affine_image_cover
    (C := C ∩ N.space) inter_subset_right T hd (fun w hw => hcover w hw.1)
  refine ⟨U, hU, ?_⟩
  intro x hx y hy hfx hgy heq hw
  have hwJ : Q (f x) ∈ J.space := hCJ hw
  have hyJ : B (g y) ∈ J.space := heq ▸ hwJ
  have hwN : Q (f x) ∈ N.space := by
    rw [hNs, hI₁s, hI₂s]
    exact ⟨⟨⟨f x, ⟨mem_image_of_mem f hx, hfx⟩, rfl⟩, hwJ⟩,
      ⟨⟨g y, ⟨mem_image_of_mem g hy, hgy⟩, heq.symm⟩, hwJ⟩⟩
  have hpair : (a (Q (f x)), b (Q (f x))) = (x, y) := by
    apply Prod.ext (hal x hx hfx hwJ)
    rw [heq]
    exact hbl y hy hgy hyJ
  exact hUc (x, y) ⟨Q (f x), ⟨hw, hwN⟩, hpair⟩

end Geometry
