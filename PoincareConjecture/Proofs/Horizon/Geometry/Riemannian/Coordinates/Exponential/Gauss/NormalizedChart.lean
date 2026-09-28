import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.FirstJet
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Orthonormal

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_normalized_exponential_chart_firstJet (g : RiemannianMetric n M) (p : M) :
    ∃ e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M,
      (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      (∀ y ∈ e.source, ∀ w, g.pullbackCoefficients e y y w = inner ℝ y w) ∧
      g.pullbackCoefficients e 0 = innerSL ℝ ∧
      CoordinateExponential.christoffelBilinear (g.pullbackCoefficients e) 0 = 0 := by
  obtain ⟨f, hf0, hfp, hf, hfi, hgauss, _⟩ := g.exists_exponential_chart_gauss p
  obtain ⟨L, hL⟩ := g.exists_orthonormal_coordinate_frame p
  let e := L.toHomeomorph.toOpenPartialHomeomorph.trans f
  have he0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source :=
    ⟨Set.mem_univ _, by simpa using hf0⟩
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := by
    change ContMDiffOn (𝓡 n) (𝓡 n) ∞ (f ∘ L) e.source
    exact hf.comp (contMDiff_iff_contDiff.mpr L.contDiff).contMDiffOn
      (fun x hx => hx.2)
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := by
    change ContMDiffOn (𝓡 n) (𝓡 n) ∞ (L.symm ∘ f.symm) e.target
    exact (contMDiff_iff_contDiff.mpr L.symm.contDiff).comp_contMDiffOn
      (hfi.mono fun x hx => hx.1)
  have hG : ∀ y ∈ e.source, ∀ w,
      g.pullbackCoefficients e y y w = inner ℝ y w := by
    intro y hy w
    have hfd : MDifferentiableAt (𝓡 n) (𝓡 n) f (L y) :=
      (hf.contMDiffAt (f.open_source.mem_nhds hy.2)).mdifferentiableAt (by simp)
    have hLd : MDifferentiableAt (𝓡 n) (𝓡 n) L y :=
      mdifferentiableAt_iff_differentiableAt.mpr L.differentiableAt
    have hd := mfderiv_comp y hfd hLd
    have hLm : mfderiv (𝓡 n) (𝓡 n) L y = L.toContinuousLinearMap := by
      simpa only [mfderiv_eq_fderiv] using L.hasFDerivAt.fderiv
    rw [hLm] at hd
    have hpull : g.pullbackCoefficients e y y w =
        g.pullbackCoefficients f (L y) (L y) (L w) := by
      unfold pullbackCoefficients
      simp only [ContinuousLinearMap.bilinearComp_apply]
      change g.inner (f (L y)) (mfderiv (𝓡 n) (𝓡 n) (f ∘ L) y y)
        (mfderiv (𝓡 n) (𝓡 n) (f ∘ L) y w) = _
      rw [hd]
      rfl
    rw [hpull]
    change g.inner (f (L y)) (mfderiv (𝓡 n) (𝓡 n) f (L y) (L y))
      (mfderiv (𝓡 n) (𝓡 n) f (L y) (L w)) = _
    rw [hgauss (L y) hy.2 (L w), ← g.chartCoefficients_center]
    exact hL y w
  have hcoeff : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) e.source :=
    fun y hy => (g.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (e.open_source.mem_nhds hy))).contDiffWithinAt
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  refine ⟨e, he0, ?_, he, hei, hG, ?_, ?_⟩
  · change f (L 0) = p
    simpa only [map_zero] using hfp
  · apply CoordinateExponential.metric_zero_eq_innerSL_of_gauss
      ((hcoeff.contDiffAt (e.open_source.mem_nhds he0)).differentiableAt (by simp))
    filter_upwards [e.open_source.mem_nhds he0] with y hy
    exact hG y hy
  · apply CoordinateExponential.christoffelBilinear_zero_of_local_gauss
      e.open_source he0 (g.pullbackCoefficients e) hcoeff
      (fun y _ v w => g.symm (e y) _ _) ?_ hG
    intro y hy v hv
    apply g.pos (e y)
    intro hz
    apply hv
    apply hD.mfderiv_injective hy
    rw [map_zero]
    convert! hz using 1

end PoincareConjecture.RiemannianMetric
