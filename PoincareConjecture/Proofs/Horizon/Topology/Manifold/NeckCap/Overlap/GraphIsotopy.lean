import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cylinder.Sphere
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.Graph
import Mathlib.Geometry.Manifold.Algebra.Structures

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] {g : RiemannianMetric 3 M} (N : EpsilonNeck g)

theorem coordinate_graph_isSmoothEmbedding (f : UnitTwoSphere → ℝ)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    (hdom : ∀ q, f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
      (fun q => N.coordinate_map (q, f q)) :=
  N.coordinatePartialHomeomorph.isSmoothEmbedding_graph N.coordinate_map_smooth
    N.coordinate_inverse_smooth (RiemannianMetric.lineModelEquiv 2) f hf
      (fun q => ⟨mem_univ q, hdom q⟩)

theorem coordinate_graphs_isotopic (f₀ f₁ : UnitTwoSphere → ℝ)
    (hf₀ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f₀)
    (hf₁ : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f₁)
    (h₀ : ∀ q, f₀ q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (h₁ : ∀ q, f₁ q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹) :
    SmoothSphereIsotopicIn N.carrier
      (range (fun q => N.coordinate_map (q, f₀ q)))
      (range (fun q => N.coordinate_map (q, f₁ q))) := by
  let height := fun (z : ℝ × UnitTwoSphere) => (1 - z.1) * f₀ z.2 + z.1 * f₁ z.2
  have hsmooth : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ height :=
    ((contMDiff_const.sub contMDiff_fst).mul (hf₀.comp contMDiff_snd)).add
      (contMDiff_fst.mul (hf₁.comp contMDiff_snd))
  have hheight (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (q : UnitTwoSphere) :
      height (t, q) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    exact convex_Ioo _ _ (h₀ q) (h₁ q) (sub_nonneg.mpr ht.2) ht.1 (by ring)
  refine ⟨fun z => N.coordinate_map (z.2, height z), ?_, ?_, ?_, ?_⟩
  · exact N.coordinate_map_smooth.comp
      (contMDiff_snd.prodMk hsmooth).contMDiffOn
      (fun z hz => ⟨mem_univ _, hheight z.1 hz.1 z.2⟩)
  · intro t ht
    refine ⟨N.coordinate_graph_isSmoothEmbedding (fun q => height (t, q))
      (((contMDiff_const.sub contMDiff_const).mul hf₀).add
        (contMDiff_const.mul hf₁)) (hheight t ht), ?_⟩
    rintro x ⟨q, rfl⟩
    exact N.coordinate_map_mem ⟨mem_univ _, hheight t ht q⟩
  · simp only [height, sub_zero, one_mul, zero_mul, add_zero]
  · simp only [height, sub_self, zero_mul, one_mul, zero_add]

end PoincareConjecture.EpsilonNeck
