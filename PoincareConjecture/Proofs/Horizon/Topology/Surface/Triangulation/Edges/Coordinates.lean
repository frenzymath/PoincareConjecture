import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.Topology.Surface

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem SmoothEdge.contDiffAt_chart_and_deriv_ne_zero (e : SmoothEdge M)
    (p : M) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    (hsource : e.map t ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    ContDiffAt ℝ ∞ ((chartAt (EuclideanSpace ℝ (Fin 2)) p) ∘ e.map) t ∧
      deriv ((chartAt (EuclideanSpace ℝ (Fin 2)) p) ∘ e.map) t ≠ 0 := by
  have he := e.smooth.contMDiffAt (Icc_mem_nhds ht.1 ht.2)
  have hc := (contMDiffOn_chart (I := 𝓡 2) (n := ∞) (x := p)).contMDiffAt
    ((chartAt (EuclideanSpace ℝ (Fin 2)) p).open_source.mem_nhds hsource)
  have hcomp := hc.comp t he
  have hinj : Function.Injective
      (fderiv ℝ ((chartAt (EuclideanSpace ℝ (Fin 2)) p) ∘ e.map) t) := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp t
      (hc.mdifferentiableAt (by simp)) (he.mdifferentiableAt (by simp))]
    exact ((mdifferentiable_chart (I := 𝓡 2) p).mfderiv_injective hsource).comp
      (e.regular t ht)
  refine ⟨hcomp.contDiffAt, ?_⟩
  intro hzero
  apply one_ne_zero (α := ℝ)
  apply hinj
  rw [fderiv_apply_one_eq_deriv, hzero, map_zero]

end PoincareConjecture.Topology.Surface
