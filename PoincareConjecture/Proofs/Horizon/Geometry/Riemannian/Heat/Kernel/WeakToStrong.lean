import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Weak
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Energy.VolumeSupport
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric n M}

theorem hasDerivAt_of_smooth_weak_heatEquation
    (D : LeviCivitaData g) {F : ℝ × M → ℝ}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (Ioi 0 ×ˢ univ))
    {t : ℝ} (ht : 0 < t)
    (hweak : ∀ φ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ φ →
      HasCompactSupport φ → HasDerivAt
        (fun r => ∫ x, φ x * F (r, x) ∂g.volumeMeasure)
        (∫ x, F (t, x) * D.laplacian φ x ∂g.volumeMeasure) t) (x : M) :
    HasDerivAt (fun r => F (r, x)) (D.laplacian (fun z => F (t, z)) x) t := by
  have hFt (z : M) : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ F (t, z) :=
    hF.contMDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds ⟨ht, mem_univ z⟩)
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun z => F (t, z)) :=
    fun z => (hFt z).comp z (contMDiffAt_const.prodMk contMDiffAt_id)
  have hd : Continuous (fun z => deriv (fun r => F (r, z)) t) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (Poincare.Manifold.contMDiffAt_deriv_time (hFt z)).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)
  have hl : Continuous (D.laplacian (fun z => F (t, z))) := D.continuous_laplacian hs
  obtain ⟨K⟩ := g.nonempty_compactExhaustion
  let : SigmaCompactSpace M :=
    SigmaCompactSpace_iff_exists_compact_covering.mpr ⟨K, K.isCompact, K.iUnion_eq⟩
  let : g.volumeMeasure.IsOpenPosMeasure := g.volumeMeasure_isOpenPosMeasure
  have hae : (fun z => deriv (fun r => F (r, z)) t) =ᵐ[g.volumeMeasure]
      D.laplacian (fun z => F (t, z)) := by
    apply ae_eq_of_integral_contMDiff_smul_eq (𝓡 n) hd.locallyIntegrable hl.locallyIntegrable
    intro φ hφ hφc
    simp only [smul_eq_mul]
    have heq := (hasDerivAt_integral_test_mul (g := g) hF hφ.continuous hφc ht).unique
      (hweak φ hφ hφc)
    rw [D.integral_mul_laplacian_comm_of_hasCompactSupport_left hφ hs hφc]
    exact heq
  have heq := congrFun (g.volumeMeasure.eq_of_ae_eq hae hd hl) x
  have htime := ((hFt x).comp t (contMDiffAt_id.prodMk contMDiffAt_const)).contDiffAt.differentiableAt
    (by simp)
  exact heq ▸ htime.hasDerivAt

end PoincareConjecture.LeviCivitaData
