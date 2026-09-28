import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Regularity.Lipschitz
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.Busemann.Regularity.Distribution
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Distribution
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.Classical

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

open Dirichlet

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem contMDiff_of_distance_lipschitz_of_weak_harmonic
    (D : LeviCivitaData g) (hn : 0 < n) {f : M → ℝ} (hf : Continuous f)
    (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal)
    (hweak : ∀ ψ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∫ y, f y * D.laplacian ψ y ∂g.volumeMeasure) = 0) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f := by
  intro a
  obtain ⟨r, hr, hball, huL2, p, hp, hpartial⟩ :=
    g.exists_chart_weakPartials_of_distance_lipschitz hLip a
  let e := (chartAt (EuclideanSpace ℝ (Fin n)) a).symm
  let O := Metric.ball (extChartAt (𝓡 n) a a) r
  have hO : IsOpen O := Metric.isOpen_ball
  have hOs : O ⊆ e.source := by
    simpa only [O, e, OpenPartialHomeomorph.symm_source,
      extChartAt_target, modelWithCornersSelf_coe_symm,
      modelWithCornersSelf_coe, preimage_id, range_id, inter_univ] using hball
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := contMDiffOn_chart_symm
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := contMDiffOn_chart
  have hcont : ContinuousOn (fun x => f (e x)) O :=
    hf.comp_continuousOn (e.continuousOn.mono hOs)
  have hsmooth : ContDiffOn ℝ ∞ (fun x => f (e x)) O := by
    refine Poincare.Analysis.Elliptic.contDiffOn_of_continuous_of_adjoint
      hn hO (divergenceCoefficients g e)
      (fun i j => (contDiffOn_divergenceCoefficients e he hei i j).mono hOs)
      ?_ (fun x => f (e x)) hcont p huL2 hp hpartial ?_
    · intro x hx
      apply Matrix.PosDef.of_dotProduct_mulVec_pos
      · ext i j
        exact divergenceCoefficients_symm e he hei (hOs hx) j i
      · intro v hv
        have hv' : (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n)) ≠ 0 := by
          intro hz
          apply hv
          exact congrArg WithLp.ofLp hz
        have hpos := divergenceCoefficients_pos (g := g) e he hei (hOs hx)
          (WithLp.toLp 2 v) hv'
        simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
          Finset.mul_sum, PiLp.toLp_apply, mul_left_comm, mul_comm, mul_assoc] using hpos
    · intro φ hφ hc hs
      exact D.integral_coefficient_divergence_eq_zero_of_weak_harmonic_on
        hf hweak e he hei hOs hφ hc hs
  rw [contMDiffAt_iff_source]
  simpa only [modelWithCornersSelf_coe, range_id, contMDiffWithinAt_univ,
    extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_def, id_eq, e] using
    (hsmooth.contDiffAt (hO.mem_nhds (Metric.mem_ball_self hr))).contMDiffAt

theorem smooth_harmonic_of_distance_lipschitz_of_weak_harmonic
    (D : LeviCivitaData g) (hn : 0 < n) {f : M → ℝ} (hf : Continuous f)
    (hLip : ∀ x y, |f x - f y| ≤ (g.edist x y).toReal)
    (hweak : ∀ ψ : M → ℝ, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ →
      HasCompactSupport ψ → (∫ y, f y * D.laplacian ψ y ∂g.volumeMeasure) = 0) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧ ∀ x, D.laplacian f x = 0 := by
  have hs := D.contMDiff_of_distance_lipschitz_of_weak_harmonic hn hf hLip hweak
  refine ⟨hs, fun x => ?_⟩
  exact laplacian_eq_zero_of_smooth_distributional isOpen_univ hs.contMDiffOn
    (fun ψ => hweak ψ ψ.smooth ψ.hasCompactSupport) x (mem_univ x)

end PoincareConjecture.LeviCivitaData
