import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.FiniteTargetChart
import PoincareConjecture.Definitions.Ch06.LGeometry






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]






theorem regular_trace_in_chart {c : ℝ → M}
    (hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ c) (p : M) {s : ℝ}
    (hs : c s ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source)
    (hv : curveVelocity (n := n) c s ≠ 0) :
    let q := chartAt (EuclideanSpace ℝ (Fin n)) p
    let I := c ⁻¹' q.source
    IsOpen I ∧ s ∈ I ∧ ContDiffOn ℝ ∞ (q ∘ c) I ∧ deriv (q ∘ c) s ≠ 0 := by
  let q := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hI : IsOpen (c ⁻¹' q.source) := q.open_source.preimage hc.continuous
  have hchart : ContDiffOn ℝ ∞ (q ∘ c) (c ⁻¹' q.source) :=
    (contMDiffOn_chart.comp hc.contMDiffOn (fun _ ht => ht)).contDiffOn
  refine ⟨hI, hs, hchart, ?_⟩
  have hqd := (mdifferentiable_chart (I := 𝓡 n) p).mdifferentiableAt hs
  have hcd := (hc s).mdifferentiableAt (by simp)
  have hchain := congrArg (fun T : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => T 1)
    (mfderiv_comp s hqd hcd)
  have hder : deriv (q ∘ c) s = mfderiv (𝓡 n) (𝓡 n) q (c s) (curveVelocity c s) := by
    simpa +instances only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply,
      fderiv_apply_one_eq_deriv, curveVelocity, q] using! hchain
  intro hz
  apply hv
  apply ((mdifferentiable_chart (I := 𝓡 n) p).mfderiv hs).injective
  change mfderiv (𝓡 n) (𝓡 n) q (c s) (curveVelocity c s) =
    mfderiv (𝓡 n) (𝓡 n) q (c s) 0
  rw [← hder, hz, map_zero]

end PoincareConjecture.M64
