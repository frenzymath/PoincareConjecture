import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Boundary.Finite.TargetChart
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.LGeometry.Basic

/-! The actual regular boundary reference remains regular in the
chosen target chart, in every finite target dimension. Only a local
arc is used, so no Jordan hypothesis is needed.
Source: MT Lemma 19.15, pp. 447-449; M64 finite collar derivation. -/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The actual charted trace is smooth on its open coordinate arc, and its central
derivative is nonzero by the genuine chart inverse. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449; project derivations
`proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md` and
`proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
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

end PoincareMT.M64
