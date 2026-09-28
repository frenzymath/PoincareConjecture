import PoincareConjecture.Proofs.M14.Sec6_7_ExponentialGramHessian
import PoincareConjecture.Proofs.M14.Sec6_7_ExponentialGramPath
import Mathlib.Analysis.Calculus.Deriv.Pi











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Matrix.Norms.Elementwise

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem ricci_hessian_pair_heq {q r : G.Point} (h : q = r) {τ : ℝ}
    (hq : G.spacetime.timeFunction q = T - τ) (hr : G.spacetime.timeFunction r = T - τ)
    (f : G.Point → ℝ) {U : G.Horizontal q} {V : G.Horizontal r} (hV : HEq U V) :
    horizontalRicci G.leafwise q U U + M14ReducedLengthHessianPairing G ⟨q, hq⟩ f U U =
      horizontalRicci G.leafwise r V V + M14ReducedLengthHessianPairing G ⟨r, hr⟩ f V V := by
  cases h
  cases hV
  rfl




theorem exponentialGram_diagonal_hasDerivWithinAt
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (v : Fin n → G.Horizontal x)
    {Z : G.Horizontal x} {s : ℝ} (hs : (Z, s) ∈ E.domain) (hpos : 0 < s)
    (hz : (Z, s) ∈ M14JointDomain G E) (i : Fin n) :
    HasDerivWithinAt (fun r => exponentialGram E v Z r i i)
      (4 * s * (horizontalRicci G.leafwise (E.gamma Z s)
          (E.differential Z s hs (v i)) (E.differential Z s hs (v i)) +
        M14ReducedLengthHessianPairing G ⟨E.gamma Z s, E.clock Z s hs⟩
          (M14ReducedLengthAt G T 0 x)
          (E.differential Z s hs (v i)) (E.differential Z s hs (v i))))
      (M14SqrtParameterInterval 0 (s ^ 2)) s := by
  let R := E.square_path Z s hs hpos
  let Q : M14JacobiFieldData G R.curve (M14SqrtParameterInterval 0 (s ^ 2)) :=
    initialValuePath_differentialData hM04 hM12
      (exponentialInitialValuePath E Z s hs hpos) (v i)
  have hsC : s ∈ M14SqrtParameterInterval 0 (s ^ 2) := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le] using
      (show s ∈ Icc 0 s from ⟨hpos.le, le_rfl⟩)
  have hpoint := exponential_square_curve_eq E Z hs hpos hsC
  have hq := R.curve_time s hsC
  have hd := squareRoot_covariantDerivative_metric_product R Q.extension Q.extension hsC
  change HasDerivWithinAt
    (fun r => G.spacetime.horizontalMetric.inner (R.curve r) (Q.field r) (Q.field r))
    (G.spacetime.horizontalMetric.inner (R.curve s) (M14JacobiFirstDerivative Q s) (Q.field s) +
      G.spacetime.horizontalMetric.inner (R.curve s) (Q.field s) (M14JacobiFirstDerivative Q s) +
      4 * s * horizontalRicci G.leafwise (R.curve s) (Q.field s) (Q.field s)) _ s at hd
  rw [G.spacetime.horizontalMetric.symm (R.curve s) (Q.field s)] at hd
  have hh := exponentialJacobi_boundary_eq_hessian hCoordinates hM04 hM12 E
    hs hpos hz hpoint hq (v i)
  change G.spacetime.horizontalMetric.inner (R.curve s)
    (M14JacobiFirstDerivative Q s) (Q.field s) = _ at hh
  rw [hh] at hd
  have hd' : HasDerivWithinAt
      (fun r => G.spacetime.horizontalMetric.inner (R.curve r) (Q.field r) (Q.field r))
      (4 * s * (horizontalRicci G.leafwise (R.curve s) (Q.field s) (Q.field s) +
        M14ReducedLengthHessianPairing G ⟨R.curve s, hq⟩ (M14ReducedLengthAt G T 0 x)
          (Q.field s) (Q.field s))) (M14SqrtParameterInterval 0 (s ^ 2)) s := by
    convert hd using 1
    ring
  rw [ricci_hessian_pair_heq hpoint hq (E.clock Z s hs) (M14ReducedLengthAt G T 0 x)
    (exponentialJacobiField_heq_differential hM04 hM12 E Z (v i) hs hpos hsC hs)] at hd'
  exact hd'.congr_of_mem
    (fun r hr => exponentialGram_eq_jacobi_pair hM04 hM12 E v hs hpos hr i i) hsC




theorem exponentialGram_hasDerivAt
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (v : Fin n → G.Horizontal x)
    {Z : G.Horizontal x} {s b : ℝ} (hb : (Z, b) ∈ E.domain)
    (hs : (Z, s) ∈ E.domain) (hpos : 0 < s) (hlt : s < b)
    (hz : (Z, s) ∈ M14JointDomain G E) :
    ∃ B : Matrix (Fin n) (Fin n) ℝ,
      HasDerivAt (exponentialGram E v Z) B s ∧ ∀ i, B i i =
        4 * s * (horizontalRicci G.leafwise (E.gamma Z s)
            (E.differential Z s hs (v i)) (E.differential Z s hs (v i)) +
          M14ReducedLengthHessianPairing G ⟨E.gamma Z s, E.clock Z s hs⟩
            (M14ReducedLengthAt G T 0 x)
            (E.differential Z s hs (v i)) (E.differential Z s hs (v i))) := by
  have hsm := (exponentialGram_contDiffOn hM04 hM12 E v hb (hpos.trans hlt)).contDiffAt
    (Icc_mem_nhds hpos hlt)
  have hd := (hsm.differentiableAt (by simp)).hasDerivAt
  refine ⟨deriv (exponentialGram E v Z) s, hd, ?_⟩
  intro i
  have hdi := hasDerivAt_pi.mp (hasDerivAt_pi.mp hd i) i
  have hwithin := exponentialGram_diagonal_hasDerivWithinAt hCoordinates hM04 hM12 E
    v hs hpos hz i
  have hC : UniqueDiffWithinAt ℝ (M14SqrtParameterInterval 0 (s ^ 2)) s := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hpos.le] using
      (uniqueDiffOn_Icc hpos s ⟨hpos.le, le_rfl⟩)
  exact (hdi.hasDerivWithinAt.derivWithin hC).symm.trans (hwithin.derivWithin hC)

end PoincareConjecture.M14
