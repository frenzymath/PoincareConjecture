import PoincareConjecture.Proofs.M60.Mathlib.ConformalHarmonicEstimate
import PoincareConjecture.Proofs.M60.Claim18_12_MinimalSphere.PlaneCurvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Intrinsic










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation ConjugateVariation

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}



theorem m60ConformalHarmonicChart_estimate (D : LeviCivitaData g)
    (b : M) {φ : LoopPlane → M} {a : LoopPlane → ℝ} {O : Set LoopPlane}
    {p : LoopPlane} (hO : IsOpen O) (hp : p ∈ O) (d e : LoopPlane)
    (hφ : ContMDiffOn (𝓡 2) (𝓡 n) ∞ φ O)
    (hchart : ∀ q ∈ O, φ q ∈ (extChartAt (𝓡 n) b).source)
    (hharm :
      let c := extChartAt (𝓡 n) b
      let u := c ∘ φ
      let B := g.pullbackCoefficients c.symm
      ∀ q ∈ O,
        covDerivAlong (christoffelBilinear B) u (fun r => fderiv ℝ u r d) d q +
          covDerivAlong (christoffelBilinear B) u (fun r => fderiv ℝ u r e) e q = 0)
    (hdd : ∀ q ∈ O, g.inner (φ q) (mfderiv (𝓡 2) (𝓡 n) φ q d)
      (mfderiv (𝓡 2) (𝓡 n) φ q d) = a q)
    (hee : ∀ q ∈ O, g.inner (φ q) (mfderiv (𝓡 2) (𝓡 n) φ q e)
      (mfderiv (𝓡 2) (𝓡 n) φ q e) = a q)
    (hde : ∀ q ∈ O, g.inner (φ q) (mfderiv (𝓡 2) (𝓡 n) φ q d)
      (mfderiv (𝓡 2) (𝓡 n) φ q e) = 0)
    (ha : 0 < a p) :
    ((fderiv ℝ a p d) ^ 2 + (fderiv ℝ a p e) ^ 2) / a p -
      2 * D.curvatureTensor (φ p) (mfderiv (𝓡 2) (𝓡 n) φ p d)
        (mfderiv (𝓡 2) (𝓡 n) φ p e) (mfderiv (𝓡 2) (𝓡 n) φ p d)
        (mfderiv (𝓡 2) (𝓡 n) φ p e) ≤
      fderiv ℝ (fun q => fderiv ℝ a q d) p d +
        fderiv ℝ (fun q => fderiv ℝ a q e) p e := by
  let c := extChartAt (𝓡 n) b
  let u := c ∘ φ
  let B := g.pullbackCoefficients c.symm
  have hφq (q : LoopPlane) (hq : q ∈ O) : ContMDiffAt (𝓡 2) (𝓡 n) ∞ φ q :=
    hφ.contMDiffAt (hO.mem_nhds hq)
  have hc (q : LoopPlane) (hq : q ∈ O) : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c (φ q) :=
    contMDiffAt_extChartAt' (by simpa only [extChartAt_source] using hchart q hq)
  have hu : ContDiffOn ℝ ∞ u O := by
    intro q hq
    exact (contMDiffAt_iff_contDiffAt.mp ((hc q hq).comp q (hφq q hq))).contDiffWithinAt
  have hdu (q : LoopPlane) (hq : q ∈ O) (v : LoopPlane) :
      fderiv ℝ u q v = mfderiv (𝓡 n) (𝓡 n) c (φ q)
        (mfderiv (𝓡 2) (𝓡 n) φ q v) := by
    have h := mfderiv_comp q ((hc q hq).mdifferentiableAt (by simp))
      ((hφq q hq).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv] at h
    exact congrArg (fun L => L v) h
  have hpair (q : LoopPlane) (hq : q ∈ O) (v w : LoopPlane) :
      B (u q) (fderiv ℝ u q v) (fderiv ℝ u q w) =
        g.inner (φ q) (mfderiv (𝓡 2) (𝓡 n) φ q v) (mfderiv (𝓡 2) (𝓡 n) φ q w) := by
    rw [hdu q hq v, hdu q hq w]
    exact chartCoefficients_apply g b (hchart q hq) _ _
  have hR : B (u p) (coordinateCurvature B (u p) (fderiv ℝ u p d)
      (fderiv ℝ u p e) (fderiv ℝ u p e)) (fderiv ℝ u p d) =
      D.curvatureTensor (φ p) (mfderiv (𝓡 2) (𝓡 n) φ p d)
        (mfderiv (𝓡 2) (𝓡 n) φ p e) (mfderiv (𝓡 2) (𝓡 n) φ p d)
        (mfderiv (𝓡 2) (𝓡 n) φ p e) := by
    rw [hdu p hp d, hdu p hp e]
    erw [coordinateCurvature_in_chart g D b (hchart p hp)]
    exact chartCoefficients_apply g b (hchart p hp) _ _
  have hnonneg (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ B (u p) v v := by
    change 0 ≤ g.inner (c.symm (u p)) (mfderiv (𝓡 n) (𝓡 n) c.symm (u p) v)
      (mfderiv (𝓡 n) (𝓡 n) c.symm (u p) v)
    by_cases hv : mfderiv (𝓡 n) (𝓡 n) c.symm (u p) v = 0
    · rw [hv]
      simp
    · exact (g.pos _ _ hv).le
  have h := M60.christoffel_conformal_harmonic_estimate hO
    (isOpen_extChartAt_target b) hp d e hu (g.contDiffOn_chartCoefficients b)
    (fun q hq => c.map_source (hchart q hq))
    (fun _ _ _ _ => g.symm _ _ _) (fun _ hx => g.isInvertible_chartCoefficients b hx)
    hnonneg hharm
    (fun q hq => (hpair q hq d d).trans (hdd q hq))
    (fun q hq => (hpair q hq e e).trans (hee q hq))
    (fun q hq => (hpair q hq d e).trans (hde q hq)) ha
  rw [hR] at h
  exact h

end PoincareConjecture
