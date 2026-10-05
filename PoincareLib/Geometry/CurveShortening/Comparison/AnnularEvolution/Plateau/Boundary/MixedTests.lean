import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.DifferenceQuotient
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Boundary.PotentialBound

/-!
# Genuine mixed boundary Sobolev tests

In coordinates straightening a boundary curve, its normal coordinates
have zero trace and its tangent coordinate has a free boundary condition.
This analytic lemma treats those two component test spaces without
assuming differentiability of the boundary parametrization.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

namespace PoincareMT

/-- The genuine scalar equation admits the actual compact H1 test in either the free or
zero-boundary component space. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local
boundary analysis. Project derivation:
`proof-work/tasks/M64/reports/2026-09-25-boundary-zero-tests.md`. -/
theorem m64NaturalGrowth_mixed_boundary_test
    (dirichlet : Prop) {O : Set LoopPlane} (hO : IsOpen O)
    {F du : Fin 2 → LoopPlane → ℝ} {b u : LoopPlane → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hb : Integrable b)
    (hu : Continuous u) (hc : HasCompactSupport u) (hs : tsupport u ⊆ O)
    (hup : MemLp u 2 volume) (hdu : ∀ i, MemLp (du i) 2 volume)
    (hw : ∀ i, HasWeakPartialDeriv i (du i) u univ)
    (hzero : dirichlet → ∀ p : LoopPlane, p 1 < 0 → u p = 0)
    (heq : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O → (dirichlet → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) →
      (∫ p, ∑ i : Fin 2, F i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, b p * phi p) :
    (∫ p, ∑ i : Fin 2, F i p * du i p) = ∫ p, b p * u p := by
  classical
  by_cases hD : dirichlet
  · apply m64NaturalGrowth_zero_boundary_test hO hF hb hu hc hs hup hdu hw (hzero hD)
    intro phi hp hpc hps
    apply heq phi hp hpc (hps.trans inter_subset_left)
    intro _ p hp0
    exact image_eq_zero_of_notMem_tsupport
      (fun hm => by have := (hps hm).2; change 0 < p 1 at this; linarith)
  · apply M60.suNaturalGrowth_weak_test (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      hO hF hb hu hc hs hup hdu hw
    intro phi hp hpc hps
    exact heq phi hp hpc hps (fun h => (hD h).elim)

/-- The mixed equation admits the actual squared-cutoff test with its full weak product
derivative. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449; local boundary analysis.
Project derivation: `proof-work/tasks/M64/reports/2026-09-25-boundary-zero-tests.md`. -/
theorem m64NaturalGrowth_mixed_cutoff_test
    (dirichlet : Prop) {O : Set LoopPlane} (hO : IsOpen O)
    {F du : Fin 2 → LoopPlane → ℝ} {b u xi : LoopPlane → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hb : Integrable b)
    (hu : Continuous u) (hdu : ∀ i, MemLp (du i) 2 volume)
    (hw : ∀ i, HasWeakPartialDeriv i (du i) u univ)
    (hzero : dirichlet → ∀ p : LoopPlane, p 1 < 0 → u p = 0)
    (hxi : ContDiff ℝ ∞ xi) (hc : HasCompactSupport xi) (hs : tsupport xi ⊆ O)
    (heq : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O → (dirichlet → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) →
      (∫ p, ∑ i : Fin 2, F i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, b p * phi p) :
    (∫ p, ∑ i : Fin 2, F i p * (xi p ^ 2 * du i p +
        2 * xi p * fderiv ℝ xi p (EuclideanSpace.single i 1) * u p)) =
      ∫ p, b p * (xi p ^ 2 * u p) := by
  classical
  by_cases hD : dirichlet
  · apply m64NaturalGrowth_boundary_cutoff_test hO hF hb hu hdu hw (hzero hD) hxi hc hs
    intro phi hp hpc hps
    apply heq phi hp hpc (hps.trans inter_subset_left)
    intro _ p hp0
    exact image_eq_zero_of_notMem_tsupport
      (fun hm => by have := (hps hm).2; change 0 < p 1 at this; linarith)
  · apply M60.suNaturalGrowth_cutoff_test (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      hO hF hb hu hdu hw hxi hc hs
    intro phi hp hpc hps
    exact heq phi hp hpc hps (fun h => (hD h).elim)

/-- Tangential differences preserve the actual mixed test conditions and yield the full
Nirenberg identity on a retained support margin. Source: Morgan--Tian (2007), Lemma 19.15,
pp. 447-449; local boundary analysis. Project derivation:
`proof-work/tasks/M64/reports/2026-09-25-boundary-zero-tests.md`. -/
theorem m64NaturalGrowth_mixed_nirenberg_identity
    (dirichlet : Prop) {O : Set LoopPlane} (hO : IsOpen O)
    {F du : Fin 2 → LoopPlane → ℝ} {b u xi : LoopPlane → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hb : Integrable b)
    (hu : Continuous u) (hdu : ∀ i, MemLp (du i) 2 volume)
    (hw : ∀ i, HasWeakPartialDeriv i (du i) u univ)
    (hzero : dirichlet → ∀ p : LoopPlane, p 1 < 0 → u p = 0)
    (hxi : ContDiff ℝ ∞ xi) (hc : HasCompactSupport xi)
    (heq : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O → (dirichlet → ∀ p : LoopPlane, p 1 = 0 → phi p = 0) →
      (∫ p, ∑ i : Fin 2, F i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, b p * phi p)
    {h : ℝ} (hh : h ≠ 0) (hs : cthickening |h| (tsupport xi) ⊆ O) :
    (∫ p, ∑ i : Fin 2, diffQuot 0 h (F i) p *
      (xi p ^ 2 * diffQuot 0 h (du i) p + 2 * xi p *
        fderiv ℝ xi p (EuclideanSpace.single i 1) * diffQuot 0 h u p)) =
      ∫ p, diffQuot 0 h b p * (xi p ^ 2 * diffQuot 0 h u p) := by
  classical
  by_cases hD : dirichlet
  · apply m64NaturalGrowth_boundary_nirenberg_identity hO hF hb hu hdu hw
      (hzero hD) hxi hc ?_ hh hs
    intro phi hp hpc hps
    apply heq phi hp hpc (hps.trans inter_subset_left)
    intro _ p hp0
    exact image_eq_zero_of_notMem_tsupport
      (fun hm => by have := (hps hm).2; change 0 < p 1 at this; linarith)
  · apply M60.suNaturalGrowth_nirenberg_identity (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      hO hF hb hu hdu hw hxi hc ?_ 0 hh hs
    intro phi hp hpc hps
    exact heq phi hp hpc hps (fun h => (hD h).elim)

end PoincareMT
