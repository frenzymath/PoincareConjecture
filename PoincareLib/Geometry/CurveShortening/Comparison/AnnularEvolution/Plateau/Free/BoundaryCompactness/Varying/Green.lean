import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.AnnulusClass
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Actual varying boundary terms in weak annular compactness

Weak L2 columns and values pass Green's identity to the limit while the
boundary term itself converges. Dominated convergence supplies this term
for almost-everywhere convergent bounded free traces. No fixed-trace
identity is substituted for the varying sequence.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareMT.M64

open Poincare.Analysis.Sobolev.WeakCompactness

/-- Weak linear observations retain an actual converging right-hand side, allowing the
boundary traces to vary with the sequence. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64
derivation `2026-09-25-free-label-compactness.md`. -/
theorem weak_affine_identity_of_tendsto
    {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u v : ℕ → H} {U V : H} (hu : WeakConverges u U) (hv : WeakConverges v V)
    (A B : H →L[ℝ] F) {c : ℕ → F} {c0 : F} (hc : Tendsto c atTop (𝓝 c0))
    (hseq : ∀ j, A (v j) + B (u j) = c j) : A V + B U = c0 := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro L
  have hleft := (hv (L.comp A)).add (hu (L.comp B))
  have hright := (L.continuous.tendsto c0).comp hc
  have heq (j : ℕ) : L (A (v j)) + L (B (u j)) = L (c j) := by
    rw [← map_add, hseq]
  have hright' : Tendsto (fun j => L (A (v j)) + L (B (u j))) atTop (𝓝 (L c0)) := by
    simpa only [heq, Function.comp_def] using hright
  simpa only [ContinuousLinearMap.comp_apply, map_add] using
    tendsto_nhds_unique hleft hright'

variable {m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "nu" => volume.restrict (Icc (0 : ℝ) curvePeriod)

/-- The Green expression for the weak bulk limit equals the genuine limit of its boundary
expressions. Source: Morgan-Tian Lemma 19.15, pp. 447-449; M64 derivation
`2026-09-25-free-label-compactness.md`. -/
theorem annulus_weak_green_of_varying_boundary
    {u v : ℕ → Lp E 2 mu} {U V : Lp E 2 mu}
    (hu : WeakConverges u U) (hv : WeakConverges v V) (i : Fin 2)
    (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi)
    {c : ℕ → E} {c0 : E} (hc : Tendsto c atTop (𝓝 c0))
    (hseq : ∀ j, (∫ p in S, phi p • v j p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • u j p) = c j) :
    (∫ p in S, phi p • V p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) • U p) = c0 := by
  let dphi : LoopPlane → ℝ := fun p => fderiv ℝ phi p (EuclideanSpace.single i 1)
  have hp : MemLp phi 2 mu := by
    apply (memLp_two_iff_integrable_sq hphi.continuous.aestronglyMeasurable).mpr
    exact (hphi.continuous.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  have hdc : Continuous dphi := (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdp : MemLp dphi 2 mu := by
    apply (memLp_two_iff_integrable_sq hdc.aestronglyMeasurable).mpr
    exact (hdc.pow 2).continuousOn.integrableOn_compact
      m64AnnulusDomain_isCompact |>.mono_set interior_subset
  simpa only [testIntegral_apply] using weak_affine_identity_of_tendsto hu hv
    (testIntegral phi hp) (testIntegral dphi hdp) hc
    (fun j => by simpa only [testIntegral_apply] using hseq j)

/-- Actual bounded almost-everywhere convergence of the observed traces implies convergence
of every continuous weighted boundary integral. Source: Morgan-Tian Lemma 19.15, pp.
447-449; M64 derivation `2026-09-25-free-label-compactness.md`. -/
theorem weighted_trace_integral_tendsto
    (u : ℕ → ℝ → E) (v : ℝ → E)
    (hu : ∀ j, AEStronglyMeasurable (u j) nu)
    {R : ℝ} (hbound : ∀ j, ∀ᵐ x ∂nu, ‖u j x‖ ≤ R)
    (hlim : ∀ᵐ x ∂nu, Tendsto (fun j => u j x) atTop (𝓝 (v x)))
    (w : ℝ → ℝ) (hw : Continuous w) :
    Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod, w x • u j x) atTop
      (𝓝 (∫ x in Icc (0 : ℝ) curvePeriod, w x • v x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖w x‖ * R)
  · intro j
    exact hw.aestronglyMeasurable.smul (hu j)
  · exact (hw.norm.mul continuous_const).integrableOn_Icc
  · intro j
    filter_upwards [hbound j] with x hx
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  · filter_upwards [hlim] with x hx
    exact tendsto_const_nhds.smul hx

end PoincareMT.M64
