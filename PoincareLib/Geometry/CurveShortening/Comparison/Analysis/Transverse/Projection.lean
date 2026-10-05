import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Coordinate transverse projection and its derivatives

Removing one coordinate is a linear contraction. Its first and second
derivatives commute with the actual smooth map, and its column energy is
exactly the transverse coordinate energy. Source: Heinz 1970, pp. 100-101;
the M64 transverse-conformality derivation for MT Lemma 19.15, pp. 447-449.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set Filter
open scoped ContDiff Topology

namespace PoincareMT

variable {ι : Type*} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι

open Classical in
/-- The actual linear projection away from the selected coordinate.
Source: Heinz pp. 100-101; the M64 transverse-conformality derivation. -/
def m64TransverseProjection (j : ι) : E →L[ℝ] E :=
  ContinuousLinearMap.id ℝ E - (EuclideanSpace.proj j).smulRight (EuclideanSpace.single j 1)

open Classical in
/-- The projection leaves every transverse coordinate unchanged. Source: the M64
transverse-conformality derivation. Source/construction:
proof-work/tasks/M64/derivations/2026-09-26-transverse-conformality.md, Construct the actual
transverse map. -/
theorem m64TransverseProjection_apply (j : ι) (v : E) (i : ι) :
    m64TransverseProjection j v i = if i = j then 0 else v i := by
  classical
  change v i - v j * (EuclideanSpace.single j 1) i = _
  by_cases hij : i = j
  · subst i
    simp only [PiLp.single_apply, ite_true, mul_one, sub_self]
  · simp only [PiLp.single_apply, hij, ite_false, mul_zero, sub_zero]

/-- Removing one coordinate does not increase the Euclidean norm. Source: the M64
transverse-conformality derivation. Source/construction:
proof-work/tasks/M64/derivations/2026-09-26-transverse-conformality.md, Construct the actual
transverse map. -/
theorem m64TransverseProjection_norm (j : ι) (v : E) : ‖m64TransverseProjection j v‖ ≤ ‖v‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
  apply Finset.sum_le_sum
  intro i _
  rw [m64TransverseProjection_apply]
  split_ifs
  · simpa only [zero_pow two_ne_zero] using sq_nonneg (v i)
  · exact le_rfl

open Classical in
/-- The projected column energy is exactly the transverse coordinate sum.
Source: Heinz pp. 100-101; the M64 transverse-conformality derivation. -/
theorem m64TransverseProjection_energy {κ : Type*} [Fintype κ] (j : ι) (V : κ → E) :
    (∑ i : κ, ‖m64TransverseProjection j (V i)‖ ^ 2) =
      ∑ a : ι, if a = j then 0 else ∑ i : κ, (V i a) ^ 2 := by
  classical
  simp_rw [EuclideanSpace.real_norm_sq_eq, m64TransverseProjection_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases haj : a = j
  · simp only [if_pos haj, zero_pow two_ne_zero, Finset.sum_const_zero]
  · simp only [if_neg haj]

/-- The first derivative of the actual projected map. Source: the chain rule in the M64
transverse-conformality derivation. Source/construction:
proof-work/tasks/M64/derivations/2026-09-26-transverse-conformality.md, Construct the actual
transverse map. -/
theorem m64TransverseProjection_fderiv
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (j : ι) {f : X → E} {x : X} (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (m64TransverseProjection j ∘ f) x =
      (m64TransverseProjection j).comp (fderiv ℝ f x) :=
  ((m64TransverseProjection j).hasFDerivAt.comp x hf.hasFDerivAt).fderiv

/-- The second derivative also commutes with the transverse projection. Source: the chain
rule in the M64 transverse-conformality derivation. Source/construction:
proof-work/tasks/M64/derivations/2026-09-26-transverse-conformality.md, Construct the actual
transverse map. -/
theorem m64TransverseProjection_hessian
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (j : ι) {f : X → E} {U : Set X} (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U)
    {x : X} (hx : x ∈ U) (v w : X) :
    fderiv ℝ (fderiv ℝ (m64TransverseProjection j ∘ f)) x v w =
      m64TransverseProjection j (fderiv ℝ (fderiv ℝ f) x v w) := by
  have hnear : fderiv ℝ (m64TransverseProjection j ∘ f) =ᶠ[𝓝 x]
      fun z => (m64TransverseProjection j).comp (fderiv ℝ f z) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact m64TransverseProjection_fderiv j
      ((hf.contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp))
  have hD : DifferentiableAt ℝ (fderiv ℝ f) x :=
    ((hf.fderiv_of_isOpen (m := 1) hU (by norm_num)).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)
  rw [hnear.fderiv_eq]
  have hh := (ContinuousLinearMap.compL ℝ X E E
    (m64TransverseProjection j)).hasFDerivAt.comp x hD.hasFDerivAt
  simpa only [Function.comp_def, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.comp_apply] using
      congrArg (fun A : X →L[ℝ] X →L[ℝ] E => A v w) hh.fderiv

end PoincareMT
