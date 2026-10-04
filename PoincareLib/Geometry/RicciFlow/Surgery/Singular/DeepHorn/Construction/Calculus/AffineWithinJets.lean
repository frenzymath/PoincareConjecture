import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.TangentCone.Prod

/-!
# Spatial restriction of actual within-domain jets

Morgan--Tian Theorem 11.8, printed p. 272, retains the final time of the
geometric limit. These affine chain-rule identities extract spatial jets
there without extending the time domain. Read-only donor declarations are
`ContinuousAffineMap.iteratedFDerivWithin_comp_right` and
`iteratedFDeriv_prod_slice_eq_within` in M34 `Mathlib/AffineWithinJets.lean`.
The proofs below use Mathlib only.
-/

set_option autoImplicit false

open Set
open scoped ContDiff

namespace PoincareMT.M32

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

/-- Affine restriction preserves the actual within-domain derivative arrays;
the endpoint extraction used in Theorem 11.8, printed p. 272. -/
theorem iteratedFDerivWithin_comp_affine
    (g : G →ᴬ[𝕜] E) {f : E → F} {s : Set E} {n : ℕ∞ω}
    (hf : ContDiffOn 𝕜 n f s) (hs : UniqueDiffOn 𝕜 s)
    (hpre : UniqueDiffOn 𝕜 (g ⁻¹' s)) {x : G} (hx : g x ∈ s)
    {i : ℕ} (hi : i ≤ n) :
    iteratedFDerivWithin 𝕜 i (f ∘ g) (g ⁻¹' s) x =
      (iteratedFDerivWithin 𝕜 i f s (g x)).compContinuousLinearMap
        (fun _ => g.contLinear) :=
  (((hf.of_le hi).ftaylorSeriesWithin hs).comp_continuousAffineMap g
    |>.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl hpre hx).symm

/-- A spatial slice uses the joint jet in spatial directions, including a
boundary value of the parameter; Theorem 11.8, printed p. 272. -/
theorem iteratedFDeriv_prod_slice_eq_within
    {f : G × E → F} {J : Set G} {U : Set E} {n : ℕ∞ω}
    (hf : ContDiffOn 𝕜 n f (J ×ˢ U)) (hJ : UniqueDiffOn 𝕜 J) (hU : IsOpen U)
    {t : G} (ht : t ∈ J) {x : E} (hx : x ∈ U) {i : ℕ} (hi : i ≤ n) :
    iteratedFDeriv 𝕜 i (fun y => f (t, y)) x =
      (iteratedFDerivWithin 𝕜 i f (J ×ˢ U) (t, x)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inr 𝕜 G E) := by
  let g : E →ᴬ[𝕜] G × E :=
    (ContinuousAffineMap.const 𝕜 E t).prod (ContinuousAffineMap.id 𝕜 E)
  have hpre : g ⁻¹' (J ×ˢ U) = U := by
    ext y
    simp [g, ht]
  have hlinear : g.contLinear = ContinuousLinearMap.inr 𝕜 G E := by
    ext v <;> rfl
  have hpre_diff : UniqueDiffOn 𝕜 (g ⁻¹' (J ×ˢ U)) := by
    rw [hpre]
    exact hU.uniqueDiffOn
  have h := iteratedFDerivWithin_comp_affine g hf (hJ.prod hU.uniqueDiffOn)
    hpre_diff (show g x ∈ J ×ˢ U from ⟨ht, hx⟩) hi
  rw [hpre, iteratedFDerivWithin_of_isOpen i hU hx, hlinear] at h
  exact h

end PoincareMT.M32
