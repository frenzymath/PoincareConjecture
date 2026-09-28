import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarLipschitzMollification
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakDerivativeClosure
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.MinimizerWeakAverages
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Lipschitz













set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory ContinuousLinearMap
open scoped Topology ContDiff Convolution NNReal

namespace PoincareConjecture.M64Uniformization

open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)





theorem scalarLipschitz_column_locallyIntegrable {u : Plane → E} {L : ℝ≥0}
    (hu : LipschitzWith L u) (v : Plane) :
    LocallyIntegrable (fun x => fderiv ℝ u x v) volume := by
  apply (continuous_const (y := (L : ℝ) * ‖v‖)).locallyIntegrable.mono
    (measurable_fderiv_apply_const ℝ u v).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  rw [Real.norm_of_nonneg (mul_nonneg L.coe_nonneg (norm_nonneg v))]
  exact ((fderiv ℝ u x).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hu) (norm_nonneg v))





theorem scalarLipschitz_column_weakPartial {u : Plane → E} {L : ℝ≥0}
    (hu : LipschitzWith L u) (i : Fin 2) (b : Fin m) (O : Set Plane) :
    HasWeakPartialDeriv i
      (fun x => (fderiv ℝ u x (EuclideanSpace.single i 1)) b) (fun x => u x b) O := by
  let B : E →L[ℝ] ℝ := EuclideanSpace.proj b
  have hup : LipschitzWith (‖B‖₊ * L) (fun x => u x b) := B.lipschitz.comp hu
  apply m64WeakPartialDeriv_ae_congr EventuallyEq.rfl _
    (hasWeakPartialDeriv_lineDeriv_of_lipschitz hup i)
  filter_upwards [ae_restrict_of_ae (hu.ae_differentiableAt (μ := volume))] with x hx
  have hd := B.hasFDerivAt.comp x hx.hasFDerivAt
  change lineDeriv ℝ (B ∘ u) x (EuclideanSpace.single i 1) =
    B (fderiv ℝ u x (EuclideanSpace.single i 1))
  rw [hd.differentiableAt.lineDeriv_eq_fderiv, hd.fderiv]
  rfl





theorem scalarLipschitz_mollifier_column {u : Plane → E} {L : ℝ≥0}
    (hu : LipschitzWith L u) {r : ℝ} (hr : 0 < r) (x : Plane) (i : Fin 2) :
    fderiv ℝ (mollifierEps hr ⋆[lsmul ℝ ℝ, volume] u) x (EuclideanSpace.single i 1) =
      (mollifierEps hr ⋆[lsmul ℝ ℝ, volume]
        (fun y => fderiv ℝ u y (EuclideanSpace.single i 1))) x := by
  simpa only [Set.indicator_univ] using M60.suWeak_convolution_fderiv
    MeasurableSet.univ (fun b => scalarLipschitz_column_weakPartial hu i b univ)
    (by simpa only [Set.indicator_univ] using hu.continuous.locallyIntegrable)
    (by simpa only [Set.indicator_univ] using
      scalarLipschitz_column_locallyIntegrable hu (EuclideanSpace.single i 1))
    (mollifierEps_smooth hr) (mollifierEps_compactSupport hr) x (subset_univ _)





theorem scalarLipschitz_mollifier_columns_tendsto_ae
    {u : Plane → E} {L : ℝ≥0} (hu : LipschitzWith L u)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (hz : Tendsto r atTop (𝓝 0)) :
    ∀ᵐ x ∂volume, ∀ i : Fin 2,
      Tendsto (fun j => fderiv ℝ (mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] u) x
        (EuclideanSpace.single i 1)) atTop
        (𝓝 (fderiv ℝ u x (EuclideanSpace.single i 1))) := by
  apply ae_all_iff.mpr
  intro i
  have ha := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := fun j => mollifierBumpEps (hr j)) hz
    (Eventually.of_forall fun j => (show r j ≤ 2 * (r j / 2) by linarith))
    (scalarLipschitz_column_locallyIntegrable hu (EuclideanSpace.single i 1))
  filter_upwards [ha] with x hx
  simp_rw [scalarLipschitz_mollifier_column hu]
  exact hx





theorem scalarLipschitz_mollifier_columns_strong
    {u : Plane → E} {L : ℝ≥0} (hu : LipschitzWith L u)
    {r : ℕ → ℝ} (hr : ∀ j, 0 < r j) (hz : Tendsto r atTop (𝓝 0))
    {K : Set Plane} (hK : IsCompact K) (i : Fin 2) :
    Tendsto (fun j => ∫ x in K,
      ‖fderiv ℝ (mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] u) x
        (EuclideanSpace.single i 1) - fderiv ℝ u x (EuclideanSpace.single i 1)‖ ^ 2)
      atTop (𝓝 0) := by
  let F := fun j => mollifierEps (hr j) ⋆[lsmul ℝ ℝ, volume] u
  let e : Plane := EuclideanSpace.single i 1
  have he : ‖e‖ = 1 := by simp [e]
  have hcolumn (f : Plane → E) (hdf : ∀ x, ‖fderiv ℝ f x‖ ≤ (L : ℝ)) (x : Plane) :
      ‖fderiv ℝ f x e‖ ≤ (L : ℝ) := by
    exact ((fderiv ℝ f x).le_opNorm e).trans (by simpa only [he, mul_one] using hdf x)
  have hbound (j : ℕ) (x : Plane) :
      ‖fderiv ℝ (F j) x e - fderiv ℝ u x e‖ ≤ 2 * (L : ℝ) := by
    exact (norm_sub_le _ _).trans (by
      have h0 := hcolumn (F j) (scalarVector_mollifier_derivative_bound hu (hr j)) x
      have h1 := hcolumn u (fun _ => norm_fderiv_le_of_lipschitz ℝ hu) x
      linarith)
  have hlim : Tendsto (fun j => ∫ x in K,
      ‖fderiv ℝ (F j) x e - fderiv ℝ u x e‖ ^ 2) atTop
      (𝓝 (∫ _x in K, (0 : ℝ))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (2 * (L : ℝ)) ^ 2)
    · intro j
      exact (((measurable_fderiv_apply_const ℝ (F j) e).aestronglyMeasurable.sub
        (measurable_fderiv_apply_const ℝ u e).aestronglyMeasurable).norm).pow 2
    · exact continuousOn_const.integrableOn_compact hK
    · intro j
      exact Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hbound j x) 2
    · filter_upwards [ae_restrict_of_ae
        (scalarLipschitz_mollifier_columns_tendsto_ae hu hr hz)] with x hx
      simpa only [F, e, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using
        ((hx i).sub_const (fderiv ℝ u x e)).norm.pow 2
  simpa only [integral_zero] using hlim

end PoincareConjecture.M64Uniformization
