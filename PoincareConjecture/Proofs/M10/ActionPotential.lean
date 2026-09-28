import PoincareConjecture.Proofs.M10.SpacetimeInverse
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false

open Filter Set
open scoped ContDiff Topology

namespace PoincareConjecture.M10

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ X]

theorem potential_contDiffAt_of_action
    {E : X × ℝ → Y} {A : X × ℝ → ℝ}
    {B : Y × ℝ → Y →L[ℝ] Y →L[ℝ] ℝ} {R : Y × ℝ → ℝ} {z₀ : X × ℝ}
    (hE : ContDiffAt ℝ ∞ E z₀) (hA : ContDiffAt ℝ ∞ A z₀)
    (hB : ContDiffAt ℝ ∞ B (E z₀, z₀.2)) (ht : 0 < z₀.2)
    (hcrit : Function.Bijective (fun h : X ↦ fderiv ℝ E z₀ (h, 0)))
    (hidentity : ∀ᶠ z in 𝓝 z₀,
      fderiv ℝ A z (0, 1) = Real.sqrt z.2 *
        (R (E z, z.2) + B (E z, z.2)
          (fderiv ℝ E z (0, 1)) (fderiv ℝ E z (0, 1)))) :
    ContDiffAt ℝ ∞ R (E z₀, z₀.2) := by
  let H : X × ℝ → Y × ℝ := fun z ↦ (E z, z.2)
  let V : X × ℝ → Y := fun z ↦ fderiv ℝ E z (0, 1)
  let Q : X × ℝ → ℝ := fun z ↦
    fderiv ℝ A z (0, 1) / Real.sqrt z.2 - B (H z) (V z) (V z)
  have hH : ContDiffAt ℝ ∞ H z₀ := hE.prodMk contDiffAt_snd
  have hV : ContDiffAt ℝ ∞ V z₀ :=
    (hE.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hDA : ContDiffAt ℝ ∞ (fun z ↦ fderiv ℝ A z (0, 1)) z₀ :=
    (hA.fderiv_right (by simp)).clm_apply contDiffAt_const
  have hQ : ContDiffAt ℝ ∞ Q z₀ :=
    (hDA.div (contDiffAt_snd.sqrt ht.ne') (Real.sqrt_pos.mpr ht).ne').sub
      (((hB.comp z₀ hH).clm_apply hV).clm_apply hV)
  have heq : Q =ᶠ[𝓝 z₀] R ∘ H := by
    filter_upwards [hidentity, continuous_snd.continuousAt (eventually_gt_nhds ht)]
      with z hz hzt
    dsimp only [Q, V, H, Function.comp_apply]
    rw [hz, mul_div_cancel_left₀ _ (Real.sqrt_pos.mpr hzt).ne']
    ring
  obtain ⟨φ, hφ, hzφ, hφsmooth, _⟩ :=
    exists_smooth_endpoint_time_inverse hE (by simp) hcrit
  change ∀ z, φ z = H z at hφ
  have hleft : φ.symm (H z₀) = z₀ := by
    rw [← hφ z₀]
    exact φ.left_inv hzφ
  have htarget : H z₀ ∈ φ.target := by
    rw [← hφ z₀]
    exact φ.map_source hzφ
  have hinv : ContDiffAt ℝ ∞ φ.symm (H z₀) := hφsmooth
  have hcont : Tendsto φ.symm (𝓝 (H z₀)) (𝓝 z₀) := by
    simpa only [ContinuousAt, hleft] using hinv.continuousAt
  have hQ' : ContDiffAt ℝ ∞ (Q ∘ φ.symm) (H z₀) :=
    (hleft.symm ▸ hQ).comp _ hinv
  apply hQ'.congr_of_eventuallyEq
  have heq' : ∀ᶠ w in 𝓝 (H z₀), Q (φ.symm w) = R (H (φ.symm w)) :=
    hcont heq
  filter_upwards [heq', φ.open_target.mem_nhds htarget] with w hw hwφ
  dsimp only [Function.comp_apply]
  rw [hw]
  congr 1
  exact ((hφ (φ.symm w)).symm.trans (φ.right_inv hwφ)).symm

end PoincareConjecture.M10
