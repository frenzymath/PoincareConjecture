import PoincareConjecture.Proofs.M09.CompactSmoothExtension
import PoincareConjecture.Proofs.M09.SmoothParameterPrimitive








set_option autoImplicit false

open scoped ContDiff Topology intervalIntegral
open Set Filter

namespace PoincareConjecture.Proofs.M09

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem contDiffAt_parameter_primitive (f : E × ℝ → ℝ)
    (U : Set (E × ℝ)) (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U)
    (z0 : E × ℝ) (hsegment : ∀ r ∈ Set.Icc (0 : ℝ) 1, (z0.1, z0.2 * r) ∈ U) :
    ContDiffAt ℝ ∞ (fun z : E × ℝ ↦ ∫ s in 0..z.2, f (z.1, s)) z0 := by
  let K : Set (E × ℝ) := (fun r : ℝ ↦ (z0.1, z0.2 * r)) '' Set.Icc 0 1
  have hK : IsCompact K := isCompact_Icc.image
    (continuous_const.prodMk (continuous_const.mul continuous_id))
  have hKU : K ⊆ U := by
    rintro _ ⟨r, hr, rfl⟩
    exact hsegment r hr
  obtain ⟨g, V, hg, hV, hKV, _, hgf⟩ :=
    exists_smooth_extension_near_compact U K hU hK hKU f hf
  have hnear : ∀ᶠ z : E × ℝ in 𝓝 z0,
      ∀ r ∈ Set.Icc (0 : ℝ) 1, (z.1, z.2 * r) ∈ V := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    have hcont : Continuous (fun w : (E × ℝ) × ℝ ↦ (w.1.1, w.1.2 * w.2)) :=
      continuous_fst.fst.prodMk (continuous_fst.snd.mul continuous_snd)
    exact hcont.continuousAt.preimage_mem_nhds
      (hV.mem_nhds (hKV ⟨r, hr, rfl⟩))
  have heq : (fun z : E × ℝ ↦ ∫ s in 0..z.2, f (z.1, s)) =ᶠ[𝓝 z0]
      (fun z : E × ℝ ↦ ∫ s in 0..z.2, g (z.1, s)) := by
    filter_upwards [hnear] with z hz
    rw [integral_zero_to_eq_scaled (fun s ↦ f (z.1, s)) z.2,
      integral_zero_to_eq_scaled (fun s ↦ g (z.1, s)) z.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Set.Icc (0 : ℝ) 1 := by
      simpa only [Set.uIcc_of_le zero_le_one] using hr
    exact (hgf (hz r hr')).symm
  exact (contDiff_parameter_primitive g hg).contDiffAt.congr_of_eventuallyEq heq

end PoincareConjecture.Proofs.M09
