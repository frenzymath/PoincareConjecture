import PoincareConjecture.Proofs.M09.SmoothSquarePath
import PoincareConjecture.Proofs.M09.LocalSmoothPrimitive

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology intervalIntegral
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem contDiffAt_smoothSquareFamily_action {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (f : E × ℝ → M) (U : Set (E × ℝ)) (hU : IsOpen U)
    (hf : ContMDiffOn (𝓘(ℝ, E × ℝ)) (𝓡 n) ∞ f U)
    (z0 : E × ℝ) (hz0 : z0.2 ∈ Set.Ioo 0 τmax)
    (hsegment : ∀ r ∈ Set.Icc (0 : ℝ) 1, (z0.1, Real.sqrt z0.2 * r) ∈ U) :
    ContDiffAt ℝ ∞
      (fun z : E × ℝ ↦ backwardLLength F T 0 z.2 (fun τ ↦ f (z.1, Real.sqrt τ))) z0 := by
  let W := U ∩ (Set.univ ×ˢ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax))
  let H := squareFamilyActionDensity F T f
  have hW : IsOpen W := hU.inter (isOpen_univ.prod isOpen_Ioo)
  have hH : ContDiffOn ℝ ∞ H W := squareFamilyActionDensity_contDiffOn F hM04 T τmax
    hτmax hwindow f W hW (hf.mono Set.inter_subset_left) (fun z hz ↦ hz.2.2)
  have hseg : ∀ r ∈ Set.Icc (0 : ℝ) 1, (z0.1, Real.sqrt z0.2 * r) ∈ W := by
    intro r hr
    have h0 : 0 ≤ Real.sqrt z0.2 * r := mul_nonneg (Real.sqrt_nonneg _) hr.1
    have hlt : Real.sqrt z0.2 * r < Real.sqrt τmax :=
      (mul_le_of_le_one_right (Real.sqrt_nonneg _) hr.2).trans_lt
        (Real.sqrt_lt_sqrt hz0.1.le hz0.2)
    exact ⟨hsegment r hr, Set.mem_univ _,
      (neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le h0, hlt⟩
  have hnear : ∀ᶠ z : E × ℝ in 𝓝 z0,
      ∀ r ∈ Set.Icc (0 : ℝ) 1, (z.1, Real.sqrt z.2 * r) ∈ W := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro r hr
    have hc : Continuous (fun w : (E × ℝ) × ℝ ↦
        (w.1.1, Real.sqrt w.1.2 * w.2)) :=
      continuous_fst.fst.prodMk ((Real.continuous_sqrt.comp continuous_fst.snd).mul continuous_snd)
    exact hc.continuousAt.preimage_mem_nhds (hW.mem_nhds (hseg r hr))
  have heq : (fun z : E × ℝ ↦ backwardLLength F T 0 z.2 (fun τ ↦ f (z.1, Real.sqrt τ)))
      =ᶠ[𝓝 z0] (fun z : E × ℝ ↦ ∫ s in 0..Real.sqrt z.2, H (z.1, s)) := by
    filter_upwards [hnear, (isOpen_univ.prod isOpen_Ioo).mem_nhds
      (show z0 ∈ Set.univ ×ˢ Set.Ioo 0 τmax from ⟨Set.mem_univ _, hz0⟩)] with z hsegz hz
    apply backwardLLength_comp_sqrt_eq F T z.2 hz.2.1 (fun s ↦ f (z.1, s))
    intro s hs
    have hpos : 0 < Real.sqrt z.2 := Real.sqrt_pos.mpr hz.2.1
    have hr : s / Real.sqrt z.2 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hs.1.le hpos.le, (div_le_one hpos).mpr hs.2.le⟩
    have hmem : (z.1, s) ∈ U := by
      have hm := (hsegz (s / Real.sqrt z.2) hr).1
      simpa only [mul_div_cancel₀ s hpos.ne'] using hm
    have hi : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, E × ℝ)) ∞ (fun r : ℝ ↦ (z.1, r)) :=
      (contDiff_const.prodMk contDiff_id).contMDiff
    exact ((hf.contMDiffAt (hU.mem_nhds hmem)).comp s hi.contMDiffAt).mdifferentiableAt (by simp)
  have hp : ContDiffAt ℝ ∞ (fun z : E × ℝ ↦ ∫ s in 0..z.2, H (z.1, s))
      (z0.1, Real.sqrt z0.2) :=
    contDiffAt_parameter_primitive H W hW hH (z0.1, Real.sqrt z0.2) hseg
  have hsqrt : ContDiffAt ℝ ∞ (fun z : E × ℝ ↦ (z.1, Real.sqrt z.2)) z0 :=
    contDiffAt_fst.prodMk (contDiffAt_snd.sqrt hz0.1.ne')
  have hsmooth : ContDiffAt ℝ ∞
      (fun z : E × ℝ ↦ ∫ s in 0..Real.sqrt z.2, H (z.1, s)) z0 :=
    ContDiffAt.comp (g := fun z : E × ℝ ↦ ∫ s in 0..z.2, H (z.1, s)) z0 hp hsqrt
  exact hsmooth.congr_of_eventuallyEq heq

end PoincareConjecture.Proofs.M09
