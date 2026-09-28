import PoincareConjecture.Proofs.M58.Cor18_28_PolarDensity
import PoincareConjecture.Proofs.M58.Cor18_28_PolarIntegration
import PoincareConjecture.Proofs.M58.Cor18_28_PeriodicSpeed
import PoincareConjecture.Proofs.M58.Cor18_28_AreaRegularity










set_option autoImplicit false

open Set MeasureTheory Real Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M58



theorem exists_diskTimeProfile_derivative_bound :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ r ∈ Icc (0 : ℝ) 1, |deriv diskTimeProfile r| ≤ H := by
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (contDiff_diskTimeProfile.continuous_deriv (by simp)).continuousOn
  exact ⟨max H 0, le_max_right _ _, fun r hr => (hH r hr).trans (le_max_left _ _)⟩

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem polar_contraction_area_density_le (g : RiemannianMetric 3 M)
    (C : ℝ × (M × M) → M) (p : M) (γ : C1FreeLoopSpace (M := M))
    {r : ℝ} (hr : 0 < r) (t : ℝ) {A B H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (hF : MDifferentiableAt (𝓡 2) (𝓡 3) (contractionDiskMap C p γ) (r • angularPoint t))
    (hC : MDifferentiableAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
      (diskTimeProfile r, p, periodicFreeLoop γ t))
    (htime : g.tangentNorm (C (diskTimeProfile r, p, periodicFreeLoop γ t))
      (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
        (diskTimeProfile r, p, periodicFreeLoop γ t) (1, 0, 0)) ≤ A)
    (hlast : ∀ v : TangentSpace (𝓡 3) (periodicFreeLoop γ t),
      g.tangentNorm (C (diskTimeProfile r, p, periodicFreeLoop γ t))
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
          (diskTimeProfile r, p, periodicFreeLoop γ t) (0, 0, v)) ≤
            B * g.tangentNorm (periodicFreeLoop γ t) v)
    (hprofile : |deriv diskTimeProfile r| ≤ H) :
    r * parametrizedAreaDensity g (contractionDiskMap C p γ) (r • angularPoint t) ≤
      H * A * B * g.tangentNorm (periodicFreeLoop γ t) (curveVelocity (periodicFreeLoop γ) t) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have h := mul_parametrizedAreaDensity_le_polar g (contractionDiskMap C p γ)
    (r • angularPoint t) hr.le t
  erw [mfderiv_contractionDiskMap_radial C p γ hr t hF hC,
    mfderiv_contractionDiskMap_angular C p γ hr t hF hC,
    contractionDiskMap_polar C p γ hr t] at h
  let D := mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
    (diskTimeProfile r, p, periodicFreeLoop γ t)
  change r * parametrizedAreaDensity g (contractionDiskMap C p γ) (r • angularPoint t) ≤
    ‖deriv diskTimeProfile r • D (1, 0, 0)‖ * ‖D (0, 0, curveVelocity (periodicFreeLoop γ) t)‖ at h
  rw [norm_smul, Real.norm_eq_abs] at h
  calc
    _ ≤ (|deriv diskTimeProfile r| * ‖D (1, 0, 0)‖) *
        ‖D (0, 0, curveVelocity (periodicFreeLoop γ) t)‖ := h
    _ ≤ (H * A) * (B * g.tangentNorm (periodicFreeLoop γ t)
        (curveVelocity (periodicFreeLoop γ) t)) :=
      mul_le_mul (mul_le_mul hprofile htime (norm_nonneg _) hH)
        (hlast _) (norm_nonneg _) (mul_nonneg hH hA)
    _ = _ := by ring



theorem contractionDiskMap_area_le (g : RiemannianMetric 3 M)
    (C : ℝ × (M × M) → M) (p : M) (γ : C1FreeLoopSpace (M := M))
    (hF : ContMDiff (𝓡 2) (𝓡 3) 1 (contractionDiskMap C p γ))
    (hC : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (s, p, periodicFreeLoop γ t))
    {A B H : ℝ} (hA : 0 ≤ A) (hH : 0 ≤ H)
    (htime : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ,
      g.tangentNorm (C (s, p, periodicFreeLoop γ t))
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
          (s, p, periodicFreeLoop γ t) (1, 0, 0)) ≤ A)
    (hlast : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t : ℝ, ∀ v : TangentSpace (𝓡 3) (periodicFreeLoop γ t),
      g.tangentNorm (C (s, p, periodicFreeLoop γ t))
        (mfderiv (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) C
          (s, p, periodicFreeLoop γ t) (0, 0, v)) ≤
            B * g.tangentNorm (periodicFreeLoop γ t) v)
    (hprofile : ∀ r ∈ Icc (0 : ℝ) 1, |deriv diskTimeProfile r| ≤ H) :
    parametrizedRiemannianArea g (contractionDiskMap C p γ) ≤ H * A * B * freeLoopLength g γ := by
  let F := contractionDiskMap C p γ
  let S : Set (ℝ × ℝ) := Ioc (0 : ℝ) 1 ×ˢ Ioo (-π) π
  let K : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-π) π
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hSK : S ⊆ K := prod_mono Ioc_subset_Icc_self Ioo_subset_Icc_self
  have hpolar : Continuous (fun q : ℝ × ℝ =>
      q.1 * parametrizedAreaDensity g F (q.1 • angularPoint q.2)) :=
    continuous_fst.mul ((continuous_parametrizedAreaDensity g hF).comp
      (continuous_fst.smul (contDiff_angularPoint.continuous.comp continuous_snd)))
  have hcomparison : Continuous (fun q : ℝ × ℝ => H * A * B *
      g.tangentNorm (periodicFreeLoop γ q.2) (curveVelocity (periodicFreeLoop γ) q.2)) :=
    continuous_const.mul ((continuous_freeLoopSpeed g γ).comp continuous_snd)
  change (∫ z in loopDiskSet, parametrizedAreaDensity g F z) ≤ _
  rw [integral_loopDisk_polar]
  calc
    _ ≤ ∫ q in S, H * A * B *
        g.tangentNorm (periodicFreeLoop γ q.2) (curveVelocity (periodicFreeLoop γ) q.2) := by
      apply setIntegral_mono_on (hpolar.continuousOn.integrableOn_compact hK |>.mono_set hSK)
        (hcomparison.continuousOn.integrableOn_compact hK |>.mono_set hSK)
        (measurableSet_Ioc.prod measurableSet_Ioo)
      intro q hq
      exact polar_contraction_area_density_le g C p γ hq.1.1 q.2 hA hH
        (hF.mdifferentiableAt one_ne_zero)
        ((hC _ (diskTimeProfile_mem_Icc _) q.2).mdifferentiableAt one_ne_zero)
        (htime _ (diskTimeProfile_mem_Icc _) q.2)
        (hlast _ (diskTimeProfile_mem_Icc _) q.2) (hprofile _ ⟨hq.1.1.le, hq.1.2⟩)
    _ = _ := by
      change (∫ q in Ioc (0 : ℝ) 1 ×ˢ Ioo (-π) π, (fun _ : ℝ => H * A * B) q.1 *
        (fun t => g.tangentNorm (periodicFreeLoop γ t) (curveVelocity (periodicFreeLoop γ) t)) q.2
        ∂volume.prod volume) = _
      rw [setIntegral_prod_mul (fun _ : ℝ => H * A * B)
        (fun t => g.tangentNorm (periodicFreeLoop γ t) (curveVelocity (periodicFreeLoop γ) t))
        (Ioc (0 : ℝ) 1) (Ioo (-π) π), integral_polar_freeLoopSpeed]
      simp

end PoincareConjecture.Proofs.M58
