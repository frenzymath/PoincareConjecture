import PoincareConjecture.Proofs.M65.Sec19_5_Limits.AreaContinuity.ContractionJacobian
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.AreaContinuity.DiagonalAnnulus

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture

open Proofs.M58

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

theorem m65Eventually_smallC1Annulus (g : RiemannianMetric 3 M)
    (compact : IsCompact (univ : Set M)) (gamma : C1FreeLoopSpace (M := M))
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ eta in 𝓝 gamma,
      ∃ A : M64Annulus g (periodicFreeLoop gamma) (periodicFreeLoop eta),
        ContMDiff (𝓡 2) (𝓡 3) 1 A.map ∧ A.area < epsilon := by
  obtain ⟨C, U, hU, hdiagU, h0, h1, hdiag, hC⟩ :=
    exists_local_contraction (𝓡 3) compact 1
  let S : Set (C1FreeLoopSpace (M := M)) := {eta | ∀ z : LoopCircle, (eta z, gamma z) ∈ U}
  have hgamma : gamma ∈ S := fun z => hdiagU (by rfl : (gamma z, gamma z) ∈ diagonal M)
  have hpair : Continuous (fun q : C1FreeLoopSpace (M := M) × LoopCircle =>
      (q.1 q.2, gamma q.2)) :=
    continuous_loop_eval.prodMk (gamma.continuous.comp continuous_snd)
  have hS : S ∈ 𝓝 gamma := by
    have hcircle : IsCompact (univ : Set LoopCircle) := isCompact_univ
    have h := hcircle.eventually_forall_of_forall_eventually
      (x₀ := gamma) (P := fun eta z => (eta z, gamma z) ∈ U)
        (fun z _ => hpair.continuousAt.preimage_mem_nhds
          (hU.mem_nhds (hdiagU (by rfl : (gamma z, gamma z) ∈ diagonal M))))
    filter_upwards [h] with eta heta
    exact fun z => heta z (mem_univ z)
  have hangle (eta : S) (x : ℝ) :
      (periodicFreeLoop eta.val x, periodicFreeLoop gamma x) ∈ U := by
    have he : periodicFreeLoop eta.val x = eta.val ⟨angularPoint x, norm_angularPoint x⟩ :=
      eta.val.boundary ⟨angularPoint x, norm_angularPoint x⟩
    have hg : periodicFreeLoop gamma x = gamma ⟨angularPoint x, norm_angularPoint x⟩ :=
      gamma.boundary ⟨angularPoint x, norm_angularPoint x⟩
    rw [he, hg]
    exact eta.property _
  have hregular (eta : S) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (x : ℝ) :
      ContMDiffAt (𝓘(ℝ, ℝ).prod ((𝓡 3).prod (𝓡 3))) (𝓡 3) 1 C
        (s, periodicFreeLoop eta.val x, periodicFreeLoop gamma x) :=
    hC _ ⟨hs, hangle eta x⟩
  have hdensity := m65ContractionAnnulusMap_continuous_density g C
    (fun _ : S => gamma) (fun eta : S => eta.val) continuous_const continuous_subtype_val
    (fun q => hregular q.1 _ ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩ _)
  let V : ℝ := volume.real m64AnnulusDomain
  let delta : ℝ := epsilon / (V + 1)
  have hV : 0 ≤ V := measureReal_nonneg
  have hV1 : 0 < V + 1 := by linarith
  have hdelta : 0 < delta := div_pos hepsilon hV1
  have hsmall : ∀ᶠ eta : S in 𝓝 (⟨gamma, hgamma⟩ : S),
      ∀ p ∈ m64AnnulusDomain,
        m60AreaDensity g (m65ContractionAnnulusMap C gamma eta.val) p < delta := by
    apply m65AnnulusDomain_isCompact.eventually_forall_of_forall_eventually
    intro p _
    apply (isOpen_lt hdensity continuous_const).mem_nhds
    change m60AreaDensity g (m65ContractionAnnulusMap C gamma gamma) p < delta
    rw [m65ContractionAnnulusMap_diagonal_density g C hdiag]
    exact hdelta
  have hresult : ∀ᶠ eta : S in 𝓝 (⟨gamma, hgamma⟩ : S),
      ∃ A : M64Annulus g (periodicFreeLoop gamma) (periodicFreeLoop eta.val),
        ContMDiff (𝓡 2) (𝓡 3) 1 A.map ∧ A.area < epsilon := by
    filter_upwards [hsmall] with eta heta
    let f := m65ContractionAnnulusMap C gamma eta.val
    have hf := m65ContractionAnnulusMap_contMDiff C gamma eta.val (hregular eta)
    let A := m65AnnulusOfContMDiff g f hf
      (m65ContractionAnnulusMap_periodic C gamma eta.val)
      (m65ContractionAnnulusMap_lower C h0 gamma eta.val)
      (m65ContractionAnnulusMap_upper C gamma eta.val (fun x => h1 _ (hangle eta x)))
    refine ⟨A, hf, ?_⟩
    have hnorm : ‖A.area‖ ≤ delta * V := by
      apply norm_setIntegral_le_of_norm_le_const m65AnnulusDomain_isCompact.measure_lt_top
      intro p hp
      rw [Real.norm_eq_abs, abs_of_nonneg
        (show 0 ≤ m60AreaDensity g A.map p from Real.sqrt_nonneg _)]
      exact (heta p hp).le
    have hbound : A.area ≤ delta * V := (le_abs_self _).trans hnorm
    have hbudget : delta * (V + 1) = epsilon := div_mul_cancel₀ epsilon hV1.ne'
    exact hbound.trans_lt (by nlinarith)
  rw [← map_nhds_subtype_coe_eq_nhds hgamma hS]
  exact hresult

end PoincareConjecture
