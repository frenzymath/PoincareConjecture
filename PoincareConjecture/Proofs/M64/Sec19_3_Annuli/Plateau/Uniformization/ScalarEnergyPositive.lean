import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarNonconstancy
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Calculus.MeanValue














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)






theorem scalarAnnulus_isConnected : IsConnected scalarAnnulus := by
  have hs : IsConnected (Metric.sphere (0 : Plane) 1) :=
    isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 zero_le_one
  have hi : IsConnected (Ioo (1 : ℝ) 2) := isConnected_Ioo (by norm_num)
  have himage := (hs.prod hi).image (fun p : Plane × ℝ => p.2 • p.1)
    (continuous_snd.smul continuous_fst).continuousOn
  have heq : scalarAnnulus = (fun p : Plane × ℝ => p.2 • p.1) ''
      (Metric.sphere (0 : Plane) 1 ×ˢ Ioo (1 : ℝ) 2) := by
    ext x
    simp only [scalarAnnulus, mem_ofPred_eq, mem_image, mem_prod, mem_Ioo, Prod.exists]
    constructor
    · intro hx
      have hxpos : 0 < ‖x‖ := lt_trans zero_lt_one hx.1
      refine ⟨‖x‖⁻¹ • x, ‖x‖, ⟨?_, hx⟩, ?_⟩
      · rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv,
          abs_norm, inv_mul_cancel₀ hxpos.ne']
      · rw [smul_smul, mul_inv_cancel₀ hxpos.ne', one_smul]
    · rintro ⟨s, t, ⟨hs, ht⟩, rfl⟩
      rw [mem_sphere_zero_iff_norm] at hs
      rw [norm_smul, hs, mul_one, Real.norm_eq_abs,
        abs_of_pos (lt_trans zero_lt_one ht.1)]
      exact ht
  rw [heq]
  exact himage

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)







theorem exists_nonzero_annular_gradient {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hnon : ¬ ∃ c : ℝ, EqOn H (fun _ => c) scalarAnnulus) :
    ∃ x ∈ scalarAnnulus, D.gradient H x ≠ 0 := by
  by_contra hnone
  push Not at hnone
  have hdiff : DifferentiableOn ℝ H scalarAnnulus :=
    (contMDiffOn_iff_contDiffOn.mp hHs).differentiableOn (by simp)
  have hzero : EqOn (fderiv ℝ H) 0 scalarAnnulus := by
    intro x hx
    ext v
    have h := D.inner_gradient H x v
    rw [hnone x hx] at h
    have heq : mvfderiv (𝓡 2) H x v = fderiv ℝ H x v := by
      simp [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
      rfl
    rw [heq] at h
    simpa using h.symm
  obtain ⟨c, hc⟩ := scalarAnnulus_isOpen.exists_is_const_of_fderiv_eq_zero
    scalarAnnulus_isConnected.isPreconnected hdiff hzero
  exact hnon ⟨c, hc⟩








theorem exists_positive_local_annular_energy {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hnon : ¬ ∃ c : ℝ, EqOn H (fun _ => c) scalarAnnulus) :
    ∃ χ : EnergyTest D scalarAnnulus,
      (∀ x, 0 ≤ χ x) ∧
      Integrable (fun x => χ x * g.inner x (D.gradient H x) (D.gradient H x))
        g.volumeMeasure ∧
      0 < ∫ x, χ x * g.inner x (D.gradient H x) (D.gradient H x) ∂g.volumeMeasure := by
  obtain ⟨x, hx, hxgrad⟩ := exists_nonzero_annular_gradient D hHs hnon
  obtain ⟨V, hVs, -, -, hVH⟩ := exists_compact_smooth_germ scalarAnnulus_isOpen hHs hx
  have hgrad : (fun y => D.gradient V y) =ᶠ[𝓝 x] (fun y => D.gradient H y) := by
    filter_upwards [hVH.eventually_nhds] with y hy
    simp only [LeviCivitaData.gradient, Poincare.mvfderiv_eq_of_eventuallyEq hy]
  obtain ⟨b, -, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 2) x).mem_iff.mp
    (inter_mem (scalarAnnulus_isOpen.mem_nhds hx) hgrad)
  let χ : EnergyTest D scalarAnnulus :=
    ⟨b, b.contMDiff, b.hasCompactSupport, fun y hy => (hb hy).1⟩
  have hfun : (fun y => χ y * g.inner y (D.gradient H y) (D.gradient H y)) =
      (fun y => b y * g.inner y (D.gradient V y) (D.gradient V y)) := by
    funext y
    change b y * _ = _
    by_cases hy : y ∈ tsupport (b : Plane → ℝ)
    · rw [show D.gradient V y = D.gradient H y from (hb hy).2]
    · simp only [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  have hcontinuous := b.continuous.mul (D.continuous_inner_gradient hVs hVs)
  have hintegrable : Integrable
      (fun y => b y * g.inner y (D.gradient V y) (D.gradient V y)) g.volumeMeasure :=
    hcontinuous.integrable_of_hasCompactSupport b.hasCompactSupport.mul_right
  have hVgrad : D.gradient V x ≠ 0 := by
    rw [show D.gradient V x = D.gradient H x from hgrad.self_of_nhds]
    exact hxgrad
  have hpositive : 0 < ∫ y, b y * g.inner y (D.gradient V y) (D.gradient V y)
      ∂g.volumeMeasure := by
    let : g.volumeMeasure.IsOpenPosMeasure := volumeMeasure_isOpenPosMeasure
    apply integral_pos_of_integrable_nonneg_nonzero hcontinuous hintegrable (x := x)
    · intro y
      apply mul_nonneg b.nonneg
      by_cases hy : D.gradient V y = 0
      · simp [hy]
      · exact (g.pos y _ hy).le
    · simpa only [Pi.mul_apply, b.eq_one, one_mul] using (g.pos x _ hVgrad).ne'
  refine ⟨χ, fun _ => b.nonneg, ?_, ?_⟩
  · rw [hfun]
    exact hintegrable
  · rw [hfun]
    exact hpositive









theorem exists_annular_positive_energy_harmonic_potential :
    ∃ (H : Plane → ℝ) (w : H1Zero D scalarAnnulus) (χ : EnergyTest D scalarAnnulus),
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
        (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
          annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ) ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x, 0 ≤ χ x) ∧
      Integrable (fun x => χ x * g.inner x (D.gradient H x) (D.gradient H x))
        g.volumeMeasure ∧
      0 < ∫ x, χ x * g.inner x (D.gradient H x) (D.gradient H x) ∂g.volumeMeasure := by
  obtain ⟨H, w, hHs, hHae, hHlap, hnon, -⟩ :=
    exists_annular_nonconstant_smooth_harmonic_potential D
  obtain ⟨χ, hχ, hχint, hχpos⟩ := exists_positive_local_annular_energy D hHs hnon
  exact ⟨H, w, χ, hHs, hHae, hHlap, hχ, hχint, hχpos⟩

end PoincareConjecture.M64Uniformization
