import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverJacobian

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem scalar_interval_integral_sq_le {d : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hd : MemLp d 2 (volume.restrict (Ioc a b))) :
    (∫ t in a..b, d t) ^ 2 ≤ (b - a) * ∫ t in a..b, (d t) ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (Ioc a b)) := ⟨by simp⟩
  have hdi : IntegrableOn d (Ioc a b) := hd.integrable (by norm_num)
  have hd2 : IntegrableOn (fun t => (d t) ^ 2) (Ioc a b) := hd.integrable_sq
  let L := b - a
  let J := ∫ t in Ioc a b, d t
  have hL : 0 < L := sub_pos.mpr hab
  have hconst : IntegrableOn (fun _ : ℝ => J ^ 2) (Ioc a b) := integrable_const _
  have hnon : 0 ≤ ∫ t in Ioc a b, (L * d t - J) ^ 2 :=
    integral_nonneg (fun _ => sq_nonneg _)
  have hfun : (fun t : ℝ => (L * d t - J) ^ 2) =
      (fun t => L ^ 2 * (d t) ^ 2 - (2 * L * J) * d t + J ^ 2) := by
    funext t
    ring
  rw [hfun] at hnon
  erw [integral_add ((hd2.const_mul (L ^ 2)).sub (hdi.const_mul (2 * L * J))) hconst,
    integral_sub (hd2.const_mul (L ^ 2)) (hdi.const_mul (2 * L * J)), integral_const_mul,
    integral_const_mul, setIntegral_const, Real.volume_real_Ioc_of_le hab.le,
    smul_eq_mul] at hnon
  have hproduct : 0 ≤ L * (L * (∫ t in Ioc a b, (d t) ^ 2) - J ^ 2) := by
    dsimp only [J, L] at hnon ⊢
    nlinarith
  have hbound := nonneg_of_mul_nonneg_right hproduct hL
  rw [intervalIntegral.integral_of_le hab.le, intervalIntegral.integral_of_le hab.le]
  exact sub_nonneg.mp hbound

theorem scalar_boundary_trace_energy {f d : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt f (d t) t)
    (hLp : MemLp d 2 (volume.restrict (Ioc a b))) :
    (f b - f a) ^ 2 ≤ (b - a) * ∫ t in a..b, (d t) ^ 2 := by
  let : IsFiniteMeasure (volume.restrict (Ioc a b)) := ⟨by simp⟩
  have hi : IntervalIntegrable d volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab.le).mpr (hLp.integrable (by norm_num))
  rw [← intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hc hd hi]
  exact scalar_interval_integral_sq_le hab hLp

theorem scalarCover_inner_trace_energy {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (t : ℝ) {r : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2)
    (hLp : MemLp (fun s => fderiv ℝ (H ∘ scalarCoverMap) (s, t) (1, 0)) 2
      (volume.restrict (Ioc 1 r))) :
    H (scalarCoverMap (r, t)) ^ 2 ≤ (r - 1) *
      ∫ s in (1 : ℝ)..r, (fderiv ℝ (H ∘ scalarCoverMap) (s, t) (1, 0)) ^ 2 := by
  have hs := scalarCoverPotential_smooth hHs
  have hd (s : ℝ) (hsr : s ∈ Ioo (1 : ℝ) r) :
      HasDerivAt (fun a : ℝ => H (scalarCoverMap (a, t)))
        (fderiv ℝ (H ∘ scalarCoverMap) (s, t) (1, 0)) s := by
    have hz : (s, t) ∈ scalarCoverStrip := ⟨hsr.1, hsr.2.trans hr.2⟩
    have h := ((hs.contDiffAt (scalarCoverStrip_isOpen.mem_nhds hz)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))
    simpa only [Function.comp_def, id_eq] using! h
  have hc : Continuous (fun a : ℝ => H (scalarCoverMap (a, t))) :=
    hHc.comp (scalarCoverMap_smooth.continuous.comp (continuous_id.prodMk continuous_const))
  have h := scalar_boundary_trace_energy hr.1 hc.continuousOn hd hLp
  have hzero : H (scalarCoverMap (1, t)) = 0 := hinner _ (by
    change ‖scalarCirclePoint 1 t‖ = 1
    rw [scalarCirclePoint_norm, abs_one])
  simpa only [hzero, sub_zero] using h

theorem scalarCover_outer_trace_energy {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (t : ℝ) {r : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2)
    (hLp : MemLp (fun s => fderiv ℝ (H ∘ scalarCoverMap) (s, t) (1, 0)) 2
      (volume.restrict (Ioc r 2))) :
    (1 - H (scalarCoverMap (r, t))) ^ 2 ≤ (2 - r) *
      ∫ s in r..(2 : ℝ), (fderiv ℝ (H ∘ scalarCoverMap) (s, t) (1, 0)) ^ 2 := by
  have hs := scalarCoverPotential_smooth hHs
  have hd (s : ℝ) (hsr : s ∈ Ioo r (2 : ℝ)) :
      HasDerivAt (fun a : ℝ => H (scalarCoverMap (a, t)))
        (fderiv ℝ (H ∘ scalarCoverMap) (s, t) (1, 0)) s := by
    have hz : (s, t) ∈ scalarCoverStrip := ⟨hr.1.trans hsr.1, hsr.2⟩
    have h := ((hs.contDiffAt (scalarCoverStrip_isOpen.mem_nhds hz)).differentiableAt
      (by simp)).hasFDerivAt.comp_hasDerivAt s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))
    simpa only [Function.comp_def, id_eq] using! h
  have hc : Continuous (fun a : ℝ => H (scalarCoverMap (a, t))) :=
    hHc.comp (scalarCoverMap_smooth.continuous.comp (continuous_id.prodMk continuous_const))
  have h := scalar_boundary_trace_energy hr.2 hc.continuousOn hd hLp
  have hone : H (scalarCoverMap (2, t)) = 1 := houter _ (by
    change ‖scalarCirclePoint 2 t‖ = 2
    rw [scalarCirclePoint_norm]
    norm_num)
  simpa only [hone] using h

end PoincareConjecture.M64Uniformization
