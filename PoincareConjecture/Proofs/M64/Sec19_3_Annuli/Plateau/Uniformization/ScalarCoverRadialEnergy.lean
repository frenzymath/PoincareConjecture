import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverDifferentialEnergy













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open Proofs.M58

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ






theorem scalarCoverMap_radial_norm (z : Cover) :
    ‖fderiv ℝ scalarCoverMap z (1, 0)‖ = 1 := by
  have heq : fderiv ℝ scalarCoverMap z (1, 0) = angularPoint (2 * Real.pi * z.2) := by
    rw [scalarCoverMap_radial_column]
    ext i
    fin_cases i <;> simp [angularPoint]
  rw [heq, norm_angularPoint]






theorem scalarCover_radial_derivative_le {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    {z : Cover} (hz : z ∈ scalarCoverStrip) :
    |fderiv ℝ (H ∘ scalarCoverMap) z (1, 0)| ≤ ‖fderiv ℝ H (scalarCoverMap z)‖ := by
  have hHd := (contMDiffAt_iff_contDiffAt.mp
    (hHs.contMDiffAt (scalarAnnulus_isOpen.mem_nhds (scalarCoverMap_mem hz)))).differentiableAt
      (by simp)
  rw [fderiv_comp z hHd (scalarCoverMap_smooth.differentiable (by simp) z)]
  change |fderiv ℝ H (scalarCoverMap z) (fderiv ℝ scalarCoverMap z (1, 0))| ≤ _
  simpa only [scalarCoverMap_radial_norm, mul_one, Real.norm_eq_abs] using
    (fderiv ℝ H (scalarCoverMap z)).le_opNorm (fderiv ℝ scalarCoverMap z (1, 0))






theorem scalarCover_radial_energy_integrable {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus) :
    IntegrableOn (fun z : Cover => (fderiv ℝ (H ∘ scalarCoverMap) z (1, 0)) ^ 2)
      (Ioo (1 : ℝ) 2 ×ˢ Ioo (0 : ℝ) 1) := by
  have hc : ContinuousOn (fun z : Cover => fderiv ℝ (H ∘ scalarCoverMap) z (1, 0))
      scalarCoverStrip :=
    ((scalarCoverPotential_smooth hHs).continuousOn_fderiv_of_isOpen
      scalarCoverStrip_isOpen (by simp)).clm_apply continuousOn_const
  apply (scalarCover_differential_energy_integrable hHs hE).mono_nonneg
    (((hc.pow 2).mono (fun _ hz => hz.1)).aestronglyMeasurable
      (measurableSet_Ioo.prod measurableSet_Ioo)) (ae_of_all _ (fun _ => sq_nonneg _))
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with z hz
  change (fderiv ℝ (H ∘ scalarCoverMap) z (1, 0)) ^ 2 ≤
    ‖fderiv ℝ H (scalarCoverMap z)‖ ^ 2
  simpa only [sq_abs] using
    (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mpr (scalarCover_radial_derivative_le hHs hz.1)







theorem scalarCover_radial_memLp_ae {H : Plane → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      MemLp (fun r : ℝ => fderiv ℝ (H ∘ scalarCoverMap) (r, t) (1, 0)) 2
        (volume.restrict (Ioc (1 : ℝ) 2)) := by
  have hi := scalarCover_radial_energy_integrable hHs hE
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at hi
  filter_upwards [hi.prod_left_ae] with t ht
  have hc : ContinuousOn (fun r : ℝ => fderiv ℝ (H ∘ scalarCoverMap) (r, t) (1, 0))
      (Ioo (1 : ℝ) 2) :=
    (((scalarCoverPotential_smooth hHs).continuousOn_fderiv_of_isOpen
      scalarCoverStrip_isOpen (by simp)).clm_apply continuousOn_const).comp
      (continuous_id.prodMk continuous_const).continuousOn (fun _ hr => hr)
  have hLp := (memLp_two_iff_integrable_sq
    (hc.aestronglyMeasurable measurableSet_Ioo)).mpr ht
  rwa [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (μ := (volume : Measure ℝ)))]







theorem scalarCover_boundary_trace_energy_ae {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1), ∀ r ∈ Ioo (1 : ℝ) 2,
      H (scalarCoverMap (r, t)) ^ 2 ≤ (r - 1) *
        ∫ s in (1 : ℝ)..r, (fderiv ℝ (H ∘ scalarCoverMap) (s, t) (1, 0)) ^ 2 ∧
      (1 - H (scalarCoverMap (r, t))) ^ 2 ≤ (2 - r) *
        ∫ s in r..(2 : ℝ), (fderiv ℝ (H ∘ scalarCoverMap) (s, t) (1, 0)) ^ 2 := by
  filter_upwards [scalarCover_radial_memLp_ae hHs hE] with t hLp
  intro r hr
  exact ⟨scalarCover_inner_trace_energy hHc hHs hinner t hr
      (MemLp.mono_measure
        (Measure.restrict_mono_set volume (Ioc_subset_Ioc le_rfl hr.2.le)) hLp),
    scalarCover_outer_trace_energy hHc hHs houter t hr
      (MemLp.mono_measure
        (Measure.restrict_mono_set volume (Ioc_subset_Ioc hr.1.le le_rfl)) hLp)⟩

end PoincareConjecture.M64Uniformization
