import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarConjugateCriticalExclusion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ

theorem scalarCoverMap_surjOn : SurjOn scalarCoverMap scalarCoverStrip scalarAnnulus := by
  intro p hp
  have hp0 : 0 < ‖p‖ := zero_lt_one.trans hp.1
  have hunit : ‖‖p‖⁻¹ • p‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hp0.le), inv_mul_cancel₀ hp0.ne']
  obtain ⟨t, -, ht⟩ := Proofs.M58.exists_angularPoint ⟨‖p‖⁻¹ • p, hunit⟩
  refine ⟨(‖p‖, t / (2 * Real.pi)), hp, ?_⟩
  rw [scalarCoverMap_polar_relation, ht, smul_inv_smul₀ hp0.ne']

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarPotential_gradient_ne_zero_on_cover (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} {V : Cover → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ))
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    (hdeck : ∀ z ∈ scalarCoverStrip,
      V (z + (0, 1)) = V z + scalarFluxPeriod D H (3 / 2))
    (hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1)
    {z : Cover} (hz : z ∈ scalarCoverStrip) : D.gradient H (scalarCoverMap z) ≠ 0 := by
  have hP := scalarPotential_fluxPeriod_pos D w hHc hHs hHae hlap hinner houter
    (by norm_num : (3 / 2 : ℝ) ∈ Ioo 1 2)
  have hinj := scalarNormalizedCoverMap_injOn D w hHc hHs hHae hlap hinner houter
    hdV hdeck hrange
  obtain ⟨U, W, hUo, hp, hUA, hWs, hform, hpair⟩ :=
    exists_injective_local_annular_conjugate D hHs hlap hdV hP.ne' hinj hz
  exact scalarPotential_gradient_ne_zero_of_local_conjugate_injective D hHc hHs hlap
    hinner houter hWs hUo hUA hform hpair hp

theorem scalarPotential_gradient_ne_zero (w : H1Zero D scalarAnnulus)
    {H : Plane → ℝ} {V : Cover → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hHae : H =ᵐ[g.volumeMeasure.restrict scalarAnnulus]
      (scalarPotentialL2 D scalarAnnulus annularBoundaryExtension
        annularBoundaryExtension_smooth annularBoundaryExtension_compact w : Plane → ℝ))
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    (hdeck : ∀ z ∈ scalarCoverStrip,
      V (z + (0, 1)) = V z + scalarFluxPeriod D H (3 / 2))
    (hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1)
    {p : Plane} (hp : p ∈ scalarAnnulus) : D.gradient H p ≠ 0 := by
  obtain ⟨z, hz, rfl⟩ := scalarCoverMap_surjOn hp
  exact scalarPotential_gradient_ne_zero_on_cover D w hHc hHs hHae hlap hinner houter
    hdV hdeck hrange hz

theorem exists_noncritical_homeomorphic_annular_cover_conjugate :
    ∃ (H : Plane → ℝ) (V : Cover → ℝ) (P : ℝ),
      Continuous H ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 1 → H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 2 → H x = 1) ∧
      (∀ x ∈ scalarAnnulus, D.gradient H x ≠ 0) ∧
      0 < P ∧ P = scalarFluxPeriod D H (3 / 2) ∧
      ContDiffOn ℝ ∞ V scalarCoverStrip ∧
      (∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z) ∧
      (∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P) ∧
      ∃ hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1,
        IsHomeomorph (scalarNormalizedCover H V P hrange) := by
  obtain ⟨H, w, V, hHc, hHs, hHae, hlap, hinner, houter, hrange, hP, hVs, hdV, hdeck⟩ :=
    exists_positive_period_annular_cover_conjugate D
  exact ⟨H, V, scalarFluxPeriod D H (3 / 2), hHc, hHs, hlap, hinner, houter,
    fun x hx => scalarPotential_gradient_ne_zero D w hHc hHs hHae hlap hinner houter
      hdV hdeck hrange hx,
    hP, rfl, hVs, hdV, hdeck, hrange,
    scalarNormalizedCover_isHomeomorph D w hHc hHs hHae hlap hinner houter hdV hdeck hrange⟩

end PoincareConjecture.M64Uniformization
