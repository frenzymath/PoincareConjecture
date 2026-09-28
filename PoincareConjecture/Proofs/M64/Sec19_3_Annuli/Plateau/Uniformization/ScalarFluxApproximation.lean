import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFluxTraceBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)

theorem scalarCover_exists_boundary_flux_approximation {H : Plane → ℝ}
    (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {epsilon delta : ℝ} (hepsilon : 0 < epsilon) (hdelta : 0 < delta) :
    (∃ r ∈ Ioo (1 : ℝ) 2, r - 1 < delta ∧
      |scalarCoverWeightedFlux D H r| < epsilon) ∧
    (∃ r ∈ Ioo (1 : ℝ) 2, 2 - r < delta ∧
      |scalarFluxPeriod D H r - scalarCoverWeightedFlux D H r| < epsilon) := by
  obtain ⟨C, -, hbound⟩ := scalarCover_boundary_flux_sq_bound D hHc hHs hlap hE hinner houter
  let K := C ^ 2 * scalarCoverRadialTotalEnergy H
  have hK : 0 ≤ K := mul_nonneg (sq_nonneg _) (integral_nonneg (fun _ => sq_nonneg _))
  have hK1 : 0 < K + 1 := by linarith
  have heta : 0 < epsilon ^ 2 / (K + 1) := div_pos (sq_pos_of_pos hepsilon) hK1
  obtain ⟨⟨r, hr, hrd, hre⟩, ⟨s, hs, hsd, hse⟩⟩ :=
    scalarCover_exists_small_energy_circles hHs hE heta hdelta
  have hEn (a : ℝ) : 0 ≤ scalarCoverCircleDifferentialEnergy H a :=
    integral_nonneg (fun _ => sq_nonneg _)
  constructor
  · refine ⟨r, hr, hrd, ?_⟩
    have hnon : 0 ≤ (r - 1) * scalarCoverCircleDifferentialEnergy H r :=
      mul_nonneg (sub_pos.mpr hr.1).le (hEn r)
    have hsmall : ((r - 1) * scalarCoverCircleDifferentialEnergy H r) * (K + 1) <
        epsilon ^ 2 := (lt_div_iff₀ hK1).mp hre
    have hsq : scalarCoverWeightedFlux D H r ^ 2 < epsilon ^ 2 := by
      have hb := (hbound r hr).1
      change scalarCoverWeightedFlux D H r ^ 2 ≤
        K * ((r - 1) * scalarCoverCircleDifferentialEnergy H r) at hb
      nlinarith
    exact (sq_lt_sq₀ (abs_nonneg _) hepsilon.le).mp (by simpa only [sq_abs] using hsq)
  · refine ⟨s, hs, hsd, ?_⟩
    have hnon : 0 ≤ (2 - s) * scalarCoverCircleDifferentialEnergy H s :=
      mul_nonneg (sub_pos.mpr hs.2).le (hEn s)
    have hsmall : ((2 - s) * scalarCoverCircleDifferentialEnergy H s) * (K + 1) <
        epsilon ^ 2 := (lt_div_iff₀ hK1).mp hse
    have hsq : (scalarFluxPeriod D H s - scalarCoverWeightedFlux D H s) ^ 2 <
        epsilon ^ 2 := by
      have hb := (hbound s hs).2
      change (scalarFluxPeriod D H s - scalarCoverWeightedFlux D H s) ^ 2 ≤
        K * ((2 - s) * scalarCoverCircleDifferentialEnergy H s) at hb
      nlinarith
    exact (sq_lt_sq₀ (abs_nonneg _) hepsilon.le).mp (by simpa only [sq_abs] using hsq)

theorem scalarCover_weighted_flux_bounds {H : Plane → ℝ} (hHc : Continuous H)
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hlap : ∀ x ∈ scalarAnnulus, D.laplacian H x = 0)
    (hE : IntegrableOn (fun x => ‖fderiv ℝ H x‖ ^ 2) scalarAnnulus)
    (hinner : ∀ x : Plane, ‖x‖ = 1 → H x = 0)
    (houter : ∀ x : Plane, ‖x‖ = 2 → H x = 1)
    {r : ℝ} (hr : r ∈ Ioo (1 : ℝ) 2) :
    0 ≤ scalarCoverWeightedFlux D H r ∧
      scalarCoverWeightedFlux D H r ≤ scalarFluxPeriod D H r := by
  constructor
  · by_contra h
    have hneg : scalarCoverWeightedFlux D H r < 0 := lt_of_not_ge h
    obtain ⟨⟨s, hs, hsd, hse⟩, -⟩ := scalarCover_exists_boundary_flux_approximation
      D hHc hHs hlap hE hinner houter
      (show 0 < -scalarCoverWeightedFlux D H r / 2 by linarith)
      (sub_pos.mpr hr.1)
    have hsr : s ≤ r := by linarith
    have hm := scalarCoverWeightedFlux_mono D hHs hlap hs hr hsr
    have ha := (abs_lt.mp hse).1
    linarith
  · by_contra h
    have hpos : scalarFluxPeriod D H r < scalarCoverWeightedFlux D H r := lt_of_not_ge h
    obtain ⟨-, ⟨s, hs, hsd, hse⟩⟩ := scalarCover_exists_boundary_flux_approximation
      D hHc hHs hlap hE hinner houter
      (show 0 < (scalarCoverWeightedFlux D H r - scalarFluxPeriod D H r) / 2 by linarith)
      (sub_pos.mpr hr.2)
    have hrs : r ≤ s := by linarith
    have hm := scalarCoverWeightedFlux_mono D hHs hlap hr hs hrs
    rw [scalarFluxPeriod_eq D hHs hlap hs hr] at hse
    have ha := (abs_lt.mp hse).1
    linarith

end PoincareConjecture.M64Uniformization
