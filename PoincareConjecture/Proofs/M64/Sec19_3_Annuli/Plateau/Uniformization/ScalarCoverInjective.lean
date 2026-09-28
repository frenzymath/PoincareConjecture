import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCoverImageArea
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarIntegerNoOverlap
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarStripInjectivity














set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M64Uniformization

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ
local notation "Band" => Set.prod (Ioo (1 : ℝ) 2) (Ioo (0 : ℝ) 1)

variable {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)





theorem scalarNormalizedCoverMap_injOn (w : H1Zero D scalarAnnulus)
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
    (hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1) :
    InjOn (scalarNormalizedCoverMap H V (scalarFluxPeriod D H (3 / 2))) scalarCoverStrip := by
  let P := scalarFluxPeriod D H (3 / 2)
  let F := scalarNormalizedCoverMap H V P
  have hP : 0 < P := scalarPotential_fluxPeriod_pos D w hHc hHs hHae hlap hinner houter
    (by norm_num : (3 / 2 : ℝ) ∈ Ioo 1 2)
  have hd : ∀ z ∈ scalarCoverStrip, DifferentiableAt ℝ F z :=
    fun z hz => scalarNormalizedCoverMap_differentiableAt D hHs hdV P hz
  have ho : ∀ z ∈ scalarCoverStrip, 𝓝 (F z) ≤ map F (𝓝 z) :=
    fun z hz => scalarNormalizedCoverMap_nhds_le_map D hHc hHs hlap hinner houter hdV hP.ne' hz
  have hE : IsOpen (F '' Band) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro _ ⟨z, hz, rfl⟩
    exact ho z hz.1 (Filter.image_mem_map ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hz))
  have hJ := (scalarPotential_unitCover_energy D w hHs hHae).1
  have hint := scalarNormalizedCoverMap_abs_det_integrable D hHs hdV hP hJ
  have hmass : (∫⁻ z in Band, ENNReal.ofReal |(fderiv ℝ F z).det|) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun z => abs_nonneg _)]
    rw [scalarNormalizedCoverMap_total_abs_det_one D w hHc hHs hHae hlap hinner houter hdV]
    norm_num
  have hcover :=
    scalarNormalizedCoverMap_integer_cover D hHc hHs hlap hinner houter hdV hP hdeck hrange
  have hlower : 1 ≤ volume (F '' Band) :=
    scalar_area_ge_one_of_integer_cover hE.measurableSet hcover
  have hupper : volume (F '' Band) ≤ 1 :=
    scalarNormalizedCoverMap_image_area_le_one D w hHc hHs hHae hlap hinner houter hdV
  have hband : InjOn F Band := scalar_injOn_of_unit_jacobian_and_image_area
    (isOpen_Ioo.prod isOpen_Ioo) (fun z hz => hd z hz.1) (fun z hz => ho z hz.1)
    hlower hmass.le
  exact scalar_injOn_strip_of_fundamental_image ho
    (scalarAngularCuts_image_measure_zero hd)
    (fun z hz n => scalarNormalizedCoverMap_sub_int (H := H) hP.ne' hdeck hz n) hband
    (fun a ha k hk => scalar_integer_translate_no_overlap hE hcover hupper ha hk)





theorem scalarNormalizedCover_isHomeomorph (w : H1Zero D scalarAnnulus)
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
    (hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1) :
    IsHomeomorph (scalarNormalizedCover H V (scalarFluxPeriod D H (3 / 2)) hrange) := by
  have hP := scalarPotential_fluxPeriod_pos D w hHc hHs hHae hlap hinner houter
    (by norm_num : (3 / 2 : ℝ) ∈ Ioo 1 2)
  have hVc : ContinuousOn V scalarCoverStrip :=
    fun z hz => (hdV z hz).continuousAt.continuousWithinAt
  refine ⟨((scalarNormalizedCoverMap_continuousOn hHc hVc _).domRestrict).subtype_mk _,
    scalarNormalizedCover_isOpenMap D hHc hHs hlap hinner houter hdV hP.ne' hrange, ?_,
    scalarNormalizedCover_surjective D hHc hHs hlap hinner houter hVc hdV hP hdeck hrange⟩
  intro x y hxy
  exact Subtype.ext (scalarNormalizedCoverMap_injOn D w hHc hHs hHae hlap hinner houter
    hdV hdeck hrange x.property y.property (congrArg Subtype.val hxy))





theorem exists_homeomorphic_annular_cover_conjugate :
    ∃ (H : Plane → ℝ) (V : Cover → ℝ) (P : ℝ),
      Continuous H ∧ ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus ∧
      (∀ x ∈ scalarAnnulus, D.laplacian H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 1 → H x = 0) ∧
      (∀ x : Plane, ‖x‖ = 2 → H x = 1) ∧
      0 < P ∧ P = scalarFluxPeriod D H (3 / 2) ∧
      ContDiffOn ℝ ∞ V scalarCoverStrip ∧
      (∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z) ∧
      (∀ z ∈ scalarCoverStrip, V (z + (0, 1)) = V z + P) ∧
      ∃ hrange : ∀ x ∈ scalarAnnulus, H x ∈ Ioo (0 : ℝ) 1,
        IsHomeomorph (scalarNormalizedCover H V P hrange) := by
  obtain ⟨H, w, V, hHc, hHs, hHae, hlap, hinner, houter, hrange, hP, hVs, hdV, hdeck⟩ :=
    exists_positive_period_annular_cover_conjugate D
  exact ⟨H, V, scalarFluxPeriod D H (3 / 2), hHc, hHs, hlap, hinner, houter, hP, rfl,
    hVs, hdV, hdeck, hrange,
    scalarNormalizedCover_isHomeomorph D w hHc hHs hHae hlap hinner houter hdV hdeck hrange⟩

end PoincareConjecture.M64Uniformization
