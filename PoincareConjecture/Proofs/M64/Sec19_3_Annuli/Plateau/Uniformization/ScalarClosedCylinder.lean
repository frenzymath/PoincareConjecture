import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarClosedCover
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCylinderMetric

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Strip" => Set.preimage (fun p : Plane => p 1) (Ioo (0 : ℝ) 1)
local notation "ClosedStrip" => Set.preimage (fun p : Plane => p 1) (Icc (0 : ℝ) 1)

theorem exists_lipschitz_modulus_conformal_closed_cylinder (g : RiemannianMetric 2 Plane) :
    ∃ r : ℝ, 0 < r ∧ ∃ (K : ℝ≥0) (F : Plane → Plane),
      LipschitzWith K F ∧ ContDiffOn ℝ ∞ F Strip ∧
      MapsTo F Strip scalarAnnulus ∧
      MapsTo F ClosedStrip (closure scalarAnnulus) ∧
      InjOn F scalarCylinderFundamental ∧ F '' scalarCylinderFundamental = scalarAnnulus ∧
      (∀ x s : ℝ, s ∈ Icc (0 : ℝ) 1 →
        F (annulusPoint (x + curvePeriod) s) = F (annulusPoint x s)) ∧
      (∀ x : ℝ, ‖F (annulusPoint x 0)‖ = 1) ∧
      (∀ x : ℝ, ‖F (annulusPoint x 1)‖ = 2) ∧
      (∀ p ∈ Strip,
        r * m60AreaGram g F p 0 0 = r⁻¹ * m60AreaGram g F p 1 1 ∧
          m60AreaGram g F p 0 1 = 0) ∧
      IntegrableOn (m60AreaDensity g F) scalarCylinderFundamental ∧
      (∫ p in scalarCylinderFundamental, m60AreaDensity g F p) =
        ∫ x in scalarAnnulus, m60AreaDensity g id x := by
  obtain ⟨D⟩ := m01_exists_leviCivitaData g
  obtain ⟨H, V, P, e, hHc, hHs, hlap, hinner, houter, hP, -, -, hdV,
    hsource, htarget, he, hes, hei, hdeck⟩ := exists_smooth_annular_cover_chart D
  obtain ⟨K, F, hF, hFeq, hmaps, -, hperiod, hzero, hone⟩ :=
    exists_scalar_closed_cover_extension D hHc hHs hlap hinner houter hdV hP.ne'
      e hsource htarget he hes hei hdeck
  let G : Plane → Plane := F ∘ scalarCylinderCoordinate
  have hGc := hF.comp scalarCylinderCoordinate.lipschitz
  have hGeq : EqOn G (scalarInverseCylinderMap e) Strip := by
    intro p hp
    exact hFeq (htarget ▸ hp)
  have hGs : ContDiffOn ℝ ∞ G Strip :=
    (scalarInverseCylinderMap_smooth e htarget hei).congr (fun _ hp => hGeq hp)
  have hGloc {p : Plane} (hp : p ∈ Strip) : G =ᶠ[𝓝 p] scalarInverseCylinderMap e := by
    filter_upwards [((EuclideanSpace.proj (1 : Fin 2)).continuous.isOpen_preimage
      _ isOpen_Ioo).mem_nhds hp] with q hq
    exact hGeq hq
  have hLcl {p : Plane} (hp : p ∈ ClosedStrip) :
      scalarCylinderCoordinate p ∈ closure e.target := by
    rw [htarget, scalarPotentialStrip_closure]
    exact hp
  have hperiodpos : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hA : IntegrableOn (m60AreaDensity g id) scalarAnnulus := by
    apply ((m60AreaDensity_continuous g contMDiff_id).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) 2)).mono_set
    intro p hp
    simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2.le
  have hAE : m60AreaDensity g G =ᵐ[volume.restrict scalarCylinderFundamental]
      m60AreaDensity g (scalarInverseCylinderMap e) := by
    filter_upwards [ae_restrict_mem scalarCylinderFundamental_measurable] with p hp
    exact m60AreaDensity_congr_of_eventuallyEq g (hGloc hp.1)
  refine ⟨curvePeriod / P, div_pos hperiodpos hP, _, G, hGc, hGs,
    ?_, fun _ hp => hmaps (hLcl hp), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p hp
    rw [hGeq hp]
    exact scalarCoverMap_mem (hsource ▸ e.map_target (htarget ▸ hp))
  · intro p hp q hq hpq
    apply scalarInverseCylinderMap_injOn_fundamental e hsource htarget hdeck hp hq
    rw [← hGeq hp.1, ← hGeq hq.1]
    exact hpq
  · rw [← scalarInverseCylinderMap_image_fundamental e hsource htarget hdeck]
    exact (show EqOn G (scalarInverseCylinderMap e) scalarCylinderFundamental from
      fun _ hp => hGeq hp.1).image_eq
  · intro x s hs
    change F (scalarCylinderCoordinate (annulusPoint (x + curvePeriod) s)) = _
    rw [scalarCylinderCoordinate_periodic]
    exact hperiod _ (hLcl hs)
  · intro x
    exact hzero (curvePeriod⁻¹ * x)
  · intro x
    exact hone (curvePeriod⁻¹ * x)
  · intro p hp
    have hgram (i j : Fin 2) : m60AreaGram g G p i j =
        m60AreaGram g (scalarInverseCylinderMap e) p i j := by
      unfold m60AreaGram
      rw [mfderiv_eq_fderiv, mfderiv_eq_fderiv, hGeq hp, (hGloc hp).fderiv_eq]
    rw [hgram, hgram, hgram]
    exact scalarInverseCylinderMap_modulus_conformal D hHs hdV hP e
      hsource htarget he hes hei hp
  · exact (scalarInverseCylinderMap_area_integrable g contMDiffOn_id hA e
      hsource htarget hei hdeck).congr hAE.symm
  · calc
      _ = ∫ p in scalarCylinderFundamental, m60AreaDensity g (scalarInverseCylinderMap e) p :=
        integral_congr_ae hAE
      _ = _ := scalarInverseCylinderMap_area g contMDiffOn_id e hsource htarget hei hdeck

end PoincareConjecture.M64Uniformization
