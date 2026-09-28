import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCylinderArea

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Cover" => ℝ × ℝ
local notation "Strip" => Set.preimage (fun p : Plane => p 1) (Ioo (0 : ℝ) 1)

private theorem period_pos : 0 < curvePeriod := by
  unfold curvePeriod
  positivity

theorem scalarInverseCylinderMap_modulus_conformal
    {g : RiemannianMetric 2 Plane} (D : LeviCivitaData g)
    {H : Plane → ℝ} {V : Cover → ℝ}
    (hHs : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ H scalarAnnulus)
    (hdV : ∀ z ∈ scalarCoverStrip, HasFDerivAt V (scalarCoverForm D H z) z)
    {P : ℝ} (hP : 0 < P) (e : OpenPartialHomeomorph Cover Cover)
    (hsource : e.source = scalarCoverStrip)
    (htarget : e.target = scalarPotentialStrip)
    (he : (e : Cover → Cover) = scalarNormalizedCoverMap H V P)
    (hes : ContDiffOn ℝ ∞ e e.source)
    (hei : ContDiffOn ℝ ∞ e.symm e.target) {p : Plane} (hp : p ∈ Strip) :
    (curvePeriod / P) * m60AreaGram g (scalarInverseCylinderMap e) p 0 0 =
      (curvePeriod / P)⁻¹ * m60AreaGram g (scalarInverseCylinderMap e) p 1 1 ∧
      m60AreaGram g (scalarInverseCylinderMap e) p 0 1 = 0 := by
  let L := scalarCylinderCoordinate
  let F := scalarInverseCylinderMap e
  have hLt : L p ∈ e.target := htarget ▸ hp
  have hFd : fderiv ℝ F p = (fderiv ℝ (scalarInverseCoverMap e) (L p)).comp L := by
    simpa only [F, scalarInverseCylinderMap, L, ContinuousLinearMap.fderiv] using fderiv_comp p
      (((scalarInverseCoverMap_smooth e hei).contDiffAt
        (e.open_target.mem_nhds hLt)).differentiableAt (by simp)) L.differentiableAt
  let E := g.inner (F p) (D.gradient H (F p)) (D.gradient H (F p))
  have hmetric (v w : Plane) :
      E * g.inner (F p) (fderiv ℝ F p v) (fderiv ℝ F p w) =
        (L v).1 * (L w).1 + P ^ 2 * (L v).2 * (L w).2 := by
    rw [hFd]
    exact scalarInverseCoverMap_metric_identity D hHs hdV hP.ne' e hsource he hes hei
      hLt (L v) (L w)
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hgram (i j : Fin 2) : m60AreaGram g F p i j =
      g.inner (F p) (fderiv ℝ F p (b i)) (fderiv ℝ F p (b j)) := by
    unfold m60AreaGram
    rw [mfderiv_eq_fderiv]
    rfl
  have h00 : E * m60AreaGram g F p 0 0 = P ^ 2 * curvePeriod⁻¹ * curvePeriod⁻¹ := by
    rw [hgram]
    simpa [L, scalarCylinderCoordinate_apply, b, EuclideanSpace.basisFun_apply]
      using hmetric (b 0) (b 0)
  have h11 : E * m60AreaGram g F p 1 1 = 1 := by
    rw [hgram]
    simpa [L, scalarCylinderCoordinate_apply, b, EuclideanSpace.basisFun_apply]
      using hmetric (b 1) (b 1)
  have h01 : E * m60AreaGram g F p 0 1 = 0 := by
    rw [hgram]
    simpa [L, scalarCylinderCoordinate_apply, b, EuclideanSpace.basisFun_apply]
      using hmetric (b 0) (b 1)
  have hE : E ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at h11
    exact zero_ne_one h11
  constructor
  · apply mul_left_cancel₀ hE
    have hbalance : (curvePeriod / P) * (P ^ 2 * curvePeriod⁻¹ * curvePeriod⁻¹) =
        (curvePeriod / P)⁻¹ := by
      field_simp [hP.ne', period_pos.ne']
    calc
      E * ((curvePeriod / P) * m60AreaGram g F p 0 0) =
          (curvePeriod / P) * (E * m60AreaGram g F p 0 0) := by ring
      _ = (curvePeriod / P) * (P ^ 2 * curvePeriod⁻¹ * curvePeriod⁻¹) := by rw [h00]
      _ = (curvePeriod / P)⁻¹ := hbalance
      _ = E * ((curvePeriod / P)⁻¹ * m60AreaGram g F p 1 1) := by
        rw [mul_left_comm E, h11, mul_one]
  · exact (mul_eq_zero.mp h01).resolve_left hE

theorem exists_smooth_modulus_conformal_cylinder_area (g : RiemannianMetric 2 Plane) :
    ∃ (r : ℝ), 0 < r ∧ ∃ F : Plane → Plane,
      ContDiffOn ℝ ∞ F Strip ∧
      (∀ p ∈ Strip, F p ∈ scalarAnnulus) ∧
      InjOn F scalarCylinderFundamental ∧
      F '' scalarCylinderFundamental = scalarAnnulus ∧
      (∀ x s : ℝ, s ∈ Ioo (0 : ℝ) 1 →
        F (annulusPoint (x + curvePeriod) s) = F (annulusPoint x s)) ∧
      (∀ p ∈ Strip,
        r * m60AreaGram g F p 0 0 = r⁻¹ * m60AreaGram g F p 1 1 ∧
          m60AreaGram g F p 0 1 = 0) ∧
      IntegrableOn (m60AreaDensity g F) scalarCylinderFundamental ∧
      (∫ p in scalarCylinderFundamental, m60AreaDensity g F p) =
        ∫ x in scalarAnnulus, m60AreaDensity g id x := by
  obtain ⟨D⟩ := m01_exists_leviCivitaData g
  obtain ⟨H, V, P, e, -, hHs, -, -, -, hP, -, -, hdV,
    hsource, htarget, he, hes, hei, hdeck⟩ := exists_smooth_annular_cover_chart D
  let F := scalarInverseCylinderMap e
  have hA : IntegrableOn (m60AreaDensity g id) scalarAnnulus := by
    apply ((m60AreaDensity_continuous g contMDiff_id).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Plane) 2)).mono_set
    intro p hp
    simpa only [Metric.mem_closedBall, dist_zero_right] using hp.2.le
  refine ⟨curvePeriod / P, div_pos period_pos hP, F,
    scalarInverseCylinderMap_smooth e htarget hei, ?_,
    scalarInverseCylinderMap_injOn_fundamental e hsource htarget hdeck,
    scalarInverseCylinderMap_image_fundamental e hsource htarget hdeck, ?_, ?_, ?_, ?_⟩
  · intro p hp
    apply scalarCoverMap_mem
    rw [← hsource]
    exact e.map_target (htarget ▸ hp)
  · intro x s hs
    change scalarInverseCoverMap e (scalarCylinderCoordinate (annulusPoint (x + curvePeriod) s)) = _
    rw [scalarCylinderCoordinate_periodic]
    exact scalarInverseCoverMap_periodic e hsource htarget hdeck (htarget ▸ hs)
  · intro p hp
    exact scalarInverseCylinderMap_modulus_conformal D hHs hdV hP e
      hsource htarget he hes hei hp
  · exact scalarInverseCylinderMap_area_integrable g contMDiffOn_id hA e
      hsource htarget hei hdeck
  · exact scalarInverseCylinderMap_area g contMDiffOn_id e hsource htarget hei hdeck

end PoincareConjecture.M64Uniformization
