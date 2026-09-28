import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFreeClosedCylinder
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicRectangleAdmission
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)





theorem scalarCylinderFundamental_ae_eq_domain :
    scalarCylinderFundamental =ᵐ[volume] m64AnnulusDomain := by
  have hsub : scalarCylinderFundamental ⊆ m64AnnulusDomain := by
    intro p hp
    exact ⟨hp.2.1, hp.2.2.le, hp.1.1.le, hp.1.2.le⟩
  have hinterior : m64AnnulusInterior ⊆ scalarCylinderFundamental := by
    intro p hp
    simp only [m64AnnulusInterior, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      Set.mem_Ioo] at hp
    exact ⟨hp 1 trivial, (hp 0 trivial).1.le, (hp 0 trivial).2⟩
  filter_upwards [m64AnnulusDomain_ae_eq_interior] with p hp
  exact propext ⟨fun h => hsub h, fun h => hinterior (hp.mp h)⟩

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [TopologicalSpace M] [T2Space M] in



theorem scalarCircleComposition_periodic (f : Plane → M) (r : ℝ) :
    Function.Periodic (fun x => f (scalarCoverMap (r, x / curvePeriod))) curvePeriod := by
  have hp : curvePeriod ≠ 0 := by unfold curvePeriod; positivity
  intro x
  have hx : (x + curvePeriod) / curvePeriod = x / curvePeriod + 1 := by
    rw [add_div, div_self hp]
  change f (scalarCoverMap (r, (x + curvePeriod) / curvePeriod)) = _
  rw [hx]
  simpa only [Prod.mk_add_mk, add_zero] using
    congrArg f (scalarCoverMap_periodic (r, x / curvePeriod))





theorem scalarSmoothComposition_metric_lipschitz
    (g : RiemannianMetric n M) (f : Plane → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) {K : ℝ≥0} {F : Plane → Plane}
    (hF : LipschitzWith K F) :
    ∃ L : ℝ≥0, ∀ x y : m64AnnulusDomain,
      g.edist (f (F x)) (f (F y)) ≤
        (L : ℝ≥0∞) * ENNReal.ofReal ‖(x : Plane) - y‖ := by
  apply m64Annulus_hLip_of_local g (hf.continuous.comp hF.continuous).continuousOn
  intro p _
  obtain ⟨C, U, hU, hC⟩ := m64_lipschitzOn_nhds_of_contMDiffAt g
    ((hf (F p)).of_le (by simp))
  refine ⟨C * K, F ⁻¹' U, hF.continuous.continuousAt.preimage_mem_nhds hU, ?_⟩
  intro y hy z hz
  have hdist : ENNReal.ofReal ‖F y - F z‖ ≤
      (K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖ := by
    simpa only [edist_dist, dist_eq_norm] using hF y z
  calc
    g.edist (f (F y)) (f (F z)) ≤ (C : ℝ≥0∞) * ENNReal.ofReal ‖F y - F z‖ :=
      hC (F y) hy (F z) hz
    _ ≤ (C : ℝ≥0∞) * ((K : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖) :=
      mul_le_mul_right hdist _
    _ = ((C * K : ℝ≥0) : ℝ≥0∞) * ENNReal.ofReal ‖y - z‖ := by
      rw [ENNReal.coe_mul, mul_assoc]





theorem scalarClosedCylinder_admit
    (g : RiemannianMetric n M) (f : Plane → M)
    (hf : ContMDiff (𝓡 2) (𝓡 n) ∞ f) {K : ℝ≥0} {F : Plane → Plane}
    (hF : LipschitzWith K F)
    (hperiod : ∀ x s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      F (annulusPoint (x + curvePeriod) s) = F (annulusPoint x s))
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    (hzero : ∀ x : ℝ,
      F (annulusPoint x 0) = scalarCoverMap (1, sigma0.map x / curvePeriod))
    (hone : ∀ x : ℝ,
      F (annulusPoint x 1) = scalarCoverMap (2, sigma1.map x / curvePeriod)) :
    ∃ A : M64Annulus g
      ((fun x => f (scalarCoverMap (1, x / curvePeriod))) ∘ sigma0.map)
      ((fun x => f (scalarCoverMap (2, x / curvePeriod))) ∘ sigma1.map),
      EqOn A.map (f ∘ F) m64AnnulusDomain := by
  have hboundary (r : ℝ) (sigma : M64PeriodicDegreeOneLift) :
      Function.Periodic
        ((fun x => f (scalarCoverMap (r, x / curvePeriod))) ∘ sigma.map) curvePeriod := by
    intro x
    dsimp only [Function.comp_apply]
    rw [sigma.period_shift]
    exact scalarCircleComposition_periodic f r (sigma.map x)
  obtain ⟨L, hL⟩ := scalarSmoothComposition_metric_lipschitz g f hf hF
  apply m64Annulus_exists_eqOn_rectangle_of_lipschitz g
    (hboundary 1 sigma0) (hboundary 2 sigma1) (f ∘ F)
    (hf.continuous.comp hF.continuous).continuousOn
  · intro s hs
    exact congrArg f (by simpa only [zero_add] using hperiod 0 s hs)
  · intro x _
    exact congrArg f (hzero x)
  · intro x _
    exact congrArg f (hone x)
  · exact L.coe_nonneg
  · simpa only [ENNReal.ofReal_coe_nnreal, Function.comp_apply] using! hL

end PoincareConjecture.M64Uniformization
