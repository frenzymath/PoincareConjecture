import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarCylinderAdmission












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]





theorem scalarLocalC1Composition_metric_lipschitz
    (g : RiemannianMetric n M) (f : Plane → M)
    {U : Set Plane} (hU : IsOpen U) (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U)
    {K : ℝ≥0} {F : Plane → Plane} (hF : LipschitzWith K F)
    (hmaps : MapsTo F m64AnnulusDomain U) :
    ∃ L : ℝ≥0, ∀ x y : m64AnnulusDomain,
      g.edist (f (F x)) (f (F y)) ≤
        (L : ℝ≥0∞) * ENNReal.ofReal ‖(x : Plane) - y‖ := by
  apply m64Annulus_hLip_of_local g
    (hf.continuousOn.comp hF.continuous.continuousOn hmaps)
  intro p hp
  obtain ⟨C, V, hV, hC⟩ := m64_lipschitzOn_nhds_of_contMDiffAt g
    (hf.contMDiffAt (hU.mem_nhds (hmaps hp)))
  refine ⟨C * K, F ⁻¹' V, hF.continuous.continuousAt.preimage_mem_nhds hV, ?_⟩
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





theorem scalarLocalC1ClosedCylinder_admit
    (g : RiemannianMetric n M) (f : Plane → M)
    {U : Set Plane} (hU : IsOpen U) (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U)
    {K : ℝ≥0} {F : Plane → Plane} (hF : LipschitzWith K F)
    (hmaps : MapsTo F m64AnnulusDomain U)
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
  obtain ⟨L, hL⟩ := scalarLocalC1Composition_metric_lipschitz g f hU hf hF hmaps
  apply m64Annulus_exists_eqOn_rectangle_of_lipschitz g
    (hboundary 1 sigma0) (hboundary 2 sigma1) (f ∘ F)
    (hf.continuousOn.comp hF.continuous.continuousOn hmaps)
  · intro s hs
    exact congrArg f (by simpa only [zero_add] using hperiod 0 s hs)
  · intro x _
    exact congrArg f (hzero x)
  · intro x _
    exact congrArg f (hone x)
  · exact L.coe_nonneg
  · simpa only [ENNReal.ofReal_coe_nnreal, Function.comp_apply] using! hL

end PoincareConjecture.M64Uniformization
