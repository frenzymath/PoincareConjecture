import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityPowerDecay

set_option autoImplicit false

open Set Metric MeasureTheory
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65LocalWeakMap

open M65Interior

theorem local_derivative_energy_decay
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M] {N : ℕ}
    {e : M → EuclideanSpace ℝ (Fin N)} {U : Set LoopPlane}
    (F : M65LocalWeakMap e U) (g : RiemannianMetric 3 M)
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    (hU : IsOpen U) (hmin : M65LocallyMinimizesEnergy g F)
    (x0 : LoopPlane) {R : ℝ} (hR : 0 < R) (hRU : closedBall x0 R ⊆ U) :
    ∃ β Λ : ℝ, 0 < β ∧ β < 1 ∧ 0 < Λ ∧
      ∀ x ∈ closedBall x0 (R / 2), ∀ r : ℝ, 0 < r → r ≤ R / 2 →
        (∫ z in closedBall x r, ∑ i : Fin 2, ‖F.derivative i z‖ ^ 2) ≤ Λ * r ^ (2 * β) := by
  let en := m65EmbeddedEnergyDensity g e F.value F.derivative
  let E0 := ∫ z in closedBall x0 R, en z
  have hen (z : LoopPlane) : 0 ≤ en z := embeddedEnergyDensity_nonneg g e F.value F.derivative z
  have hE0 : 0 ≤ E0 := integral_nonneg hen
  obtain ⟨a, ha, ha1, hdecay⟩ :=
    localMinimum_energy_power_decay g e he hinj hemb compact E0 hE0
  obtain ⟨c, C, hc, _, hb⟩ := m65EmbeddingMetric_uniform_bounds g e he hinj compact
  let Λ0 := (2 / c) * E0 * (R / 2) ^ (-a)
  have hΛ0 : 0 ≤ Λ0 := by dsimp only [Λ0]; positivity
  have hhalf : 0 < R / 2 := by positivity
  refine ⟨a / 2, 1 + Λ0, by positivity, by linarith, by positivity, ?_⟩
  intro x hx r hr hrhalf
  have houter : closedBall x (R / 2) ⊆ closedBall x0 R :=
    closedBall_subset_closedBall' (by have h := mem_closedBall.mp hx; linarith)
  have hinner : closedBall x r ⊆ U :=
    ((closedBall_subset_closedBall hrhalf).trans houter).trans hRU
  have hEouter : (∫ z in closedBall x (R / 2), en z) ≤ E0 :=
    setIntegral_mono_set
      (F.energy_integrable g he hinj hemb compact (closedBall x0 R)
        (isCompact_closedBall x0 R) hRU)
      (ae_of_all _ hen) (ae_of_all _ (fun _ hz => houter hz))
  have hEi := F.energy_integrable g he hinj hemb compact (closedBall x r)
    (isCompact_closedBall x r) hinner
  have hDi : IntegrableOn (fun z => ∑ i : Fin 2, ‖F.derivative i z‖ ^ 2) (closedBall x r) := by
    apply integrable_finsetSum
    intro i _
    exact (F.derivative_memLp i (closedBall x r)
      (isCompact_closedBall x r) hinner).norm.integrable_sq
  have hlower : (c / 2) * (∫ z in closedBall x r, ∑ i : Fin 2, ‖F.derivative i z‖ ^ 2) ≤
      ∫ z in closedBall x r, en z := by
    simpa only [integral_const_mul] using integral_mono_ae (hDi.const_mul (c / 2)) hEi
      (ae_of_all _ (fun z => (m65EmbeddedEnergyDensity_bounds g e hb F.value F.derivative z).1))
  have hraw : (∫ z in closedBall x r, ∑ i : Fin 2, ‖F.derivative i z‖ ^ 2) ≤
      (2 / c) * ∫ z in closedBall x r, en z := by
    calc
      _ ≤ (∫ z in closedBall x r, en z) / (c / 2) := by
        apply (le_div_iff₀ (show 0 < c / 2 by positivity)).mpr
        simpa only [mul_comm] using hlower
      _ = _ := by ring
  have hE := hdecay U F hU hmin x r (R / 2) hr hrhalf (houter.trans hRU) hEouter
  calc
    _ ≤ (2 / c) * ∫ z in closedBall x r, en z := hraw
    _ ≤ (2 / c) * (E0 * (r / (R / 2)) ^ a) :=
      mul_le_mul_of_nonneg_left hE (by positivity)
    _ = Λ0 * r ^ (2 * (a / 2)) := by
      dsimp only [Λ0]
      rw [show 2 * (a / 2) = a by ring]
      rw [Real.div_rpow hr.le hhalf.le, Real.rpow_neg hhalf.le]
      ring
    _ ≤ (1 + Λ0) * r ^ (2 * (a / 2)) := by
      apply mul_le_mul_of_nonneg_right (by linarith)
      exact Real.rpow_nonneg hr.le _

end PoincareConjecture.M65LocalWeakMap
