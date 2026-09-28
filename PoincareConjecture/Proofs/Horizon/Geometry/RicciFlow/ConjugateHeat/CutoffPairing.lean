import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.ProductTests
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.MassExhaustion


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow.ConjugateHeat

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}



theorem tendsto_weakPairing_productTests
    (F : RicciFlow n M J) {α β V : ℝ} (hαβ : α ≤ β) (hV : 0 ≤ V)
    (ht : ∀ τ ∈ Icc α β, -τ ∈ interior J)
    {u : M × ℝ → ℝ} (hu : ContinuousOn u (univ ×ˢ Icc α β))
    (hu0 : ∀ τ ∈ Icc α β, ∀ x, 0 ≤ u (x, τ))
    (hmass : ∀ τ ∈ Icc α β,
      Integrable (fun x => u (x, τ)) (F.metric (-τ)).volumeMeasure ∧
      (∫ x, u (x, τ) ∂(F.metric (-τ)).volumeMeasure) = V)
    (χ : ℕ → M → ℝ) (hχ : ∀ j, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (χ j))
    (hc : ∀ j, HasCompactSupport (χ j))
    (hχrange : ∀ j x, χ j x ∈ Icc 0 1)
    (hχlim : ∀ x, Tendsto (fun j => χ j x) atTop (𝓝 1))
    {B : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hBlim : Tendsto B atTop (𝓝 0))
    (hlap : ∀ j τ, τ ∈ Icc α β →
      |∫ x, u (x, τ) * (F.connection (-τ)).laplacian (χ j) x
        ∂(F.metric (-τ)).volumeMeasure| ≤ B j)
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hs : tsupport η ⊆ Ioo α β) :
    Tendsto (fun j => weakPairing F u (fun z => χ j z.1 * η z.2)) atTop (𝓝 0) := by
  let a := fun j τ => deriv η τ * ∫ x, u (x, τ) * χ j x ∂(F.metric (-τ)).volumeMeasure
  let b := fun j τ => η τ * ∫ x, u (x, τ) * (F.connection (-τ)).laplacian (χ j) x
    ∂(F.metric (-τ)).volumeMeasure
  let H := fun j τ => ∫ x, u (x, τ) * testOperator F (fun z => χ j z.1 * η z.2) (x, τ)
    ∂(F.metric (-τ)).volumeMeasure
  have heq (j : ℕ) (τ : ℝ) (hτ : τ ∈ Icc α β) : H j τ = a j τ + b j τ :=
    integral_productTest_operator F (hu.comp_continuous
      (continuous_id.prodMk continuous_const) (fun x => ⟨mem_univ x, hτ⟩))
      (hχ j) (hc j) hη
  have ha (j : ℕ) : IntegrableOn (a j) (Icc α β) :=
    (((hη.deriv' (n := ∞)).continuous.continuousOn).mul
      (continuousOn_cutoffMass F ht hu (hχ j).continuous (hc j))).integrableOn_Icc
  have hH (j : ℕ) : Integrable (H j) :=
    (weakPairing_integrable_of_continuousOn F ht hu
      (productTest (hχ j) (hc j) hη hηc hs)).2
  have hb (j : ℕ) : IntegrableOn (b j) (Icc α β) := by
    apply ((hH j).integrableOn.sub (ha j)).congr_fun ?_ measurableSet_Icc
    intro τ hτ
    change H j τ - a j τ = b j τ
    rw [heq j τ hτ]
    ring
  have hbound (j : ℕ) : |∫ τ in Icc α β, b j τ| ≤
      (∫ τ in Icc α β, |η τ|) * B j := by
    have h := norm_integral_le_of_norm_le
      ((hη.continuous.abs.continuousOn.mul_const (B j)).integrableOn_Icc)
      (show ∀ᵐ τ ∂volume.restrict (Icc α β), ‖b j τ‖ ≤ |η τ| * B j from by
        filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
        simp only [b, Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hlap j τ hτ) (abs_nonneg _))
    simpa only [Real.norm_eq_abs, integral_mul_const] using h
  have hblim : Tendsto (fun j => ∫ τ in Icc α β, b j τ) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simp only [Real.norm_eq_abs]
    exact squeeze_zero (fun _ => abs_nonneg _) hbound
      (by simpa only [mul_zero] using tendsto_const_nhds.mul hBlim)
  have halim : Tendsto (fun j => ∫ τ in Icc α β, a j τ) atTop (𝓝 0) :=
    tendsto_integral_deriv_cutoffMass F hαβ hV ht hu hu0 hmass χ
      (fun j => (hχ j).continuous) hc hχrange hχlim hη hs
  have hsum : Tendsto (fun j => (∫ τ in Icc α β, a j τ) +
      (∫ τ in Icc α β, b j τ)) atTop (𝓝 0) := by
    simpa only [add_zero] using halim.add hblim
  apply hsum.congr
  intro j
  rw [← integral_add (ha j) (hb j)]
  change (∫ τ in Icc α β, a j τ + b j τ) = ∫ τ, H j τ
  rw [← setIntegral_congr_fun measurableSet_Icc (heq j)]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro τ hτ
  apply integral_eq_zero_of_ae
  exact ae_of_all _ (fun x => by
    have hn : (x, τ) ∉ tsupport (fun z : M × ℝ => χ j z.1 * η z.2) := by
      intro hz
      have ht' := hs (tsupport_productTest_subset (χ j) η hz).2
      exact hτ ⟨ht'.1.le, ht'.2.le⟩
    change u (x, τ) * testOperator F (fun z => χ j z.1 * η z.2) (x, τ) = 0
    rw [testOperator_eq_zero_of_notMem_tsupport F hn, mul_zero])

end PoincareConjecture.RicciFlow.ConjugateHeat
