import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Cutoff.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Spectral
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.CompactCutoff








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology BoundedContinuousFunction

namespace PoincareConjecture.LeviCivitaData.Dirichlet

open Boundary

variable {n : ℕ} [NeZero n] {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [PreconnectedSpace M]
  {g : RiemannianMetric n M}

theorem cutoff_sub_le_integral_heatKernelContinuousTime
    (D : LeviCivitaData g) {Ω : Set M} (S : Poincare.Manifold.SmoothDomain n Ω)
    {η : M → ℝ} (hη : Continuous η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ Ω) (hηrange : ∀ x, η x ∈ Icc 0 1)
    {B : ℝ} (hB : 0 ≤ B)
    (hsupport : ∀ x, 0 < η x → ∃ (U : Set M) (σ : M → ℝ),
      IsOpen U ∧ x ∈ U ∧ ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ σ U ∧
      σ x = η x ∧ (∀ y ∈ U, σ y ≤ η y) ∧ -B ≤ D.laplacian σ x)
    {t : ℝ} (ht : 0 < t) (x : M) :
    η x - B * t ≤ ∫ y, heatKernelContinuousTime D S t x y ∂g.volumeMeasure := by
  let : SecondCountableTopology M := g.secondCountableTopology
  obtain ⟨χ, hχ, hχc, hχΩ, hχrange, hχone, -⟩ :=
    Poincare.Manifold.exists_compact_smooth_cutoff (𝓡 n) hηc S.isOpen hηΩ
  let φ : EnergyTest D Ω := ⟨χ, hχ, hχc, hχΩ⟩
  obtain ⟨F, hF, hFzero, hFpos⟩ := exists_continuous_heat_test D S φ
  have hFc : Continuous (fun p : M × ℝ => F p.2 p.1) :=
    continuous_eval.comp ((hF.comp continuous_snd).prodMk continuous_fst)
  have hnonneg (z : M) (s : ℝ) (hs : s ∈ Icc 0 t) : 0 ≤ F s z := by
    by_cases hsp : 0 < s
    · rw [hFpos s hsp, heatPowerContinuousTime_of_pos D S 0 hsp]
      exact heatPowerContinuous_test_nonneg D S φ (fun w => (hχrange w).1) s hsp z
    · have hs0 : s = 0 := le_antisymm (not_lt.mp hsp) hs.1
      rw [hs0, hFzero]
      exact (hχrange z).1
  have hderiv (z : M) (s : ℝ) (hs : s ∈ Ioc 0 t) :
      HasDerivAt (fun r => F r z) (deriv (fun r => F r z) s) s := by
    let f := toDomainL2 D Ω (φ : H1Zero D Ω)
    have hT := hasDerivAt_heatPowerContinuousTime D S 0 hs.1
    have hd : HasDerivAt (fun r : ℝ => heatPowerContinuousTime D S 0 r f z)
        (-heatPowerContinuousTime D S 1 s f z) s := by
      have h := (BoundedContinuousFunction.evalCLM ℝ z).hasFDerivAt.comp_hasDerivAt s
        (hT.clm_apply (hasDerivAt_const s f))
      convert! h using 1
      simp
    have heq : (fun r => F r z) =ᶠ[𝓝 s]
        fun r => heatPowerContinuousTime D S 0 r f z := by
      filter_upwards [Ioi_mem_nhds hs.1] with r hr
      rw [hFpos r hr]
    exact (hd.congr_of_eventuallyEq heq).differentiableAt.hasDerivAt
  have hbound := D.cutoff_sub_le_heat_of_lower_supports S.isOpen hη hηc hηΩ hB hsupport
    (F := fun z s => F s z) (F' := fun z s => deriv (fun r => F r z) s) (b := t)
    hFc.continuousOn
    (fun s hs => contMDiffOn_heat_test_extension D S φ F hFpos s hs.1) hderiv
    (fun z hz s hs => (hasDerivAt_heat_test_extension D S φ F hFpos s hs.1 z hz).deriv.ge)
    hnonneg (fun z => by
      rw [hFzero]
      by_cases hz : z ∈ tsupport η
      · change η z ≤ χ z
        rw [hχone.self_of_nhdsSet z hz]
        exact (hηrange z).2
      · rw [image_eq_zero_of_notMem_tsupport hz]
        exact (hχrange z).1)
  apply (hbound x t ⟨ht.le, le_rfl⟩).trans
  rw [hFpos t ht, heatPowerContinuousTime_of_pos D S 0 ht,
    ← integral_heatKernelContinuous_test D S t ht x φ]
  have hK := heatKernelContinuousTime_isDirichletHeatKernel D S
  have heq : (∫ y, heatKernelContinuousTime D S t x y ∂g.volumeMeasure) =
      ∫ y in Ω, heatKernelContinuous D S t ht x y ∂g.volumeMeasure := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Ω) (fun y hy => hK.zero_outside t ht x y (Or.inr hy))]
    simp only [heatKernelContinuousTime_of_pos D S ht]
  rw [heq]
  apply integral_mono_of_nonneg
  · exact ae_of_all _ (fun y => mul_nonneg (heatKernelContinuous_nonneg D S t ht x y)
      (hχrange y).1)
  · exact integrable_heatKernelContinuous D S t ht x
  · exact ae_of_all _ (fun y => mul_le_of_le_one_right
      (heatKernelContinuous_nonneg D S t ht x y) (hχrange y).2)

end PoincareConjecture.LeviCivitaData.Dirichlet
