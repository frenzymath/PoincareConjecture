import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Spectral
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Exhaustion.Supremum













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology BoundedContinuousFunction

universe u

namespace PoincareConjecture.LeviCivitaData

open Dirichlet Dirichlet.Boundary

variable {n : ℕ} [NeZero n] {M : Type u} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

private theorem integral_heatKernelContinuous_test_le_shifted_solution
    (D : LeviCivitaData g) {Ω : Set M} (S : Poincare.Manifold.SmoothDomain n Ω)
    {u : M → ℝ → ℝ}
    (hcont : ContinuousOn (Function.uncurry u) (univ ×ˢ Ioi 0))
    (hspace : ∀ t, 0 < t → ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => u x t))
    (hheat : ∀ x t, 0 < t → HasDerivAt (u x)
      (D.laplacian (fun z => u z t) x) t)
    (hnonneg : ∀ x t, 0 < t → 0 ≤ u x t)
    {τ t : ℝ} (hτ : 0 < τ) (ht : 0 < t) (φ : EnergyTest D Ω)
    (hinit : ∀ x, φ x ≤ u x τ) (x : M) (hx : x ∈ Ω) :
    (∫ z in Ω, heatKernelContinuous D S t ht x z * φ z ∂g.volumeMeasure) ≤
      u x (t + τ) := by
  obtain ⟨F, hF, hFzero, hFpos⟩ := exists_continuous_heat_test D S φ
  have hFc : Continuous (fun p : M × ℝ => F p.2 p.1) :=
    continuous_eval.comp ((hF.comp continuous_snd).prodMk continuous_fst)
  have huc : ContinuousOn (fun p : M × ℝ => u p.1 (p.2 + τ))
      (closure Ω ×ˢ Icc 0 t) := by
    apply hcont.comp (f := fun p : M × ℝ => (p.1, p.2 + τ)) (by fun_prop)
    intro p hp
    exact ⟨mem_univ _, add_pos_of_nonneg_of_pos hp.2.1 hτ⟩
  have hboundary (z : M) (_hz : z ∈ closure Ω) (hzo : z ∉ Ω)
      (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : F s z ≤ u z (s + τ) := by
    have hz : F s z = 0 := by
      by_cases hsp : 0 < s
      · rw [hFpos s hsp, heatPowerContinuousTime_of_pos D S 0 hsp,
          heatPowerContinuous_zero_outside D S 0 s hsp _ z hzo]
      · have hs0 : s = 0 := le_antisymm (not_lt.mp hsp) hs.1
        rw [hs0, hFzero]
        exact image_eq_zero_of_notMem_tsupport (fun h => hzo (φ.support_subset h))
    rw [hz]
    exact hnonneg z (s + τ) (add_pos_of_nonneg_of_pos hs.1 hτ)
  have hcompare := le_of_subsolution_supersolution D S.isOpen S.isCompact_closure
    (F := fun z s => F s z) (G := fun z s => u z (s + τ))
    (F' := fun z s => D.laplacian (F s : M → ℝ) z)
    (G' := fun z s => D.laplacian (fun w => u w (s + τ)) z)
    (a := 0) (b := t) hFc.continuousOn huc
    (fun s hs => contMDiffOn_heat_test_extension D S φ F hFpos s hs.1)
    (fun s hs => (hspace (s + τ) (add_pos hs.1 hτ)).contMDiffOn)
    (fun z hz s hs =>
      (hasDerivAt_heat_test_extension D S φ F hFpos s hs.1 z hz).hasDerivWithinAt)
    (fun z _ s hs => by
      have hd := (hheat z (s + τ) (add_pos hs.1 hτ)).comp s
        ((hasDerivAt_id s).add_const τ)
      simpa only [mul_one, Function.comp_def, id_eq] using
        hd.hasDerivWithinAt (s := Icc 0 t))
    (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => le_rfl) hboundary
    (fun z _ => by rw [hFzero, zero_add]; exact hinit z)
  have h := hcompare x (subset_closure hx) t ⟨ht.le, le_rfl⟩
  rw [hFpos t ht, heatPowerContinuousTime_of_pos D S 0 ht] at h
  rwa [integral_heatKernelContinuous_test D S t ht x φ]




theorem heatKernelContinuousTime_le_of_nonnegative_heat_solution
    (D : LeviCivitaData g) {Ω : Set M} (S : Poincare.Manifold.SmoothDomain n Ω)
    {u : M → ℝ → ℝ} {y : M}
    (hcont : ContinuousOn (Function.uncurry u) (univ ×ˢ Ioi 0))
    (hspace : ∀ t, 0 < t → ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => u x t))
    (hheat : ∀ x t, 0 < t → HasDerivAt (u x)
      (D.laplacian (fun z => u z t) x) t)
    (hnonneg : ∀ x t, 0 < t → 0 ≤ u x t)
    (htrace : ∀ φ : M → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun t => ∫ z, φ z * u z t ∂g.volumeMeasure)
        (𝓝[>] 0) (𝓝 (φ y)))
    {t : ℝ} (ht : 0 < t) (x : M) :
    heatKernelContinuousTime D S t x y ≤ u x t := by
  rw [heatKernelContinuousTime_of_pos D S ht]
  by_cases hx : x ∈ Ω
  · by_cases hy : y ∈ Ω
    · obtain ⟨χ, -, hχ⟩ :=
        (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓡 n) y).mem_iff.mp
          (S.isOpen.mem_nhds hy)
      have hcompare (τ : ℝ) (hτ : 0 < τ) :
          (∫ z, heatKernelContinuous D S t ht x z * χ z * u z τ ∂g.volumeMeasure) ≤
            u x (t + τ) := by
        let φ : EnergyTest D Ω :=
          ⟨fun z => χ z * u z τ, χ.contMDiff.mul (hspace τ hτ),
            χ.hasCompactSupport.mul_right, tsupport_mul_subset_left.trans hχ⟩
        have h := integral_heatKernelContinuous_test_le_shifted_solution D S
          hcont hspace hheat hnonneg hτ ht φ
          (fun z => mul_le_of_le_one_left (hnonneg z τ hτ) χ.le_one) x hx
        change (∫ z in Ω, heatKernelContinuous D S t ht x z * (χ z * u z τ)
          ∂g.volumeMeasure) ≤ u x (t + τ) at h
        simp_rw [← mul_assoc] at h
        have heq :
            (∫ z in Ω, heatKernelContinuous D S t ht x z * χ z * u z τ
              ∂g.volumeMeasure) =
            ∫ z, heatKernelContinuous D S t ht x z * χ z * u z τ
              ∂g.volumeMeasure := by
          apply setIntegral_eq_integral_of_forall_compl_eq_zero
          intro z hz
          have hzχ : χ z = 0 :=
            image_eq_zero_of_notMem_tsupport (fun h => hz (hχ h))
          simp only [hzχ, mul_zero, zero_mul]
        rwa [heq] at h
      have hrow := continuous_heatKernelContinuous_row D S t ht x
      have hlim := htrace (fun z => heatKernelContinuous D S t ht x z * χ z)
        (hrow.mul χ.contMDiff.continuous) χ.hasCompactSupport.mul_left
      rw [χ.eq_one, mul_one] at hlim
      have hright : Tendsto (fun τ => u x (t + τ)) (𝓝[>] 0) (𝓝 (u x t)) := by
        have hd : Tendsto (fun τ : ℝ => t + τ) (𝓝[>] 0) (𝓝 t) := by
          simpa using ((show Continuous (fun τ : ℝ => t + τ) by fun_prop).tendsto 0).mono_left
            (nhdsWithin_le_nhds (s := Ioi 0))
        exact (hheat x t ht).continuousAt.tendsto.comp hd
      apply le_of_tendsto_of_tendsto hlim hright
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact hcompare τ hτ
    · rw [heatKernelContinuous_zero D S t ht x y (Or.inr hy)]
      exact hnonneg x t ht
  · rw [heatKernelContinuous_zero D S t ht x y (Or.inl hx)]
    exact hnonneg x t ht





theorem dirichletExhaustionKernel_le_of_nonnegative_heat_solution
    (D : LeviCivitaData g) {Ω : ℕ → Set M}
    (S : ∀ j, Poincare.Manifold.SmoothDomain n (Ω j))
    {u : M → ℝ → ℝ} {y : M}
    (hcont : ContinuousOn (Function.uncurry u) (univ ×ˢ Ioi 0))
    (hspace : ∀ t, 0 < t → ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => u x t))
    (hheat : ∀ x t, 0 < t → HasDerivAt (u x)
      (D.laplacian (fun z => u z t) x) t)
    (hnonneg : ∀ x t, 0 < t → 0 ≤ u x t)
    (htrace : ∀ φ : M → ℝ, Continuous φ → HasCompactSupport φ →
      Tendsto (fun t => ∫ z, φ z * u z t ∂g.volumeMeasure)
        (𝓝[>] 0) (𝓝 (φ y)))
    {t : ℝ} (ht : 0 < t) (x : M) :
    dirichletExhaustionKernel (fun j => heatKernelContinuousTime D (S j)) t x y ≤
      u x t := by
  exact ciSup_le fun j => D.heatKernelContinuousTime_le_of_nonnegative_heat_solution
    (S j) hcont hspace hheat hnonneg htrace ht x

end PoincareConjecture.LeviCivitaData
