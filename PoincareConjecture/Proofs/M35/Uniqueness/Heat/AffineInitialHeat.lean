import PoincareConjecture.Proofs.M35.Uniqueness.Heat.WeakValuePathEquation
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.SmoothAffineInverse
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.ValueInitial.FormPrimitive










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace PoincareConjecture.M35.Uniqueness.Heat

open SpectralHeatNative ValueInitial

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [SeparableSpace H]

def homogeneousInitialLp (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T) (u₀ : H) :
    Lp V 2 (timeMeasure T) :=
  (initialFormPath_memLp J hc hd hi hn hT u₀).toLp (initialFormPath J hc hd hi hn u₀)

def affineInitialForm (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (M : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (F : Lp V 2 (timeMeasure T)) (u₀ : H) : Lp V 2 (timeMeasure T) :=
  affineResponse ((formWeakHeatOperator J hc hd hi hn hT).comp M)
    (formWeakHeatOperator J hc hd hi hn hT F + homogeneousInitialLp J hc hd hi hn hT u₀)

def affineInitialValue (J : V →L[ℝ] H) (hc : IsCompactOperator J) (hd : DenseRange J)
    (hi : Function.Injective J) (hn : ‖J‖ ≤ 1) {T : ℝ} (hT : 0 ≤ T)
    (M : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (F : Lp V 2 (timeMeasure T)) (u₀ : H) (t : ℝ) : H :=
  weakValueFunction J hc hd hi hn hT (M (affineInitialForm J hc hd hi hn hT M F u₀) + F) t +
    initialValuePath J hc hd hn u₀ t

theorem affineInitialForm_fixedPoint (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T)
    (M : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (hM : ‖(formWeakHeatOperator J hc hd hi hn hT).comp M‖ < 1)
    (F : Lp V 2 (timeMeasure T)) (u₀ : H) :
    affineInitialForm J hc hd hi hn hT M F u₀ =
      formWeakHeatOperator J hc hd hi hn hT (M (affineInitialForm J hc hd hi hn hT M F u₀) + F) +
        homogeneousInitialLp J hc hd hi hn hT u₀ := by
  have he := affineResponse_equation ((formWeakHeatOperator J hc hd hi hn hT).comp M) hM
    (formWeakHeatOperator J hc hd hi hn hT F + homogeneousInitialLp J hc hd hi hn hT u₀)
  simpa only [affineInitialForm, ContinuousLinearMap.comp_apply, map_add, add_assoc] using he

theorem affineInitialValue_solution (J : V →L[ℝ] H) (hc : IsCompactOperator J)
    (hd : DenseRange J) (hi : Function.Injective J) (hn : ‖J‖ ≤ 1)
    {T : ℝ} (hT : 0 ≤ T)
    (M : Lp V 2 (timeMeasure T) →L[ℝ] Lp V 2 (timeMeasure T))
    (hM : ‖(formWeakHeatOperator J hc hd hi hn hT).comp M‖ < 1)
    (F : Lp V 2 (timeMeasure T)) (u₀ : H) :
    let v := affineInitialForm J hc hd hi hn hT M F u₀
    let U := affineInitialValue J hc hd hi hn hT M F u₀
    U 0 = u₀ ∧ ContinuousOn U (Icc 0 T) ∧
      (∀ᵐ t ∂timeMeasure T, J (v t) = U t) ∧
      ∀ t ∈ Icc 0 T, J.adjoint (U t) = J.adjoint u₀ +
        ∫ s in (0 : ℝ)..t, (M v + F) s - v s + J.adjoint (J (v s)) := by
  let v := affineInitialForm J hc hd hi hn hT M F u₀
  let G := M v + F
  let w := formWeakHeatOperator J hc hd hi hn hT G
  let p := initialFormPath J hc hd hi hn u₀
  let W := initialValuePath J hc hd hn u₀
  have hp := initialFormPath_memLp J hc hd hi hn hT u₀
  have hv : v = w + homogeneousInitialLp J hc hd hi hn hT u₀ :=
    affineInitialForm_fixedPoint J hc hd hi hn hT M hM F u₀
  have hvt : ∀ᵐ t ∂timeMeasure T, v t = w t + p t := by
    rw [hv]
    filter_upwards [Lp.coeFn_add w (homogeneousInitialLp J hc hd hi hn hT u₀),
      hp.coeFn_toLp] with t ht hp'
    change homogeneousInitialLp J hc hd hi hn hT u₀ t = p t at hp'
    rw [ht, Pi.add_apply, hp']
  have hZ := weakValueFunction_spec J hc hd hi hn hT G
  have hpW := initialFormPath_graph J hc hd hi hn hT u₀
  change ∀ᵐ t ∂timeMeasure T, J (p t) = W t at hpW
  refine ⟨?_, hZ.2.1.add (initialValuePath_continuous J hc hd hn u₀).continuousOn, ?_, ?_⟩
  · change weakValueFunction J hc hd hi hn hT G 0 + W 0 = u₀
    rw [hZ.1, zero_add]
    exact initialValuePath_zero J hc hd hn u₀
  · filter_upwards [hvt, hZ.2.2.1, hpW] with t ht hz hp'
    rw [ht, map_add, hz, hp']
    rfl
  · intro t ht
    let E₀ : ℝ → V := fun s => G s - w s + J.adjoint (J (w s))
    let E₁ : ℝ → V := fun s => -p s + J.adjoint (W s)
    have hE₀ : MemLp E₀ 2 (timeMeasure T) :=
      ((Lp.memLp G).sub (Lp.memLp w)).add
        (J.adjoint.comp_memLp' (J.comp_memLp' (Lp.memLp w)))
    have hE₁ : MemLp E₁ 2 (timeMeasure T) := hp.neg.add
      (J.adjoint.comp_memLp' (initialValuePath_memLp J hc hd hi hn hT u₀))
    have hint (f : ℝ → V) (hf : MemLp f 2 (timeMeasure T)) :
        IntervalIntegrable f volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1).mpr
        ((show IntegrableOn f (Ioc 0 T) volume from hf.integrable (by norm_num)).mono_set
          (Ioc_subset_Ioc le_rfl ht.2))
    change J.adjoint (weakValueFunction J hc hd hi hn hT G t + W t) = _
    rw [map_add, weakValueFunction_integral J hc hd hi hn hT G ht,
      initialValuePath_integral J hc hd hi hn hT u₀ ht]
    have he : (∫ s in (0 : ℝ)..t, E₀ s) +
        (J.adjoint u₀ + ∫ s in (0 : ℝ)..t, E₁ s) =
      J.adjoint u₀ + ∫ s in (0 : ℝ)..t, E₀ s + E₁ s := by
      rw [intervalIntegral.integral_add (hint E₀ hE₀) (hint E₁ hE₁)]
      abel
    rw [he]
    congr 1
    apply intervalIntegral.integral_congr_ae_restrict
    rw [uIoc_of_le ht.1]
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2) hvt,
      ae_restrict_of_ae_restrict_of_subset (Ioc_subset_Ioc le_rfl ht.2) hpW] with s hv' hp'
    dsimp only [E₀, E₁]
    rw [hv', ← hp', map_add, map_add]
    dsimp only [G, v]
    abel

end PoincareConjecture.M35.Uniqueness.Heat
