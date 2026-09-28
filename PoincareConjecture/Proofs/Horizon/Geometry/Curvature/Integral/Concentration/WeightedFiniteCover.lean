import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.FiniteCover








set_option autoImplicit false
open Set Filter MeasureTheory
namespace Poincare.CurvatureIntegral

theorem exists_subseq_fixed_member_integral_ratio_tendsto_atTop
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)] {ι : Type*} [Fintype ι]
    (μ : ∀ j, Measure (X j)) (U : ∀ j, Set (X j)) (V : ∀ j, ι → Set (X j))
    (h : ∀ j, X j → ℝ) (hU : ∀ j, MeasurableSet (U j))
    (hV : ∀ j i, MeasurableSet (V j i)) (hhn : ∀ j x, 0 ≤ h j x)
    (hUi : ∀ j, IntegrableOn (h j) (U j) (μ j))
    (hVi : ∀ j i, IntegrableOn (h j) (V j i) (μ j))
    (d : ℕ → ℝ) (hd : ∀ j, 0 < d j)
    (w : ℕ → ι → ℝ) (hw : ∀ j i, 0 < w j i) (hwd : ∀ j i, w j i ≤ d j)
    (C : ℝ) (houtside : ∀ j, (∫ x in U j \ ⋃ i, V j i, h j x ∂μ j) ≤ C * d j)
    (hlarge : ∀ B : ℝ, ∃ j, B < (∫ x in U j, h j x ∂μ j) / d j) :
    ∃ i : ι, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun j => (∫ x in V (phi j) i, h (phi j) x ∂μ (phi j)) /
        w (phi j) i) atTop atTop := by
  obtain ⟨i, phi, hphi, hdiv⟩ := exists_subseq_fixed_member_integral_tendsto_atTop
    μ U V (fun j x => h j x / d j) hU hV
    (fun j x => div_nonneg (hhn j x) (hd j).le)
    (fun j => (hUi j).div_const (d j))
    (fun j i => (hVi j i).div_const (d j)) C
    (by
      intro j
      rw [integral_div]
      exact (div_le_iff₀ (hd j)).mpr (houtside j))
    (by simpa only [integral_div] using hlarge)
  simp only [integral_div] at hdiv
  refine ⟨i, phi, hphi, tendsto_atTop_mono (fun j => ?_) hdiv⟩
  exact div_le_div_of_nonneg_left (integral_nonneg (fun x => hhn (phi j) x))
    (hw (phi j) i) (hwd (phi j) i)



theorem exists_subseq_fixed_member_weighted_integral_tendsto_atTop
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)] {ι : Type*} [Fintype ι]
    (μ : ∀ j, Measure (X j)) (U W : ∀ j, Set (X j)) (V : ∀ j, ι → Set (X j))
    (h K : ∀ j, X j → ℝ) (hU : ∀ j, MeasurableSet (U j))
    (hV : ∀ j i, MeasurableSet (V j i)) (hhn : ∀ j x, 0 ≤ h j x)
    (hKn : ∀ j x, 0 ≤ K j x)
    (hUi : ∀ j, IntegrableOn (h j) (U j) (μ j))
    (hVi : ∀ j i, IntegrableOn (h j) (V j i) (μ j))
    (hKi : ∀ j, IntegrableOn (K j) (W j) (μ j))
    (hVW : ∀ j i, V j i ⊆ W j)
    (C : ℝ) (houtside : ∀ j,
      (∫ x in U j \ ⋃ i, V j i, h j x ∂μ j) ≤ C * (1 + ∫ x in W j, K j x ∂μ j))
    (hlarge : ∀ B : ℝ, ∃ j,
      B < (∫ x in U j, h j x ∂μ j) / (1 + ∫ x in W j, K j x ∂μ j)) :
    ∃ i : ι, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun j => (∫ x in V (phi j) i, h (phi j) x ∂μ (phi j)) /
        (1 + ∫ x in V (phi j) i, K (phi j) x ∂μ (phi j))) atTop atTop := by
  apply exists_subseq_fixed_member_integral_ratio_tendsto_atTop
    μ U V h hU hV hhn hUi hVi
    (fun j => 1 + ∫ x in W j, K j x ∂μ j)
    (fun j => by
      have hn : 0 ≤ ∫ x in W j, K j x ∂μ j := integral_nonneg (hKn j)
      linarith)
    (fun j i => 1 + ∫ x in V j i, K j x ∂μ j)
    (fun j i => by
      have hn : 0 ≤ ∫ x in V j i, K j x ∂μ j := integral_nonneg (hKn j)
      linarith) ?_ C houtside hlarge
  intro j i
  apply add_le_add_right
  exact setIntegral_mono_set (hKi j) (Filter.Eventually.of_forall (hKn j))
    (Filter.Eventually.of_forall (fun _ hx => hVW j i hx))




theorem exists_subseq_nonempty_fixed_member_weighted_integral_tendsto_atTop
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)] {ι : Type*} [Fintype ι]
    (μ : ∀ j, Measure (X j)) (U W : ∀ j, Set (X j)) (V : ∀ j, ι → Set (X j))
    (h K : ∀ j, X j → ℝ) (hU : ∀ j, MeasurableSet (U j))
    (hV : ∀ j i, MeasurableSet (V j i)) (hhn : ∀ j x, 0 ≤ h j x)
    (hKn : ∀ j x, 0 ≤ K j x)
    (hUi : ∀ j, IntegrableOn (h j) (U j) (μ j))
    (hVi : ∀ j i, IntegrableOn (h j) (V j i) (μ j))
    (hKi : ∀ j, IntegrableOn (K j) (W j) (μ j))
    (hVW : ∀ j i, V j i ⊆ W j)
    (C : ℝ) (houtside : ∀ j,
      (∫ x in U j \ ⋃ i, V j i, h j x ∂μ j) ≤ C * (1 + ∫ x in W j, K j x ∂μ j))
    (hlarge : ∀ B : ℝ, ∃ j,
      B < (∫ x in U j, h j x ∂μ j) / (1 + ∫ x in W j, K j x ∂μ j)) :
    ∃ i : ι, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      (∀ j, (V (phi j) i).Nonempty) ∧
      Tendsto (fun j => (∫ x in V (phi j) i, h (phi j) x ∂μ (phi j)) /
        (1 + ∫ x in V (phi j) i, K (phi j) x ∂μ (phi j))) atTop atTop := by
  obtain ⟨i, phi, hphi, hdiv⟩ :=
    exists_subseq_fixed_member_weighted_integral_tendsto_atTop
      μ U W V h K hU hV hhn hKn hUi hVi hKi hVW C houtside hlarge
  obtain ⟨J, hJ⟩ := eventually_atTop.mp (hdiv.eventually (eventually_gt_atTop 0))
  refine ⟨i, fun j => phi (j + J), fun a b hab => hphi (Nat.add_lt_add_right hab J),
    ?_, hdiv.comp (tendsto_add_atTop_nat J)⟩
  intro j
  rcases (V (phi (j + J)) i).eq_empty_or_nonempty with he | he
  · have hj := hJ (j + J) (by omega)
    rw [he, setIntegral_empty, zero_div] at hj
    exact False.elim ((lt_irrefl 0) hj)
  · exact he

end Poincare.CurvatureIntegral
