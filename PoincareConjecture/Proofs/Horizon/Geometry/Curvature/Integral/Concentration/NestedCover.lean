import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.FiniteCover








set_option autoImplicit false

open Set Filter MeasureTheory
open scoped BigOperators

namespace Poincare.CurvatureIntegral



theorem exists_fixed_member_integral_unbounded_all_scales
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)] {ι : Type*} [Fintype ι]
    (μ : ∀ j, Measure (X j)) (U : ∀ j, Set (X j))
    (V : ∀ j, ℕ → ι → Set (X j)) (h : ∀ j, X j → ℝ)
    (hU : ∀ j, MeasurableSet (U j)) (hV : ∀ j k i, MeasurableSet (V j k i))
    (hhn : ∀ j x, 0 ≤ h j x) (hUi : ∀ j, IntegrableOn (h j) (U j) (μ j))
    (hVi : ∀ j k i, IntegrableOn (h j) (V j k i) (μ j))
    (hnested : ∀ j i, Antitone (fun k => V j k i))
    (C : ℕ → ℝ)
    (houtside : ∀ k j, (∫ x in U j \ ⋃ i, V j k i, h j x ∂μ j) ≤ C k)
    (hlarge : ∀ B : ℝ, ∃ j, B < ∫ x in U j, h j x ∂μ j) :
    ∃ i : ι, ∀ k, ∀ B : ℝ, ∃ j, B < ∫ x in V j k i, h j x ∂μ j := by
  classical
  by_contra hb
  push Not at hb
  choose k b hb using hb
  let K := Finset.univ.sup k
  have hiK (i : ι) : k i ≤ K := Finset.le_sup (Finset.mem_univ i)
  obtain ⟨j, hj⟩ := hlarge (C K + ∑ i, b i)
  have hmono (i : ι) : (∫ x in V j K i, h j x ∂μ j) ≤ b i := by
    apply le_trans _ (hb i j)
    exact setIntegral_mono_set (hVi j (k i) i)
      (Eventually.of_forall (hhn j))
      (Eventually.of_forall (fun _ hx => hnested j i (hiK i) hx))
  have hcover := integral_le_complement_add_sum (hU j) (V j K) (hV j K)
    (hhn j) (hUi j) (hVi j K)
  exact (not_le_of_gt hj) (hcover.trans (add_le_add (houtside K j)
    (Finset.sum_le_sum (fun i _ => hmono i))))



theorem exists_subseq_fixed_member_integral_tendsto_atTop_at_scales
    {X : ℕ → Type*} [∀ j, MeasurableSpace (X j)] {ι : Type*} [Fintype ι]
    (μ : ∀ j, Measure (X j)) (U : ∀ j, Set (X j))
    (V : ∀ j, ℕ → ι → Set (X j)) (h : ∀ j, X j → ℝ)
    (hU : ∀ j, MeasurableSet (U j)) (hV : ∀ j k i, MeasurableSet (V j k i))
    (hhn : ∀ j x, 0 ≤ h j x) (hUi : ∀ j, IntegrableOn (h j) (U j) (μ j))
    (hVi : ∀ j k i, IntegrableOn (h j) (V j k i) (μ j))
    (hnested : ∀ j i, Antitone (fun k => V j k i))
    (C : ℕ → ℝ)
    (houtside : ∀ k j, (∫ x in U j \ ⋃ i, V j k i, h j x ∂μ j) ≤ C k)
    (hlarge : ∀ B : ℝ, ∃ j, B < ∫ x in U j, h j x ∂μ j)
    (scale : ℕ → ℕ) :
    ∃ i : ι, ∃ phi : ℕ → ℕ, StrictMono phi ∧
      Tendsto (fun j => ∫ x in V (phi j) (scale j) i,
        h (phi j) x ∂μ (phi j)) atTop atTop := by
  obtain ⟨i, hi⟩ := exists_fixed_member_integral_unbounded_all_scales
    μ U V h hU hV hhn hUi hVi hnested C houtside hlarge
  obtain ⟨phi, hphi, hvalue⟩ := exists_strictMono_above_thresholds_family
    (fun k j => ∫ x in V j (scale k) i, h j x ∂μ j) (fun k => (k : ℝ))
    (fun k => hi (scale k))
  exact ⟨i, phi, hphi, tendsto_atTop_mono (fun j => (hvalue j).le)
    tendsto_natCast_atTop_atTop⟩

end Poincare.CurvatureIntegral
