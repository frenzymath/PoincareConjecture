import PoincareConjecture.Proofs.M08.LocalMinimality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M]

theorem finite_chart_action_of_interior_regular {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (htime : ∀ s ∈ Icc (t 0) (t (Fin.last m)), T - s ^ 2 ∈ J)
    (γ : ℝ → M) (hγ : ContinuousOn γ (Icc (t 0) (t (Fin.last m))))
    (hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Ioo (t 0) (t (Fin.last m))))
    (x : Fin m → M)
    (hsrc : ∀ i, MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source)
    (w : ∀ i : Fin m, ChartL2 (EuclideanSpace ℝ (Fin n)) (t i.castSucc) (t i.succ))
    (hprimitive : ∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
      extChartAt (𝓡 n) (x i) (γ s) = extChartAt (𝓡 n) (x i) (γ (t i.castSucc)) +
        ∫ r in t i.castSucc..s, w i r) :
    IntervalIntegrable (regularizedLIntegrand F T γ) volume (t 0) (t (Fin.last m)) ∧
      (∑ i, chartH1Action F T (x i) (t i.castSucc) (t i.succ) γ (w i)) =
        ∫ s in t 0..t (Fin.last m), regularizedLIntegrand F T γ s := by
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc (t 0) (t (Fin.last m)) :=
    Icc_subset_Icc (ht (Fin.zero_le _)) (ht (Fin.le_last _))
  have hreg' (i : Fin m) :
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Ioo (t i.castSucc) (t i.succ)) := by
    apply hreg.mono
    intro s hs
    exact ⟨(ht (Fin.zero_le _)).trans_lt hs.1, hs.2.trans_le (ht (Fin.le_last _))⟩
  have hv (i : Fin m) :
      (w i : ℝ → EuclideanSpace ℝ (Fin n)) =ᵐ[volume.restrict (Icc (t i.castSucc) (t i.succ))]
        deriv ((extChartAt (𝓡 n) (x i)) ∘ γ) := by
    filter_upwards [chart_primitive_ae_hasDerivAt (hseg i)
      ((extChartAt (𝓡 n) (x i)) ∘ γ) (w i) (hprimitive i)] with s hs
    exact hs.deriv.symm
  have hint (i : Fin m) :
      IntervalIntegrable (regularizedLIntegrand F T γ) volume (t i.castSucc) (t i.succ) :=
    chart_piece_integrable F hM04 T (hseg i) (x i) γ (hγ.mono (hsub i)) (hreg' i)
      (hsrc i) (fun s hs ↦ htime s (hsub i hs)) (w i) (hv i)
  obtain ⟨hglobal, hsum⟩ := integrable_sum_fin_partition t (regularizedLIntegrand F T γ) hint
  refine ⟨hglobal, ?_⟩
  calc
    _ = ∑ i : Fin m, ∫ s in t i.castSucc..t i.succ, regularizedLIntegrand F T γ s := by
      apply Finset.sum_congr rfl
      intro i hi
      exact chart_piece_action_eq F hM04 T (hseg i) (x i) γ (hγ.mono (hsub i))
        (hreg' i) (hsrc i) (fun s hs ↦ htime s (hsub i hs)) (hint i) (w i) (hv i)
    _ = _ := hsum

theorem exists_minimizing_backward_path_of_chart_limit {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u}) (hT : T ∈ J)
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₁ : 0 ≤ τ₁) (hordered : τ₁ < τ₂) (hτ₂ : τ₂ ≤ τmax)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hta : t 0 = Real.sqrt τ₁) (htb : t (Fin.last m) = Real.sqrt τ₂)
    (γ : ℝ → M) (hγ : ContinuousOn γ (Icc (t 0) (t (Fin.last m))))
    (hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Ioo (t 0) (t (Fin.last m))))
    (p₁ p₂ : M) (hγa : γ (Real.sqrt τ₁) = p₁) (hγb : γ (Real.sqrt τ₂) = p₂)
    (x : Fin m → M)
    (hsrc : ∀ i, MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source)
    (w : ∀ i : Fin m, ChartL2 (EuclideanSpace ℝ (Fin n)) (t i.castSucc) (t i.succ))
    (hprimitive : ∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
      extChartAt (𝓡 n) (x i) (γ s) = extChartAt (𝓡 n) (x i) (γ (t i.castSucc)) +
        ∫ r in t i.castSucc..s, w i r)
    (hmin : (∑ i, chartH1Action F T (x i) (t i.castSucc) (t i.succ) γ (w i)) ≤
      sInf (backwardActionValues F T τ₁ τ₂ p₁ p₂)) :
    ∃ p : BackwardTimePath F T τ₁ τ₂,
      p.curve τ₁ = p₁ ∧ p.curve τ₂ = p₂ ∧ IsMinimizingBackwardLPath F T τ₁ τ₂ p ∧
        backwardLLength F T τ₁ τ₂ p.curve = sInf (backwardActionValues F T τ₁ τ₂ p₁ p₂) ∧
          ∀ τ, p.curve τ = γ (Real.sqrt τ) := by
  have htime (τ : ℝ) (hτ : τ ∈ Icc τ₁ τ₂) : T - τ ∈ J :=
    hwindow (backwardTime_mem_window hτ₁ hτ₂ hτ)
  have htimesq (s : ℝ) (hs : s ∈ Icc (t 0) (t (Fin.last m))) : T - s ^ 2 ∈ J := by
    rw [hta, htb] at hs
    have hsn : 0 ≤ s := (Real.sqrt_nonneg τ₁).trans hs.1
    apply htime
    constructor
    · simpa only [Real.sq_sqrt hτ₁] using
        (sq_le_sq₀ (Real.sqrt_nonneg τ₁) hsn).mpr hs.1
    · simpa only [Real.sq_sqrt (hτ₁.trans hordered.le)] using
        (sq_le_sq₀ hsn (Real.sqrt_nonneg τ₂)).mpr hs.2
  obtain ⟨hint, hact⟩ :=
    finite_chart_action_of_interior_regular F hM04 T t ht htimesq γ hγ hreg x hsrc w hprimitive
  have hcont : ContinuousOn γ (Icc (Real.sqrt τ₁) (Real.sqrt τ₂)) := by
    simpa only [hta, htb] using hγ
  have hregular : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ
      (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) := by
    simpa only [hta, htb] using hreg
  have hintegrable : IntervalIntegrable (regularizedLIntegrand F T γ) volume
      (Real.sqrt τ₁) (Real.sqrt τ₂) := by
    simpa only [hta, htb] using hint
  let p := backwardPathOfSqrt F T τ₁ τ₂ hτ₁ hordered hT htime γ hcont hregular hintegrable
  have hpa : p.curve τ₁ = p₁ := hγa
  have hpb : p.curve τ₂ = p₂ := hγb
  have hpact : backwardLLength F T τ₁ τ₂ p.curve =
      ∑ i, chartH1Action F T (x i) (t i.castSucc) (t i.succ) γ (w i) := by
    rw [backwardPathOfSqrt_action]
    simpa only [regularizedLAction, hta, htb] using hact.symm
  have hple : backwardLLength F T τ₁ τ₂ p.curve ≤
      sInf (backwardActionValues F T τ₁ τ₂ p₁ p₂) := hpact.trans_le hmin
  have hbdd : BddBelow (backwardActionValues F T τ₁ τ₂ p₁ p₂) :=
    backwardActionValues_bddBelow hM04 hcurvature hτ₂ p₁ p₂
  have hpeq : backwardLLength F T τ₁ τ₂ p.curve =
      sInf (backwardActionValues F T τ₁ τ₂ p₁ p₂) :=
    le_antisymm hple (csInf_le hbdd ⟨p, hpa, hpb, rfl⟩)
  refine ⟨p, hpa, hpb, ?_, hpeq, fun _ ↦ rfl⟩
  intro q hqa hqb
  exact hple.trans (csInf_le hbdd ⟨q, hqa.trans hpa, hqb.trans hpb, rfl⟩)

end PoincareConjecture.M08
