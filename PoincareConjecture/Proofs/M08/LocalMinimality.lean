import PoincareConjecture.Proofs.M08.FiniteRecovery

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def chartH1Action {J : Set ℝ} (F : RicciFlow n M J) (T : ℝ)
    (x : M) (a b : ℝ) (γ : ℝ → M) (w : ChartL2 (EuclideanSpace ℝ (Fin n)) a b) : ℝ :=
  (∫ s in a..b, regularizedChartMetric F T x (s, γ s) (w s) (w s)) +
    ∫ s in a..b, 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (γ s)

theorem chart_piece_minimal [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u}) (hT : T ∈ J)
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₁ : 0 ≤ τ₁) (hordered : τ₁ < τ₂) (hτ₂ : τ₂ ≤ τmax)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hta : t 0 = Real.sqrt τ₁) (htb : t (Fin.last m) = Real.sqrt τ₂)
    (γ : ℝ → M) (hγ : ContinuousOn γ (Icc (t 0) (t (Fin.last m))))
    (x : Fin m → M)
    (hsrc : ∀ i, MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source)
    (w : ∀ i : Fin m, ChartL2 (EuclideanSpace ℝ (Fin n)) (t i.castSucc) (t i.succ))
    (hprimitive : ∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
      extChartAt (𝓡 n) (x i) (γ s) = extChartAt (𝓡 n) (x i) (γ (t i.castSucc)) +
        ∫ r in t i.castSucc..s, w i r)
    (hmin : (∑ i, chartH1Action F T (x i) (t i.castSucc) (t i.succ) γ (w i)) ≤
      sInf (backwardActionValues F T τ₁ τ₂ (γ (t 0)) (γ (t (Fin.last m)))))
    (j : Fin m) (ξ : ℝ → M)
    (hξ : ContinuousOn ξ (Icc (t j.castSucc) (t j.succ)))
    (hξa : ξ (t j.castSucc) = γ (t j.castSucc))
    (hξb : ξ (t j.succ) = γ (t j.succ))
    (hξsrc : MapsTo ξ (Icc (t j.castSucc) (t j.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x j)).source)
    (v : ChartL2 (EuclideanSpace ℝ (Fin n)) (t j.castSucc) (t j.succ))
    (hv : ∀ s ∈ Icc (t j.castSucc) (t j.succ),
      extChartAt (𝓡 n) (x j) (ξ s) = extChartAt (𝓡 n) (x j) (ξ (t j.castSucc)) +
        ∫ r in t j.castSucc..s, v r) :
    chartH1Action F T (x j) (t j.castSucc) (t j.succ) γ (w j) ≤
      chartH1Action F T (x j) (t j.castSucc) (t j.succ) ξ v := by
  classical
  let β : Fin m → ℝ → M := Function.update (fun _ ↦ γ) j ξ
  let v' : ∀ i : Fin m, ChartL2 (EuclideanSpace ℝ (Fin n)) (t i.castSucc) (t i.succ) :=
    Function.update w j v
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc (t 0) (t (Fin.last m)) :=
    Icc_subset_Icc (ht (Fin.zero_le _)) (ht (Fin.le_last _))
  have hβ (i : Fin m) : ContinuousOn (β i) (Icc (t i.castSucc) (t i.succ)) := by
    by_cases hij : i = j
    · subst i
      simpa only [β, Function.update_self] using hξ
    · simpa only [β, Function.update_of_ne hij] using hγ.mono (hsub i)
  have hβa (i : Fin m) : β i (t i.castSucc) = γ (t i.castSucc) := by
    by_cases hij : i = j
    · subst i
      simpa only [β, Function.update_self] using hξa
    · simp only [β, Function.update_of_ne hij]
  have hβb (i : Fin m) : β i (t i.succ) = γ (t i.succ) := by
    by_cases hij : i = j
    · subst i
      simpa only [β, Function.update_self] using hξb
    · simp only [β, Function.update_of_ne hij]
  have hβsrc (i : Fin m) : MapsTo (β i) (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source := by
    by_cases hij : i = j
    · subst i
      simpa only [β, Function.update_self] using hξsrc
    · simpa only [β, Function.update_of_ne hij] using hsrc i
  have hβprimitive (i : Fin m) (s : ℝ) (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      extChartAt (𝓡 n) (x i) (β i s) = extChartAt (𝓡 n) (x i) (β i (t i.castSucc)) +
        ∫ r in t i.castSucc..s, v' i r := by
    by_cases hij : i = j
    · subst i
      simpa only [β, v', Function.update_self] using hv s hs
    · simpa only [β, v', Function.update_of_ne hij] using hprimitive i s hs
  let A : Fin m → ℝ := fun i ↦ chartH1Action F T (x i) (t i.castSucc) (t i.succ) γ (w i)
  let B : Fin m → ℝ := fun i ↦ chartH1Action F T (x i) (t i.castSucc) (t i.succ) (β i) (v' i)
  have hineq : ∑ i, A i ≤ ∑ i, B i := hmin.trans
    (backwardInf_le_finite_chart_piece_action hM04 hT hwindow hcurvature hτ₁ hordered hτ₂
      t ht hta htb γ β hβ hβa hβb x hβsrc v' hβprimitive)
  have heq : ∑ i ∈ Finset.univ.erase j, B i = ∑ i ∈ Finset.univ.erase j, A i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [B, A, β, v', Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [← Finset.add_sum_erase Finset.univ A (Finset.mem_univ j),
    ← Finset.add_sum_erase Finset.univ B (Finset.mem_univ j), heq] at hineq
  simpa only [A, B, β, v', Function.update_self] using (add_le_add_iff_right _).mp hineq

end PoincareConjecture.M08
