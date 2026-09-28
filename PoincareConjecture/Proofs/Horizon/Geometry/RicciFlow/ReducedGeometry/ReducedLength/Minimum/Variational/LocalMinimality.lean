import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Recovery.Ancient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Regularity.Action
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Sequence.Infimum









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum.Variational

variable {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ConnectedSpace M]

theorem chart_piece_minimal (K : AncientKappaSolution 2 M)
    {τ : ℝ} (hτ : 0 < τ)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hta : t 0 = 0) (htb : t (Fin.last m) = Real.sqrt τ)
    (γ : ℝ → M) (hγ : ContinuousOn γ (Icc (t 0) (t (Fin.last m))))
    (x : Fin m → M)
    (hsrc : ∀ i, MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source)
    (w : ∀ i : Fin m, IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t i.castSucc) (t i.succ))
    (hprimitive : ∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
      extChartAt (𝓡 2) (x i) (γ s) = extChartAt (𝓡 2) (x i) (γ (t i.castSucc)) +
        ∫ r in t i.castSucc..s, w i r)
    (hmin : (∑ i, chartH1Action K.flow 0 (x i) (t i.castSucc) (t i.succ) γ (w i)) ≤
      2 * Real.sqrt τ * K.spatialReducedLengthInfimum (γ 0) τ)
    (j : Fin m) (ξ : ℝ → M)
    (hξ : ContinuousOn ξ (Icc (t j.castSucc) (t j.succ)))
    (hξa : ξ (t j.castSucc) = γ (t j.castSucc))
    (hξb : ξ (t j.succ) = γ (t j.succ))
    (hξsrc : MapsTo ξ (Icc (t j.castSucc) (t j.succ))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x j)).source)
    (v : IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t j.castSucc) (t j.succ))
    (hv : ∀ s ∈ Icc (t j.castSucc) (t j.succ),
      extChartAt (𝓡 2) (x j) (ξ s) = extChartAt (𝓡 2) (x j) (ξ (t j.castSucc)) +
        ∫ r in t j.castSucc..s, v r) :
    chartH1Action K.flow 0 (x j) (t j.castSucc) (t j.succ) γ (w j) ≤
      chartH1Action K.flow 0 (x j) (t j.castSucc) (t j.succ) ξ v := by
  classical
  let β : Fin m → ℝ → M := Function.update (fun _ => γ) j ξ
  let v' : ∀ i : Fin m, IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t i.castSucc) (t i.succ) :=
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
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source := by
    by_cases hij : i = j
    · subst i
      simpa only [β, Function.update_self] using hξsrc
    · simpa only [β, Function.update_of_ne hij] using hsrc i
  have hβprimitive (i : Fin m) (s : ℝ) (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      extChartAt (𝓡 2) (x i) (β i s) = extChartAt (𝓡 2) (x i) (β i (t i.castSucc)) +
        ∫ r in t i.castSucc..s, v' i r := by
    by_cases hij : i = j
    · subst i
      simpa only [β, v', Function.update_self] using hv s hs
    · simpa only [β, v', Function.update_of_ne hij] using hprimitive i s hs
  let A : Fin m → ℝ := fun i => chartH1Action K.flow 0 (x i) (t i.castSucc) (t i.succ) γ (w i)
  let B : Fin m → ℝ := fun i => chartH1Action K.flow 0 (x i) (t i.castSucc) (t i.succ) (β i) (v' i)
  have hineq : ∑ i, A i ≤ ∑ i, B i := by
    apply hmin.trans
    apply (mul_le_mul_of_nonneg_left
      (K.spatialReducedLengthInfimum_le (γ 0) (γ (Real.sqrt τ)) τ)
      (show 0 ≤ 2 * Real.sqrt τ by positivity)).trans
    exact K.reducedLength_le_finite_chart_piece_action hτ t ht hta htb γ β
      hβ hβa hβb x hβsrc v' hβprimitive
  have heq : ∑ i ∈ Finset.univ.erase j, B i = ∑ i ∈ Finset.univ.erase j, A i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [B, A, β, v', Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [← Finset.add_sum_erase Finset.univ A (Finset.mem_univ j),
    ← Finset.add_sum_erase Finset.univ B (Finset.mem_univ j), heq] at hineq
  simpa only [A, B, β, v', Function.update_self] using (add_le_add_iff_right _).mp hineq

end PoincareConjecture.AncientKappaSolution
