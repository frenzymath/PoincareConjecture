import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Recovery.Finite
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.CompactTime








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum.Variational

variable {M : Type u} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ConnectedSpace M]



theorem reducedLength_le_finite_chart_piece_action (K : AncientKappaSolution 2 M)
    {τ : ℝ} (hτ : 0 < τ)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hta : t 0 = 0) (htb : t (Fin.last m) = Real.sqrt τ)
    (γ : ℝ → M) (β : Fin m → ℝ → M)
    (hβ : ∀ i, ContinuousOn (β i) (Icc (t i.castSucc) (t i.succ)))
    (hβa : ∀ i, β i (t i.castSucc) = γ (t i.castSucc))
    (hβb : ∀ i, β i (t i.succ) = γ (t i.succ))
    (x : Fin m → M)
    (hsrc : ∀ i, MapsTo (β i) (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source)
    (w : ∀ i : Fin m, IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t i.castSucc) (t i.succ))
    (hprimitive : ∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
      extChartAt (𝓡 2) (x i) (β i s) = extChartAt (𝓡 2) (x i) (β i (t i.castSucc)) +
        ∫ r in t i.castSucc..s, w i r) :
    2 * Real.sqrt τ * reducedLength K.flow 0 (γ 0) (γ (Real.sqrt τ)) τ ≤
      ∑ i, ((∫ s in t i.castSucc..t i.succ,
        regularizedChartMetric K.flow 0 (x i) (s, β i s) (w i s) (w i s)) +
        ∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * (K.flow.connection (0 - s ^ 2)).scalarCurvature (β i s)) := by
  have htime (s : ℝ) (_hs : s ∈ Icc (t 0) (t (Fin.last m))) :
      0 - s ^ 2 ∈ Iic (0 : ℝ) := by simp only [mem_Iic]; nlinarith [sq_nonneg s]
  have hpotential : ContinuousOn (fun z : ℝ × M =>
      2 * z.1 ^ 2 * (K.flow.connection (0 - z.1 ^ 2)).scalarCurvature z.2)
      (Icc (t 0) (t (Fin.last m)) ×ˢ univ) := by
    rw [hta, htb]
    exact K.regularizedPotential_continuousOn le_rfl (Real.sqrt_nonneg τ) univ
  obtain ⟨α, hα, _, hlim⟩ := exists_smooth_finite_chart_piece_recovery K.flow 0 t ht htime
    hpotential γ β hβ hβa hβb x hsrc w hprimitive
  have hcont (k : ℕ) : ContinuousOn (α k) (Icc (Real.sqrt 0) (Real.sqrt τ)) :=
    (hα k).1.continuous.continuousOn
  have hreg (k : ℕ) : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) 1 (α k)
      (Ioo (Real.sqrt 0) (Real.sqrt τ)) := ((hα k).1.of_le (by simp)).contMDiffOn
  have hint (k : ℕ) : IntervalIntegrable (regularizedLIntegrand K.flow 0 (α k)) volume
      (Real.sqrt 0) (Real.sqrt τ) := by
    simpa only [hta, htb, Real.sqrt_zero] using (hα k).2.2.2
  have hback (r : ℝ) (hr : r ∈ Icc 0 τ) : 0 - r ∈ Iic (0 : ℝ) := by
    simpa only [mem_Iic, sub_nonpos] using hr.1
  let paths : ℕ → BackwardTimePath K.flow 0 0 τ := fun k =>
    backwardPathOfSqrt K.flow 0 0 τ le_rfl hτ (by simp) hback
      (α k) (hcont k) (hreg k) (hint k)
  have hstart (k : ℕ) : (paths k).curve 0 = γ 0 := by
    change α k (Real.sqrt 0) = γ 0
    simpa only [Real.sqrt_zero, hta] using (hα k).2.1
  have hend (k : ℕ) : (paths k).curve τ = γ (Real.sqrt τ) := by
    change α k (Real.sqrt τ) = γ (Real.sqrt τ)
    simpa only [htb] using (hα k).2.2.1
  have haction (k : ℕ) : backwardLLength K.flow 0 0 τ (paths k).curve =
      ∫ s in t 0..t (Fin.last m), regularizedLIntegrand K.flow 0 (α k) s := by
    rw [backwardPathOfSqrt_action]
    simp only [hta, htb, Real.sqrt_zero]
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro k
  have h := (le_div_iff₀ (show 0 < 2 * Real.sqrt τ by positivity)).mp
    (K.reducedLength_le_path (paths k) (hstart k) (hend k))
  simpa only [haction, mul_comm] using h


theorem reducedLength_le_finite_chart_action (K : AncientKappaSolution 2 M)
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
        ∫ r in t i.castSucc..s, w i r) :
    2 * Real.sqrt τ * reducedLength K.flow 0 (γ 0) (γ (Real.sqrt τ)) τ ≤
      ∑ i, ((∫ s in t i.castSucc..t i.succ,
        regularizedChartMetric K.flow 0 (x i) (s, γ s) (w i s) (w i s)) +
        ∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * (K.flow.connection (0 - s ^ 2)).scalarCurvature (γ s)) := by
  exact K.reducedLength_le_finite_chart_piece_action hτ t ht hta htb γ (fun _ => γ)
    (fun i => hγ.mono (Icc_subset_Icc (ht (Fin.zero_le _)) (ht (Fin.le_last _))))
    (fun _ => rfl) (fun _ => rfl) x hsrc w hprimitive

end PoincareConjecture.AncientKappaSolution
