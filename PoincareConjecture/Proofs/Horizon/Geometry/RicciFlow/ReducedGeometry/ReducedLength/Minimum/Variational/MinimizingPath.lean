import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.LocalMinimality








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

namespace PoincareConjecture.ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem finite_chart_action_of_interior_regular {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (htime : ∀ s ∈ Icc (t 0) (t (Fin.last m)), T - s ^ 2 ∈ J)
    (hpotential : ContinuousOn
      (fun z : ℝ × M => 2 * z.1 ^ 2 * (F.connection (T - z.1 ^ 2)).scalarCurvature z.2)
      (Icc (t 0) (t (Fin.last m)) ×ˢ univ))
    (γ : ℝ → M) (hγ : ContinuousOn γ (Icc (t 0) (t (Fin.last m))))
    (hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Ioo (t 0) (t (Fin.last m))))
    (x : Fin m → M)
    (hsrc : ∀ i, MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source)
    (w : ∀ i : Fin m, IntervalL2 (EuclideanSpace ℝ (Fin n)) (t i.castSucc) (t i.succ))
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
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Ioo (t i.castSucc) (t i.succ)) :=
    hreg.mono (Ioo_subset_Ioo (ht (Fin.zero_le _)) (ht (Fin.le_last _)))
  have hv (i : Fin m) :
      (w i : ℝ → EuclideanSpace ℝ (Fin n)) =ᵐ[volume.restrict (Icc (t i.castSucc) (t i.succ))]
        deriv ((extChartAt (𝓡 n) (x i)) ∘ γ) := by
    filter_upwards [primitive_ae_hasDerivAt (hseg i)
      ((extChartAt (𝓡 n) (x i)) ∘ γ) (w i) (hprimitive i)] with s hs
    exact hs.deriv.symm
  have hV (i : Fin m) : ContinuousOn
      (fun s => 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (γ s))
      (Icc (t i.castSucc) (t i.succ)) :=
    (hpotential.comp (continuousOn_id.prodMk hγ) (fun s hs => ⟨hs, mem_univ _⟩)).mono (hsub i)
  have hint (i : Fin m) :
      IntervalIntegrable (regularizedLIntegrand F T γ) volume (t i.castSucc) (t i.succ) :=
    chart_piece_integrable F T (hseg i) (x i) γ (hγ.mono (hsub i)) (hreg' i)
      (hsrc i) (fun s hs => htime s (hsub i hs)) (hV i) (w i) (hv i)
  obtain ⟨hglobal, hsum⟩ := integrable_sum_fin_partition t (regularizedLIntegrand F T γ) hint
  refine ⟨hglobal, ?_⟩
  calc
    _ = ∑ i : Fin m, ∫ s in t i.castSucc..t i.succ, regularizedLIntegrand F T γ s := by
      apply Finset.sum_congr rfl
      intro i _
      exact chart_piece_action_eq F T (hseg i) (x i) γ (hreg' i) (hsrc i)
        (hV i) (hint i) (w i) (hv i)
    _ = _ := hsum

end PoincareConjecture.ReducedLengthMinimum.Variational

namespace PoincareConjecture.AncientKappaSolution

open ReducedLengthMinimum.Variational

variable {M : Type*} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [ConnectedSpace M]

theorem exists_minimizing_path_of_regular_chart_limit (K : AncientKappaSolution 2 M)
    {τ : ℝ} (hτ : 0 < τ) {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hta : t 0 = 0) (htb : t (Fin.last m) = Real.sqrt τ)
    (γ : ℝ → M) (hγ : ContinuousOn γ (Icc 0 (Real.sqrt τ)))
    (hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 2) 1 γ (Ioo 0 (Real.sqrt τ)))
    (x : Fin m → M)
    (hsrc : ∀ i, MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin 2)) (x i)).source)
    (w : ∀ i : Fin m, IntervalL2 (EuclideanSpace ℝ (Fin 2)) (t i.castSucc) (t i.succ))
    (hprimitive : ∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
      extChartAt (𝓡 2) (x i) (γ s) = extChartAt (𝓡 2) (x i) (γ (t i.castSucc)) +
        ∫ r in t i.castSucc..s, w i r)
    (hmin : (∑ i, chartH1Action K.flow 0 (x i) (t i.castSucc) (t i.succ) γ (w i)) ≤
      2 * Real.sqrt τ * K.spatialReducedLengthInfimum (γ 0) τ) :
    ∃ p : BackwardTimePath K.flow 0 0 τ,
      (∀ s, p.curve s = γ (Real.sqrt s)) ∧
      backwardLLength K.flow 0 0 τ p.curve =
        2 * Real.sqrt τ * K.spatialReducedLengthInfimum (γ 0) τ ∧
      ∀ q : BackwardTimePath K.flow 0 0 τ, q.curve 0 = γ 0 →
        backwardLLength K.flow 0 0 τ p.curve ≤ backwardLLength K.flow 0 0 τ q.curve := by
  have htime (s : ℝ) (_hs : s ∈ Icc (t 0) (t (Fin.last m))) :
      0 - s ^ 2 ∈ Iic (0 : ℝ) := sub_nonpos.mpr (sq_nonneg s)
  have hpot : ContinuousOn (fun z : ℝ × M =>
      2 * z.1 ^ 2 * (K.flow.connection (0 - z.1 ^ 2)).scalarCurvature z.2)
      (Icc (t 0) (t (Fin.last m)) ×ˢ univ) := by
    rw [hta, htb]
    exact K.regularizedPotential_continuousOn le_rfl (Real.sqrt_nonneg τ) univ
  obtain ⟨hint, hact⟩ := finite_chart_action_of_interior_regular K.flow 0 t ht htime hpot
    γ (by simpa only [hta, htb] using hγ) (by simpa only [hta, htb] using hreg)
    x hsrc w hprimitive
  have hback (r : ℝ) (hr : r ∈ Icc 0 τ) : 0 - r ∈ Iic (0 : ℝ) := sub_nonpos.mpr hr.1
  let p := backwardPathOfSqrt K.flow 0 0 τ le_rfl hτ (by simp) hback γ
    (by simpa only [Real.sqrt_zero] using hγ)
    (by simpa only [Real.sqrt_zero] using hreg)
    (by simpa only [hta, htb, Real.sqrt_zero] using hint)
  have hpact : backwardLLength K.flow 0 0 τ p.curve =
      ∑ i, chartH1Action K.flow 0 (x i) (t i.castSucc) (t i.succ) γ (w i) := by
    rw [backwardPathOfSqrt_action]
    simpa only [hta, htb, Real.sqrt_zero] using hact.symm
  have hbound (q : BackwardTimePath K.flow 0 0 τ) (hq : q.curve 0 = γ 0) :
      2 * Real.sqrt τ * K.spatialReducedLengthInfimum (γ 0) τ ≤
        backwardLLength K.flow 0 0 τ q.curve := by
    have hle := (K.spatialReducedLengthInfimum_le (γ 0) (q.curve τ) τ).trans
      (K.reducedLength_le_path q hq rfl)
    simpa only [mul_comm] using (le_div_iff₀ (show 0 < 2 * Real.sqrt τ by positivity)).mp hle
  have hpa : p.curve 0 = γ 0 := by change γ (Real.sqrt 0) = γ 0; rw [Real.sqrt_zero]
  have heq := le_antisymm (hpact.trans_le hmin) (hbound p hpa)
  exact ⟨p, fun _ => rfl, heq, fun q hq => heq.le.trans (hbound q hq)⟩

end PoincareConjecture.AncientKappaSolution
