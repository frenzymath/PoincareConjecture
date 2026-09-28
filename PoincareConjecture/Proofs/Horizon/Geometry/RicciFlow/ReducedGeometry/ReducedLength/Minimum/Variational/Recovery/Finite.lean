import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Recovery.Chart
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Recovery.Gluing
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Recovery.BackwardPath








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem regularizedLIntegrand_congr_eventually {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {α β : ℝ → M} {s : ℝ} (h : α =ᶠ[𝓝 s] β) :
    regularizedLIntegrand F T α s = regularizedLIntegrand F T β s := by
  have hd := h.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
  simp only [regularizedLIntegrand, curveVelocity, hd, h.eq_of_nhds]
  congr 2
  exact congrArg (fun x : M ↦ (F.metric (T - s ^ 2)).inner x
    ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) β s) 1)
    ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) β s) 1)) h.eq_of_nhds

theorem exists_smooth_finite_chart_piece_recovery {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (htime : ∀ s ∈ Icc (t 0) (t (Fin.last m)), T - s ^ 2 ∈ J)
    (hpotential : ContinuousOn
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2)
      (Icc (t 0) (t (Fin.last m)) ×ˢ univ))
    (γ : ℝ → M) (β : Fin m → ℝ → M)
    (hβ : ∀ i, ContinuousOn (β i) (Icc (t i.castSucc) (t i.succ)))
    (hβa : ∀ i, β i (t i.castSucc) = γ (t i.castSucc))
    (hβb : ∀ i, β i (t i.succ) = γ (t i.succ))
    (x : Fin m → M)
    (hsrc : ∀ i, MapsTo (β i) (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source)
    (w : ∀ i : Fin m, IntervalL2 (EuclideanSpace ℝ (Fin n)) (t i.castSucc) (t i.succ))
    (hprimitive : ∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
      extChartAt (𝓡 n) (x i) (β i s) = extChartAt (𝓡 n) (x i) (β i (t i.castSucc)) +
        ∫ r in t i.castSucc..s, w i r) :
    ∃ α : ℕ → ℝ → M,
      (∀ k, ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (α k) ∧
        α k (t 0) = γ (t 0) ∧ α k (t (Fin.last m)) = γ (t (Fin.last m)) ∧
        IntervalIntegrable (regularizedLIntegrand F T (α k)) volume (t 0) (t (Fin.last m))) ∧
      (∀ i, TendstoUniformlyOn α (β i) atTop (Icc (t i.castSucc) (t i.succ))) ∧
      Tendsto (fun k ↦ ∫ s in t 0..t (Fin.last m), regularizedLIntegrand F T (α k) s)
        atTop (𝓝 (∑ i, ((∫ s in t i.castSucc..t i.succ,
          regularizedChartMetric F T (x i) (s, β i s) (w i s) (w i s)) +
          ∫ s in t i.castSucc..t i.succ,
            2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (β i s)))) := by
  classical
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc (t 0) (t (Fin.last m)) :=
    Icc_subset_Icc (ht (Fin.zero_le _)) (ht (Fin.le_last _))
  choose f d hdLp K hK hKs hγK hf hlim hdlim using fun i : Fin m ↦
    smooth_chart_recovery (hseg i) (x i) (β i) (hβ i) (hsrc i) (w i) (hprimitive i)
  choose α hα hpieces hleft hright hleftgerm hrightgerm using fun k : ℕ ↦
    exists_smooth_fin_gluing m t ht γ (fun i ↦ f i k)
      (fun i ↦ (hf i k).1)
      (fun i s hs ↦ ((hf i k).2.2.2.2.2.1 s hs).trans (hβa i))
      (fun i s hs ↦ ((hf i k).2.2.2.2.2.2.1 s hs).trans (hβb i))
      (fun i ↦ (hf i k).2.2.2.1.trans (Eventually.of_forall (fun _ ↦ hβa i)))
      (fun i ↦ (hf i k).2.2.2.2.1.trans (Eventually.of_forall (fun _ ↦ hβb i)))
  have htime' (i : Fin m) (s : ℝ) (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      T - s ^ 2 ∈ J := htime s (hsub i hs)
  have hpotential' (i : Fin m) (S : Set M) : ContinuousOn
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2)
      (Icc (t i.castSucc) (t i.succ) ×ˢ S) :=
    hpotential.mono (fun _ hz => ⟨hsub i hz.1, mem_univ _⟩)
  have hfk (i : Fin m) (k : ℕ) : MapsTo (f i k) (Icc (t i.castSucc) (t i.succ)) (K i) :=
    (hf i k).2.2.2.2.2.2.2.1
  let v : ∀ i : Fin m, ℕ → IntervalL2 (EuclideanSpace ℝ (Fin n)) (t i.castSucc) (t i.succ) :=
    fun i k ↦ (hdLp i k).toLp (d i k)
  have hv (i : Fin m) (k : ℕ) :
      (v i k : ℝ → EuclideanSpace ℝ (Fin n)) =ᵐ[volume.restrict (Icc (t i.castSucc) (t i.succ))]
        deriv ((extChartAt (𝓡 n) (x i)) ∘ f i k) := by
    apply (hdLp i k).coeFn_toLp.trans
    exact Eventually.of_forall (fun s ↦ ((hf i k).2.2.2.2.2.2.2.2 s).deriv.symm)
  have hlocalint (i : Fin m) (k : ℕ) :
      IntervalIntegrable (regularizedLIntegrand F T (f i k)) volume (t i.castSucc) (t i.succ) :=
    chart_piece_integrable F T (hseg i) (x i) (f i k)
      (hf i k).1.continuous.continuousOn ((hf i k).1.of_le (by simp)).contMDiffOn
      (fun s hs ↦ hKs i (hfk i k hs)) (htime' i)
      ((hpotential' i (K i)).comp
        (continuousOn_id.prodMk (hf i k).1.continuous.continuousOn)
        (fun s hs => ⟨hs, hfk i k hs⟩)) (v i k) (hv i k)
  have hdensity (i : Fin m) (k : ℕ) :
      EqOn (regularizedLIntegrand F T (α k)) (regularizedLIntegrand F T (f i k))
        (Ioo (t i.castSucc) (t i.succ)) := by
    intro s hs
    apply regularizedLIntegrand_congr_eventually
    exact eventually_of_mem (isOpen_Ioo.mem_nhds hs)
      (fun r hr ↦ hpieces k i (Ioo_subset_Icc_self hr))
  have hpieceint (i : Fin m) (k : ℕ) :
      IntervalIntegrable (regularizedLIntegrand F T (α k)) volume (t i.castSucc) (t i.succ) := by
    apply (hlocalint i k).congr_uIoo
    intro s hs
    rw [uIoo_of_le (hseg i)] at hs
    exact (hdensity i k hs).symm
  have hint (k : ℕ) :
      IntervalIntegrable (regularizedLIntegrand F T (α k)) volume (t 0) (t (Fin.last m)) :=
    (integrable_sum_fin_partition t _ (fun i ↦ hpieceint i k)).1
  have haction (i : Fin m) (k : ℕ) :
      ((∫ s in t i.castSucc..t i.succ,
        regularizedChartMetric F T (x i) (s, f i k s) (v i k s) (v i k s)) +
        ∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (f i k s)) =
        ∫ s in t i.castSucc..t i.succ, regularizedLIntegrand F T (α k) s := by
    rw [chart_piece_action_eq F T (hseg i) (x i) (f i k)
      ((hf i k).1.of_le (by simp)).contMDiffOn
      (fun s hs ↦ hKs i (hfk i k hs))
      ((hpotential' i (K i)).comp
        (continuousOn_id.prodMk (hf i k).1.continuous.continuousOn)
        (fun s hs => ⟨hs, hfk i k hs⟩)) (hlocalint i k) (v i k) (hv i k)]
    exact intervalIntegral.integral_congr_Ioo_of_le (hseg i)
      (fun s hs ↦ (hdensity i k hs).symm)
  refine ⟨α, fun k ↦ ⟨hα k, hleft k _ le_rfl, hright k _ le_rfl, hint k⟩, ?_, ?_⟩
  · intro i
    exact (hlim i).congr (Eventually.of_forall (fun k s hs ↦ (hpieces k i hs).symm))
  · have hlocal (i : Fin m) := chart_piece_action_tendsto F T (hseg i) (x i)
      (hK i) (hKs i) (htime' i) (hpotential' i (K i)) (f i) (β i) (fun k ↦ (hf i k).1.continuous.continuousOn)
      (hβ i) (hfk i) (hγK i) (hlim i) (v i) (w i) (hdlim i)
    have hsum := tendsto_finsetSum Finset.univ (fun i _ ↦ hlocal i)
    have hsum_eq (k : ℕ) := (integrable_sum_fin_partition t _ (fun i ↦ hpieceint i k)).2
    simpa only [haction, hsum_eq] using hsum

theorem exists_smooth_finite_chart_recovery {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (htime : ∀ s ∈ Icc (t 0) (t (Fin.last m)), T - s ^ 2 ∈ J)
    (hpotential : ContinuousOn
      (fun z : ℝ × M => 2 * z.1 ^ 2 *
        (F.connection (T - z.1 ^ 2)).scalarCurvature z.2)
      (Icc (t 0) (t (Fin.last m)) ×ˢ univ))
    (γ : ℝ → M) (hγ : ContinuousOn γ (Icc (t 0) (t (Fin.last m))))
    (x : Fin m → M)
    (hsrc : ∀ i, MapsTo γ (Icc (t i.castSucc) (t i.succ))
      (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source)
    (w : ∀ i : Fin m, IntervalL2 (EuclideanSpace ℝ (Fin n)) (t i.castSucc) (t i.succ))
    (hprimitive : ∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
      extChartAt (𝓡 n) (x i) (γ s) = extChartAt (𝓡 n) (x i) (γ (t i.castSucc)) +
        ∫ r in t i.castSucc..s, w i r) :
    ∃ α : ℕ → ℝ → M,
      (∀ k, ContMDiff (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (α k) ∧
        α k (t 0) = γ (t 0) ∧ α k (t (Fin.last m)) = γ (t (Fin.last m)) ∧
        IntervalIntegrable (regularizedLIntegrand F T (α k)) volume (t 0) (t (Fin.last m))) ∧
      TendstoUniformlyOn α γ atTop (Icc (t 0) (t (Fin.last m))) ∧
      Tendsto (fun k ↦ ∫ s in t 0..t (Fin.last m), regularizedLIntegrand F T (α k) s)
        atTop (𝓝 (∑ i, ((∫ s in t i.castSucc..t i.succ,
          regularizedChartMetric F T (x i) (s, γ s) (w i s) (w i s)) +
          ∫ s in t i.castSucc..t i.succ,
            2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (γ s)))) := by
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc (t 0) (t (Fin.last m)) :=
    Icc_subset_Icc (ht (Fin.zero_le _)) (ht (Fin.le_last _))
  obtain ⟨α, hα, hlim, hact⟩ := exists_smooth_finite_chart_piece_recovery F T t ht
    htime hpotential γ (fun _ ↦ γ) (fun i ↦ hγ.mono (hsub i)) (fun _ ↦ rfl) (fun _ ↦ rfl)
    x hsrc w hprimitive
  refine ⟨α, hα, ?_, hact⟩
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hfinite : ∀ᶠ k in atTop, ∀ i : Fin m, ∀ s ∈ Icc (t i.castSucc) (t i.succ),
      dist (γ s) (α k s) < ε := by
    apply eventually_all.mpr
    intro i
    exact Metric.tendstoUniformlyOn_iff.mp (hlim i) ε hε
  filter_upwards [hfinite] with k hk s hs
  rcases mem_fin_partition t ht hs with rfl | ⟨i, hi⟩
  · simpa only [(hα k).2.1, dist_self] using hε
  · exact hk i s hi


end PoincareConjecture.ReducedLengthMinimum.Variational
