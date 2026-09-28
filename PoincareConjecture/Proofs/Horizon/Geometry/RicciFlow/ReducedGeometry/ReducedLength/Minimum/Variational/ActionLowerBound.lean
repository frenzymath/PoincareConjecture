import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.ChartEnergy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.ChartCover
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.LowerSemicontinuity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.Action

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral ENNReal

universe u

namespace PoincareConjecture.ReducedLengthMinimum.Variational

theorem sum_integral_fin_partition {m : ℕ} (t : Fin (m + 1) → ℝ)
    (ht : Monotone t) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (t 0) (t (Fin.last m))) :
    (∑ i : Fin m, ∫ s in t i.castSucc..t i.succ, f s) =
      ∫ s in t 0..t (Fin.last m), f s := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    have hfirst : IntervalIntegrable f volume (t 0) (t (Fin.last m).castSucc) :=
      hf.mono_set (by
        rw [uIcc_of_le (ht (Fin.zero_le _)),
          uIcc_of_le (ht (Fin.zero_le _))]
        exact Icc_subset_Icc le_rfl (ht (Fin.le_last _)))
    have hlast : IntervalIntegrable f volume
        (t (Fin.last m).castSucc) (t (Fin.last (m + 1))) :=
      let hlastidx : (Fin.last m).castSucc ≤ Fin.last (m + 1) := by
        simpa only [Fin.succ_last] using Fin.castSucc_le_succ (Fin.last m)
      hf.mono_set (by
        rw [uIcc_of_le (ht hlastidx),
          uIcc_of_le (ht (Fin.zero_le _))]
        exact Icc_subset_Icc (ht (Fin.zero_le _)) le_rfl)
    have hsum := ih (fun i => t i.castSucc) (ht.comp (fun _ _ hij => hij)) hfirst
    simpa only [Fin.castSucc_zero, Fin.succ_last] using
      hsum ▸ intervalIntegral.integral_add_adjacent_intervals hfirst hlast

variable {n : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem chart_piece_action_eq {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {a b : ℝ} (hab : a ≤ b) (x : M) (α : ℝ → M)
    (hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α (Ioo a b))
    (hsrc : MapsTo α (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (hpotential : ContinuousOn
      (fun s => 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s)) (Icc a b))
    (hint : IntervalIntegrable (regularizedLIntegrand F T α) volume a b)
    (v : IntervalL2 (EuclideanSpace ℝ (Fin n)) a b)
    (hv : (v : ℝ → EuclideanSpace ℝ (Fin n)) =ᵐ[volume.restrict (Icc a b)]
      deriv ((extChartAt (𝓡 n) x) ∘ α)) :
    (∫ s in a..b, regularizedChartMetric F T x (s, α s) (v s) (v s)) +
      (∫ s in a..b, 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s)) =
      ∫ s in a..b, regularizedLIntegrand F T α s := by
  let V := fun s => 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s)
  have hV : IntervalIntegrable V volume a b := hpotential.intervalIntegrable_of_Icc hab
  have hkin : (∫ s in a..b, regularizedChartMetric F T x (s, α s) (v s) (v s)) =
      ∫ s in a..b, regularizedLIntegrand F T α s - V s := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
      ← integral_Icc_eq_integral_Ioc, ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    have hmem : ∀ᵐ s ∂volume.restrict (Icc a b), s ∈ Ioo a b := by
      rw [← restrict_Ioo_eq_restrict_Icc]
      exact ae_restrict_mem measurableSet_Ioo
    filter_upwards [hv, hmem] with s hs hsI
    rw [hs]
    have hdiff := ((hreg s hsI).contMDiffAt (isOpen_Ioo.mem_nhds hsI)).mdifferentiableAt
      (by norm_num)
    change (1 / 2 : ℝ) * metricInChart (F.metric (T - s ^ 2)) x (α s)
      (deriv ((extChartAt (𝓡 n) x) ∘ α) s) (deriv ((extChartAt (𝓡 n) x) ∘ α) s) = _
    rw [metricInChart_deriv _ (hsrc (Ioo_subset_Icc_self hsI)) hdiff]
    simp only [regularizedLIntegrand, referenceSpeedSq, V, add_sub_cancel_left]
  rw [hkin, intervalIntegral.integral_sub hint hV, sub_add_cancel]

theorem finite_chart_action_le {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i) (x : ι → M)
    (K : ι → Set M) (hK : ∀ i, IsCompact (K i))
    (hsrc : ∀ i, K i ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source)
    (htime : ∀ i s, s ∈ Icc (a i) (b i) → T - s ^ 2 ∈ J)
    (hpotential : ∀ i, ContinuousOn
      (fun z : ℝ × M => 2 * z.1 ^ 2 * (F.connection (T - z.1 ^ 2)).scalarCurvature z.2)
      (Icc (a i) (b i) ×ˢ K i))
    (α : ℕ → ℝ → M) (γ : ℝ → M)
    (hα : ∀ i k, ContinuousOn (α k) (Icc (a i) (b i)))
    (hγ : ∀ i, ContinuousOn γ (Icc (a i) (b i)))
    (hαK : ∀ i k, MapsTo (α k) (Icc (a i) (b i)) (K i))
    (hγK : ∀ i, MapsTo γ (Icc (a i) (b i)) (K i))
    (hlim : ∀ i, TendstoUniformlyOn α γ atTop (Icc (a i) (b i)))
    (v : ∀ i, ℕ → IntervalL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i))
    (w : ∀ i, IntervalL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i))
    (C : ι → ℝ) (hbound : ∀ i k, ‖v i k‖ ≤ C i)
    (hweak : ∀ i, ∀ l : IntervalL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i) →L[ℝ] ℝ,
      Tendsto (fun k => l (v i k)) atTop (𝓝 (l (w i))))
    (action : ℕ → ℝ) (L : ℝ) (haction : Tendsto action atTop (𝓝 L))
    (henergy : ∀ k,
      (∑ i, ((∫ s in a i..b i, regularizedChartMetric F T (x i) (s, α k s)
          (v i k s) (v i k s)) +
        ∫ s in a i..b i, 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α k s)))
        ≤ action k) :
    (∑ i, ((∫ s in a i..b i, regularizedChartMetric F T (x i) (s, γ s)
        (w i s) (w i s)) +
      ∫ s in a i..b i, 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (γ s))) ≤ L := by
  classical
  let B i k s := regularizedChartMetric F T (x i) (s, α k s)
  let D i s := regularizedChartMetric F T (x i) (s, γ s)
  have hBcont (i : ι) (k : ℕ) : ContinuousOn (B i k) (Icc (a i) (b i)) :=
    (regularizedChartMetric_continuousOn F T (x i) (htime i) (hsrc i)).comp
      (continuousOn_id.prodMk (hα i k)) (fun s hs => ⟨hs, hαK i k hs⟩)
  have hDcont (i : ι) : ContinuousOn (D i) (Icc (a i) (b i)) :=
    (regularizedChartMetric_continuousOn F T (x i) (htime i) (hsrc i)).comp
      (continuousOn_id.prodMk (hγ i)) (fun s hs => ⟨hs, hγK i hs⟩)
  have hB (i : ι) (k : ℕ) :
      MemLp (B i k) ∞ (volume.restrict (Icc (a i) (b i))) :=
    continuousOn_memLp_top_Icc (f := B i k) (a := a i) (b := b i) (hBcont i k)
  have hD (i : ι) : MemLp (D i) ∞ (volume.restrict (Icc (a i) (b i))) :=
    continuousOn_memLp_top_Icc (f := D i) (a := a i) (b := b i) (hDcont i)
  have hcoeff (i : ι) : TendstoUniformlyOn (B i) (D i) atTop (Icc (a i) (b i)) :=
    uniform_composition_on_compact_core (hK i) _
      (regularizedChartMetric_continuousOn F T (x i) (htime i) (hsrc i)) α γ
      (Eventually.of_forall (hαK i)) (hγK i) (hlim i)
  let V : ℝ × M → ℝ := fun z =>
    2 * z.1 ^ 2 * (F.connection (T - z.1 ^ 2)).scalarCurvature z.2
  have hVlim (i : ι) : Tendsto (fun k => ∫ s in a i..b i, V (s, α k s)) atTop
      (𝓝 (∫ s in a i..b i, V (s, γ s))) := by
    apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    · apply Eventually.of_forall
      intro k
      rw [uIcc_of_le (hab i)]
      exact (hpotential i).comp (continuousOn_id.prodMk (hα i k))
        (fun s hs => ⟨hs, hαK i k hs⟩)
    · rw [uIcc_of_le (hab i)]
      exact uniform_composition_on_compact_core (hK i) V (hpotential i) α γ
        (Eventually.of_forall (hαK i)) (hγK i) (hlim i)
  have hinterval (i : ι) (f : ℝ → ℝ) :
      (∫ s, f s ∂volume.restrict (Icc (a i) (b i))) = ∫ s in a i..b i, f s := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (hab i)]
  have htotal := finite_integral_action_le_of_weak_limit a b B D hB hD
    (fun i => by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact regularizedChartMetric_nonneg F T (x i) s (hsrc i (hγK i hs)))
    hcoeff v w C hbound hweak
    (fun k => ∑ i, ∫ s in a i..b i, V (s, α k s)) action
    (∑ i, ∫ s in a i..b i, V (s, γ s)) L
    (tendsto_finsetSum Finset.univ (fun i _ => hVlim i)) haction (by
      intro k
      simpa only [hinterval, ← Finset.sum_add_distrib, B, V] using henergy k)
  simpa only [hinterval, ← Finset.sum_add_distrib, D, V] using htotal

end PoincareConjecture.ReducedLengthMinimum.Variational
