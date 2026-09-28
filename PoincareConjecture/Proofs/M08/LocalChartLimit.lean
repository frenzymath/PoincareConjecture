import PoincareConjecture.Proofs.M08.MinimizingCompactness
import PoincareConjecture.Proofs.M08.PathGluing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [mTop : TopologicalSpace M]
  [mChart : ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [mSmooth : IsManifold (𝓡 n) ∞ M] [mConnected : ConnectedSpace M] [mT3 : T3Space M]

set_option maxHeartbeats 800000 in

set_option synthInstance.maxHeartbeats 200000 in
theorem finite_chart_limit_le_inf {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₁ : 0 ≤ τ₁) (hordered : τ₁ < τ₂) (hτ₂ : τ₂ ≤ τmax) (p₁ p₂ : M)
    (p : ℕ → BackwardTimePath F T τ₁ τ₂)
    (hanti : Antitone (fun k ↦ backwardLLength F T τ₁ τ₂ (p k).curve))
    (hmin : Tendsto (fun k ↦ backwardLLength F T τ₁ τ₂ (p k).curve)
      atTop (𝓝 (sInf (backwardActionValues F T τ₁ τ₂ p₁ p₂))))
    (γ : ℝ → M) (hγ : Continuous γ)
    (hlim : letI : MetricSpace M := referenceMetricSpace (F.metric T)
      TendstoUniformlyOn (fun k ↦ squareReparameterizedCurve (p k).curve) γ atTop
        (Icc (Real.sqrt τ₁) (Real.sqrt τ₂)))
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hta : t 0 = Real.sqrt τ₁) (htb : t (Fin.last m) = Real.sqrt τ₂)
    (x : Fin m → M) (K : Fin m → Set M)
    (hK : ∀ i, IsCompact (K i) ∧
      γ '' Icc (t i.castSucc) (t i.succ) ⊆ interior (K i) ∧
      K i ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source) :
    ∃ w : ∀ i : Fin m, ChartL2 (EuclideanSpace ℝ (Fin n)) (t i.castSucc) (t i.succ),
      (∀ i s, s ∈ Icc (t i.castSucc) (t i.succ) →
        extChartAt (𝓡 n) (x i) (γ s) = extChartAt (𝓡 n) (x i) (γ (t i.castSucc)) +
          ∫ r in t i.castSucc..s, w i r) ∧
      (∑ i, ((∫ s in t i.castSucc..t i.succ,
          regularizedChartMetric F T (x i) (s, γ s) (w i s) (w i s)) +
        ∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (γ s))) ≤
        sInf (backwardActionValues F T τ₁ τ₂ p₁ p₂) := by
  classical
  letI : MetricSpace M := referenceMetricSpace (F.metric T)
  let a := Real.sqrt τ₁
  let b := Real.sqrt τ₂
  have hab : a < b := Real.sqrt_lt_sqrt hτ₁ hordered
  have hta : t 0 = a := hta
  have htb : t (Fin.last m) = b := htb
  have hsubset (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc a b := by
    rw [← hta, ← htb]
    exact Icc_subset_Icc (ht (Fin.zero_le _)) (ht (Fin.le_last _))
  have heventually (i : Fin m) : ∀ᶠ k in atTop,
      MapsTo (squareReparameterizedCurve (p k).curve) (Icc (t i.castSucc) (t i.succ)) (K i) := by
    obtain ⟨δ, hδ, hmargin⟩ :=
      (isCompact_Icc.image hγ).exists_cthickening_subset_open isOpen_interior (hK i).2.1
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with k hk s hs
    apply interior_subset (hmargin ?_)
    exact Metric.mem_cthickening_of_dist_le _ (γ s) _ _
      (mem_image_of_mem γ hs) (by simpa only [dist_comm] using (hk s (hsubset i hs)).le)
  obtain ⟨N, htail⟩ := eventually_atTop.mp (Filter.eventually_all.mpr heventually)
  have hseg (i : Fin m) : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hleft (i : Fin m) : a ≤ t i.castSucc := by
    rw [← hta]
    exact ht (Fin.zero_le _)
  have hright (i : Fin m) : t i.succ ≤ b := by
    rw [← htb]
    exact ht (Fin.le_last _)
  have hsub (i : Fin m) : Icc (t i.castSucc) (t i.succ) ⊆ Icc a b :=
    Icc_subset_Icc (hleft i) (hright i)
  have hsuboo (i : Fin m) : Ioo (t i.castSucc) (t i.succ) ⊆ Ioo a b :=
    Ioo_subset_Ioo (hleft i) (hright i)
  have husub (i : Fin m) : uIcc (t i.castSucc) (t i.succ) ⊆ uIcc a b := by
    simpa only [uIcc_of_le (hseg i), uIcc_of_le hab.le] using hsub i
  let q : ℕ → BackwardTimePath F T τ₁ τ₂ := fun k ↦ p (k + N)
  let α : ℕ → ℝ → M := fun k ↦ squareReparameterizedCurve (q k).curve
  have hshift : StrictMono (fun k : ℕ ↦ k + N) := fun _ _ hij ↦ Nat.add_lt_add_right hij N
  have hlimq : TendstoUniformlyOn α γ atTop (Icc a b) := by
    intro U hU
    exact hshift.tendsto_atTop.eventually (hlim U hU)
  have hα (i : Fin m) (k : ℕ) : ContinuousOn (α k) (Icc (t i.castSucc) (t i.succ)) :=
    (squarePath_continuousOn (q k)).mono (hsub i)
  have hreg (i : Fin m) (k : ℕ) :
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (α k) (Ioo (t i.castSucc) (t i.succ)) :=
    (squarePath_regular (q k)).mono (hsuboo i)
  have hαK (i : Fin m) (k : ℕ) : MapsTo (α k) (Icc (t i.castSucc) (t i.succ)) (K i) :=
    htail (k + N) (Nat.le_add_left N k) i
  have hγK (i : Fin m) : MapsTo γ (Icc (t i.castSucc) (t i.succ)) (K i) :=
    fun s hs ↦ interior_subset ((hK i).2.1 (mem_image_of_mem γ hs))
  have htime (i : Fin m) (s : ℝ) (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      T - s ^ 2 ∈ J := by
    apply (p 0).time_mem
    have hsab := hsub i hs
    have hsn : 0 ≤ s := (Real.sqrt_nonneg τ₁).trans hsab.1
    constructor
    · simpa only [a, Real.sq_sqrt hτ₁] using
        (sq_le_sq₀ (Real.sqrt_nonneg τ₁) hsn).mpr hsab.1
    · simpa only [b, Real.sq_sqrt (hτ₁.trans hordered.le)] using
        (sq_le_sq₀ hsn (Real.sqrt_nonneg τ₂)).mpr hsab.2
  obtain ⟨R, hR, hRm⟩ := hcurvature.2
  let C := 2 * (Real.exp (2 * (n : ℝ) * R * τmax) *
    (backwardLLength F T τ₁ τ₂ (p 0).curve +
      (Real.sqrt τ₂ * (n : ℝ) ^ 2 * R) * (τ₂ - τ₁)))
  have hE (k : ℕ) : IntervalIntegrable
      (referenceSpeedSq (F.metric T) (α k)) volume a b ∧
      (∫ s in a..b, referenceSpeedSq (F.metric T) (α k) s) ≤ C := by
    have href := referenceWeightedEnergy_bound hM04 hwindow hR hRm (q k) hτ₂
    have hsquare := squarePath_referenceEnergy (q k) (F.metric T) href.1
    refine ⟨hsquare.1, ?_⟩
    rw [hsquare.2]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply href.2.trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact add_le_add (hanti (Nat.zero_le (k + N))) le_rfl
  have hEpiece (i : Fin m) (k : ℕ) : IntervalIntegrable
      (referenceSpeedSq (F.metric T) (α k)) volume (t i.castSucc) (t i.succ) :=
    (hE k).1.mono_set (husub i)
  have hEbound (i : Fin m) (k : ℕ) :
      (∫ s in t i.castSucc..t i.succ, referenceSpeedSq (F.metric T) (α k) s) ≤ C := by
    apply le_trans _ (hE k).2
    exact intervalIntegral.integral_mono_interval (hleft i) (hseg i) (hright i)
      (Eventually.of_forall (referenceSpeedSq_nonneg _ _)) (hE k).1
  obtain ⟨v, w, B, φ, hφ, hv, hprimitive, hweak⟩ :=
    finite_chartH1_limit (F.metric T) (fun i ↦ t i.castSucc) (fun i ↦ t i.succ) hseg
      x K (fun i ↦ (hK i).1) (fun i ↦ (hK i).2.2) α γ hα hreg hαK hγK
      (fun i s hs ↦ hlimq.tendsto_at (hsub i hs)) hEpiece (fun _ ↦ C) hEbound
  have hlimφ (i : Fin m) : TendstoUniformlyOn (fun k ↦ α (φ k)) γ atTop
      (Icc (t i.castSucc) (t i.succ)) := by
    intro U hU
    exact hφ.tendsto_atTop.eventually ((hlimq.mono (hsub i)) U hU)
  have henergy (k : ℕ) :
      (∑ i : Fin m,
        ((∫ s in t i.castSucc..t i.succ,
          regularizedChartMetric F T (x i) (s, α (φ k) s) (v i (φ k) s) (v i (φ k) s)) +
          ∫ s in t i.castSucc..t i.succ,
            2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α (φ k) s))) ≤
        backwardLLength F T τ₁ τ₂ (q (φ k)).curve := by
    have haction := squarePath_action (q (φ k))
    have hpieces (i : Fin m) := chart_piece_action_eq F hM04 T (hseg i) (x i) (α (φ k))
      (hα i (φ k)) (hreg i (φ k))
      (fun s hs ↦ (hK i).2.2 (hαK i (φ k) hs)) (htime i)
      (haction.1.mono_set (husub i)) (v i (φ k)) (hv i (φ k)).2
    simp only [hpieces]
    have hsum := (integrable_sum_fin_partition t (regularizedLIntegrand F T (α (φ k)))
      (fun i ↦ haction.1.mono_set (husub i))).2
    rw [hsum, hta, htb]
    exact haction.2.le
  have hLSC :
      (∑ i : Fin m, ((∫ s in t i.castSucc..t i.succ,
        regularizedChartMetric F T (x i) (s, γ s) (w i s) (w i s)) +
        ∫ s in t i.castSucc..t i.succ,
          2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (γ s))) ≤
        sInf (backwardActionValues F T τ₁ τ₂ p₁ p₂) :=
    @finite_chart_action_le n M mTop mChart mSmooth mConnected mT3 J F hM04 T
    (Fin m) inferInstance
    (fun i ↦ t i.castSucc) (fun i ↦ t i.succ) hseg
    x K (fun i ↦ (hK i).1) (fun i ↦ (hK i).2.2) htime (fun k ↦ α (φ k)) γ
    (fun i k ↦ hα i (φ k)) (fun _ ↦ hγ.continuousOn)
    (fun i k ↦ hαK i (φ k)) hγK hlimφ (fun i k ↦ v i (φ k)) w B
    (fun i ↦ (norm_nonneg (v i 0)).trans (hv i 0).1)
    (fun i k ↦ (hv i (φ k)).1) hweak
    (fun k ↦ backwardLLength F T τ₁ τ₂ (q (φ k)).curve) _
    ((hmin.comp hshift.tendsto_atTop).comp hφ.tendsto_atTop) henergy
  exact ⟨w, hprimitive, hLSC⟩

end PoincareConjecture.M08
