import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variational.TimeSupport.RegularPath
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ReducedGeometry.LGeometry.Theory








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture

namespace LGeodesicTheory

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}

theorem reducedLength_le_path (L : LGeodesicTheory F T τmax)
    {τ : ℝ} (hτ : 0 < τ) (hτmax : τ ≤ τmax) (p q : M)
    (path : BackwardTimePath F T 0 τ) (hp : path.curve 0 = p) (hq : path.curve τ = q) :
    reducedLength F T p q τ ≤ backwardLLength F T 0 τ path.curve / (2 * Real.sqrt τ) := by
  obtain ⟨minimal, hm0, hmτ, hm, hvalue⟩ := L.reduced_length_attained τ hτ hτmax p q
  rw [hvalue]
  exact div_le_div_of_nonneg_right (hm path (hp.trans hm0.symm) (hq.trans hmτ.symm))
    (by positivity)

end LGeodesicTheory

namespace ReducedLengthMinimum.Variational

variable {n : ℕ} {M : Type u} [MetricSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ}



theorem reducedLength_le_finite_piece_action
    (L : LGeodesicTheory F T τmax) {τ : ℝ} (hτ : 0 < τ) (hτmax : τ ≤ τmax)
    (hT : T ∈ J) (hback : ∀ r ∈ Icc 0 τ, T - r ∈ J)
    {m : ℕ} (t : Fin (m + 1) → ℝ) (ht : Monotone t)
    (hta : t 0 = 0) (htb : t (Fin.last m) = Real.sqrt τ)
    (hpotential : ContinuousOn (fun z : ℝ × M =>
      2 * z.1 ^ 2 * (F.connection (T - z.1 ^ 2)).scalarCurvature z.2)
      (Icc 0 (Real.sqrt τ) ×ˢ univ))
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
    2 * Real.sqrt τ * reducedLength F T (γ 0) (γ (Real.sqrt τ)) τ ≤
      ∑ i, chartH1Action F T (x i) (t i.castSucc) (t i.succ) (β i) (w i) := by
  have htime (s : ℝ) (hs : s ∈ Icc (t 0) (t (Fin.last m))) : T - s ^ 2 ∈ J := by
    rw [hta, htb] at hs
    exact hback _ ⟨sq_nonneg _, (Real.le_sqrt hs.1 hτ.le).mp hs.2⟩
  have hpotential' : ContinuousOn (fun z : ℝ × M =>
      2 * z.1 ^ 2 * (F.connection (T - z.1 ^ 2)).scalarCurvature z.2)
      (Icc (t 0) (t (Fin.last m)) ×ˢ univ) := by
    simpa only [hta, htb] using hpotential
  obtain ⟨α, hα, _, hlim⟩ := exists_smooth_finite_chart_piece_recovery F T t ht htime
    hpotential' γ β hβ hβa hβb x hsrc w hprimitive
  have hcont (k : ℕ) : ContinuousOn (α k) (Icc (Real.sqrt 0) (Real.sqrt τ)) :=
    (hα k).1.continuous.continuousOn
  have hreg (k : ℕ) : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (α k)
      (Ioo (Real.sqrt 0) (Real.sqrt τ)) := ((hα k).1.of_le (by simp)).contMDiffOn
  have hint (k : ℕ) : IntervalIntegrable (regularizedLIntegrand F T (α k)) volume
      (Real.sqrt 0) (Real.sqrt τ) := by
    simpa only [hta, htb, Real.sqrt_zero] using (hα k).2.2.2
  let paths : ℕ → BackwardTimePath F T 0 τ := fun k =>
    backwardPathOfSqrt F T 0 τ le_rfl hτ hT hback (α k) (hcont k) (hreg k) (hint k)
  have hstart (k : ℕ) : (paths k).curve 0 = γ 0 := by
    change α k (Real.sqrt 0) = γ 0
    simpa only [Real.sqrt_zero, hta] using (hα k).2.1
  have hend (k : ℕ) : (paths k).curve τ = γ (Real.sqrt τ) := by
    change α k (Real.sqrt τ) = γ (Real.sqrt τ)
    simpa only [htb] using (hα k).2.2.1
  have haction (k : ℕ) : backwardLLength F T 0 τ (paths k).curve =
      ∫ s in t 0..t (Fin.last m), regularizedLIntegrand F T (α k) s := by
    rw [backwardPathOfSqrt_action]
    simp only [hta, htb, Real.sqrt_zero]
  apply ge_of_tendsto hlim
  apply Eventually.of_forall
  intro k
  have h := (le_div_iff₀ (show 0 < 2 * Real.sqrt τ by positivity)).mp
    (L.reducedLength_le_path hτ hτmax _ _ (paths k) (hstart k) (hend k))
  simpa only [haction, mul_comm] using h



theorem reducedLength_le_two_smooth_pieces
    (L : LGeodesicTheory F T τmax) {τ c : ℝ}
    (hτ : 0 < τ) (hτmax : τ ≤ τmax) (hc : c ∈ Icc 0 (Real.sqrt τ))
    (hT : T ∈ J) (hback : ∀ r ∈ Icc 0 τ, T - r ∈ J)
    (hpotential : ContinuousOn (fun z : ℝ × M =>
      2 * z.1 ^ 2 * (F.connection (T - z.1 ^ 2)).scalarCurvature z.2)
      (Icc 0 (Real.sqrt τ) ×ˢ univ))
    (γ α β : ℝ → M) (hγ : Continuous γ)
    {U V : Set ℝ} (hU : IsOpen U) (hV : IsOpen V)
    (hIU : Icc 0 c ⊆ U) (hIV : Icc c (Real.sqrt τ) ⊆ V)
    (hα : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ α U)
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ β V)
    (hleft : EqOn γ α (Icc 0 c)) (hright : EqOn γ β (Icc c (Real.sqrt τ))) :
    2 * Real.sqrt τ * reducedLength F T (γ 0) (γ (Real.sqrt τ)) τ ≤
      (∫ s in 0..c, regularizedLIntegrand F T α s) +
        ∫ s in c..Real.sqrt τ, regularizedLIntegrand F T β s := by
  classical
  let R : Set (ℝ × ℝ) := {ab | ab.1 ≤ ab.2 ∧
    ∃ x : M, ∃ w : IntervalL2 (EuclideanSpace ℝ (Fin n)) ab.1 ab.2,
      MapsTo γ (Icc ab.1 ab.2) (chartAt (EuclideanSpace ℝ (Fin n)) x).source ∧
      (∀ s ∈ Icc ab.1 ab.2,
        extChartAt (𝓡 n) x (γ s) = extChartAt (𝓡 n) x (γ ab.1) +
          ∫ r in ab.1..s, w r) ∧
      ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 γ (Ioo ab.1 ab.2)}
  have partition {a b : ℝ} (hab : a ≤ b) (δ : ℝ → M) {W : Set ℝ}
      (hW : IsOpen W) (hIW : Icc a b ⊆ W)
      (hδ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ δ W)
      (heq : EqOn γ δ (Icc a b)) :
      ∃ p : RelSeries R, p.head = a ∧ p.last = b := by
    obtain ⟨m, t, x, w, ht, hta, htb, hsrc, hw⟩ :=
      exists_finite_chart_primitive_of_smooth hab δ γ hγ hW hIW hδ heq
    refine ⟨⟨m, t, ?_⟩, hta, htb⟩
    intro i
    refine ⟨ht (Fin.castSucc_le_succ i), x i, w i, hsrc i, hw i, ?_⟩
    have hsub : Ioo (t i.castSucc) (t i.succ) ⊆ Icc a b := by
      rw [← hta, ← htb]
      exact Ioo_subset_Icc_self.trans
        (Icc_subset_Icc (ht (Fin.zero_le _)) (ht (Fin.le_last _)))
    exact ((hδ.of_le (by simp)).mono (hsub.trans hIW)).congr
      (fun s hs => heq (hsub hs))
  obtain ⟨p, hp0, hpc⟩ := partition hc.1 α hU hIU hα hleft
  obtain ⟨q, hqc, hqb⟩ := partition hc.2 β hV hIV hβ hright
  have hpq : p.last = q.head := hpc.trans hqc.symm
  let r := p.smash q hpq
  let t : Fin (r.length + 1) → ℝ := r
  have ht : Monotone t := Fin.monotone_iff_le_succ.mpr (fun i => (r.step i).1)
  have hta : t 0 = 0 := by
    change r.head = 0
    simpa only [r, RelSeries.head_smash] using hp0
  have htb : t (Fin.last r.length) = Real.sqrt τ := by
    change r.last = Real.sqrt τ
    simpa only [r, RelSeries.last_smash] using hqb
  choose x w hsrc hw hreg using fun i : Fin r.length => (r.step i).2
  have hseg (i : Fin r.length) : t i.castSucc ≤ t i.succ := ht (Fin.castSucc_le_succ i)
  have hsub (i : Fin r.length) : Icc (t i.castSucc) (t i.succ) ⊆ Icc 0 (Real.sqrt τ) := by
    rw [← hta, ← htb]
    exact Icc_subset_Icc (ht (Fin.zero_le _)) (ht (Fin.le_last _))
  have htime (i : Fin r.length) (s : ℝ) (hs : s ∈ Icc (t i.castSucc) (t i.succ)) :
      T - s ^ 2 ∈ J :=
    hback _ ⟨sq_nonneg _, (Real.le_sqrt (hsub i hs).1 hτ.le).mp (hsub i hs).2⟩
  have hvel (i : Fin r.length) :
      (w i : ℝ → EuclideanSpace ℝ (Fin n)) =ᵐ[volume.restrict (Icc (t i.castSucc) (t i.succ))]
        deriv ((extChartAt (𝓡 n) (x i)) ∘ γ) := by
    filter_upwards [primitive_ae_hasDerivAt (hseg i)
      ((extChartAt (𝓡 n) (x i)) ∘ γ) (w i) (hw i)] with s hs
    exact hs.deriv.symm
  have hpot (i : Fin r.length) : ContinuousOn
      (fun s => 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (γ s))
      (Icc (t i.castSucc) (t i.succ)) :=
    hpotential.comp (continuousOn_id.prodMk hγ.continuousOn)
      (fun s hs => ⟨hsub i hs, mem_univ _⟩)
  have hint (i : Fin r.length) :
      IntervalIntegrable (regularizedLIntegrand F T γ) volume (t i.castSucc) (t i.succ) :=
    chart_piece_integrable F T (hseg i) (x i) γ hγ.continuousOn (hreg i)
      (hsrc i) (htime i) (hpot i) (w i) (hvel i)
  obtain ⟨hglobal, hsum⟩ := integrable_sum_fin_partition t (regularizedLIntegrand F T γ) hint
  have hsum' : (∑ i, chartH1Action F T (x i) (t i.castSucc) (t i.succ) γ (w i)) =
      ∫ s in 0..Real.sqrt τ, regularizedLIntegrand F T γ s := by
    calc
      _ = ∑ i : Fin r.length,
          ∫ s in t i.castSucc..t i.succ, regularizedLIntegrand F T γ s := by
        apply Finset.sum_congr rfl
        intro i _
        exact chart_piece_action_eq F T (hseg i) (x i) γ (hreg i) (hsrc i)
          (hpot i) (hint i) (w i) (hvel i)
      _ = _ := by simpa only [hta, htb] using hsum
  have hbound := reducedLength_le_finite_piece_action L hτ hτmax hT hback t ht hta htb
    hpotential γ (fun _ => γ) (fun _ => hγ.continuousOn) (fun _ => rfl) (fun _ => rfl)
    x hsrc w hw
  rw [hsum'] at hbound
  have hint' : IntervalIntegrable (regularizedLIntegrand F T γ) volume 0 (Real.sqrt τ) := by
    simpa only [hta, htb] using hglobal
  have hintLeft : IntervalIntegrable (regularizedLIntegrand F T γ) volume 0 c := by
    apply hint'.mono_set
    rw [uIcc_of_le hc.1, uIcc_of_le (Real.sqrt_nonneg τ)]
    exact Icc_subset_Icc le_rfl hc.2
  have hintRight : IntervalIntegrable (regularizedLIntegrand F T γ) volume c (Real.sqrt τ) := by
    apply hint'.mono_set
    rw [uIcc_of_le hc.2, uIcc_of_le (Real.sqrt_nonneg τ)]
    exact Icc_subset_Icc hc.1 le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals hintLeft hintRight] at hbound
  convert hbound using 1
  congr 1
  · apply intervalIntegral.integral_congr_Ioo_of_le hc.1
    intro s hs
    apply regularizedLIntegrand_congr_eventually
    exact eventually_of_mem (isOpen_Ioo.mem_nhds hs)
      (fun v hv => (hleft (Ioo_subset_Icc_self hv)).symm)
  · apply intervalIntegral.integral_congr_Ioo_of_le hc.2
    intro s hs
    apply regularizedLIntegrand_congr_eventually
    exact eventually_of_mem (isOpen_Ioo.mem_nhds hs)
      (fun v hv => (hright (Ioo_subset_Icc_self hv)).symm)

end ReducedLengthMinimum.Variational

end PoincareConjecture
