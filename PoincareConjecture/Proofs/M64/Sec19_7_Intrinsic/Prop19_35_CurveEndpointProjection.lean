import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CurveEndpointChart










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix ENNReal

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_curve_endpoint_projection_measure_le
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : ContDiff ℝ ∞ e) {height : ℝ → ℝ} (hh : Measurable height)
    {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hinj : InjOn (fun a => e !₂[a, height a]) S)
    (hregular : ∀ a ∈ S, Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, height a]))
    {target : ℝ → AnnulusCoordinates} (htarget : ContDiff ℝ ∞ target)
    (htargetInj : InjOn target T)
    (hend : ∀ a ∈ S, e !₂[a, height a] ∈ target '' T)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ a ∈ S, ∀ v : AnnulusCoordinates,
      c ^ 2 * (intrinsicBoundarySpeed N.metric 1 a ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e !₂[a, height a])
          (fderiv ℝ e !₂[a, height a] v) (fderiv ℝ e !₂[a, height a] v)) :
    ENNReal.ofReal c * (∫⁻ a in S, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a)) ≤
      ∫⁻ t in T, ENNReal.ofReal
        (Real.sqrt (N.metric.inner (target t) (deriv target t) (deriv target t))) := by
  classical
  rcases S.eq_empty_or_nonempty with hEmpty | hNonempty
  · simp [hEmpty]
  have hInv (a : S) :
      ∃ F : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates,
        !₂[a.1, height a.1] ∈ F.source ∧
        (F : AnnulusCoordinates → AnnulusCoordinates) = e ∧
        ContDiffOn ℝ ∞ F.symm F.target := by
    obtain ⟨F, hpoint, _, hF, _, hFi⟩ :=
      m64Intrinsic_exists_smooth_polar_inverse isOpen_univ
        (contMDiff_iff_contDiff.mpr he).contMDiffOn (mem_univ !₂[a.1, height a.1])
        (hregular a a.2)
    exact ⟨F, hpoint, hF, hFi⟩
  choose F hpoint hF hFi using hInv
  obtain ⟨C, hCcount, hCcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun a : S => (F a).source) (fun a => (F a).open_source)
  have hCnonempty : C.Nonempty := by
    obtain ⟨a, ha⟩ := hNonempty
    have hmem : !₂[a, height a] ∈ ⋃ b : S, (F b).source :=
      mem_iUnion.mpr ⟨⟨a, ha⟩, hpoint ⟨a, ha⟩⟩
    rw [← hCcover] at hmem
    obtain ⟨b, hb⟩ := mem_iUnion.mp hmem
    obtain ⟨hbC, _⟩ := mem_iUnion.mp hb
    exact ⟨b, hbC⟩
  obtain ⟨v, hv⟩ := hCcount.exists_eq_range hCnonempty
  have hcover (a : ℝ) (ha : a ∈ S) : ∃ n : ℕ, !₂[a, height a] ∈ (F (v n)).source := by
    have hmem : !₂[a, height a] ∈ ⋃ b : S, (F b).source :=
      mem_iUnion.mpr ⟨⟨a, ha⟩, hpoint ⟨a, ha⟩⟩
    rw [← hCcover] at hmem
    obtain ⟨b, hb⟩ := mem_iUnion.mp hmem
    obtain ⟨hbC, hbpoint⟩ := mem_iUnion.mp hb
    rw [hv] at hbC
    obtain ⟨n, rfl⟩ := hbC
    exact ⟨n, hbpoint⟩
  let A : ℕ → Set ℝ := fun n => S ∩ (fun a => !₂[a, height a]) ⁻¹' (F (v n)).source
  have hgraph : Measurable (fun a => (!₂[a, height a] : AnnulusCoordinates)) := by fun_prop
  have hA (n : ℕ) : MeasurableSet (A n) :=
    hS.inter ((F (v n)).open_source.measurableSet.preimage hgraph)
  have hAunion : (⋃ n, A n) = S := by
    apply Subset.antisymm
    · intro a ha
      obtain ⟨n, hn⟩ := mem_iUnion.mp ha
      exact hn.1
    · intro a ha
      obtain ⟨n, hn⟩ := hcover a ha
      exact mem_iUnion.mpr ⟨n, ha, hn⟩
  let P := disjointed A
  have hP (n : ℕ) : MeasurableSet (P n) := MeasurableSet.disjointed hA n
  have hPsub (n : ℕ) : P n ⊆ S := (disjointed_subset A n).trans inter_subset_left
  have hPsource (n : ℕ) (a : ℝ) (ha : a ∈ P n) :
      !₂[a, height a] ∈ (F (v n)).source := (disjointed_subset A n ha).2
  have hPunion : (⋃ n, P n) = S := by rw [iUnion_disjointed, hAunion]
  let B : ℕ → Set ℝ := fun n => m64IntrinsicCurveEndpointParameters e height (P n) target T
  have hlocal (n : ℕ) : MeasurableSet (B n) ∧
      ENNReal.ofReal c * (∫⁻ a in P n, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a)) ≤
        ∫⁻ t in B n, ENNReal.ofReal
          (Real.sqrt (N.metric.inner (target t) (deriv target t) (deriv target t))) :=
    m64Intrinsic_curve_endpoint_chart_measure_le N e (he.differentiable (by simp))
      (F (v n)) (hF (v n)) (hFi (v n)) (hP n) hT hh htarget htargetInj (hPsource n)
      (fun a ha => hend a (hPsub n ha)) hc (fun a ha => hbound a (hPsub n ha))
  have hBdisj : Pairwise (fun n m => Disjoint (B n) (B m)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro t htn htm
    obtain ⟨_, a, ha, hat⟩ := htn
    obtain ⟨_, a', ha', ha't⟩ := htm
    have haa' := hinj (hPsub n ha) (hPsub m ha') (hat.trans ha't.symm)
    exact Set.disjoint_left.mp (disjoint_disjointed A hnm) ha (haa'.symm ▸ ha')
  have hBsub : (⋃ n, B n) ⊆ T := by
    intro t ht
    obtain ⟨n, hn⟩ := mem_iUnion.mp ht
    exact hn.1
  calc
    _ = ∑' n, ENNReal.ofReal c *
        (∫⁻ a in P n, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a)) := by
      rw [← hPunion, lintegral_iUnion hP (disjoint_disjointed A), ENNReal.tsum_mul_left]
    _ ≤ ∑' n, ∫⁻ t in B n, ENNReal.ofReal
        (Real.sqrt (N.metric.inner (target t) (deriv target t) (deriv target t))) :=
      ENNReal.tsum_le_tsum (fun n => (hlocal n).2)
    _ = ∫⁻ t in ⋃ n, B n, ENNReal.ofReal
        (Real.sqrt (N.metric.inner (target t) (deriv target t) (deriv target t))) :=
      (lintegral_iUnion (fun n => (hlocal n).1) hBdisj _).symm
    _ ≤ _ := lintegral_mono_set hBsub




theorem m64Intrinsic_unit_curve_endpoint_projection_length_le
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : ContDiff ℝ ∞ e) {height : ℝ → ℝ} (hh : Measurable height)
    {S : Set ℝ} (hS : MeasurableSet S) {l u : ℝ} (hSsub : S ⊆ Icc l u)
    (hinj : InjOn (fun a => e !₂[a, height a]) S)
    (hregular : ∀ a ∈ S, Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, height a]))
    {target : ℝ → AnnulusCoordinates} (htarget : ContDiff ℝ ∞ target)
    {a b : ℝ} (hab : a ≤ b) (htargetInj : InjOn target (Icc a b))
    (hunit : ∀ t ∈ Icc a b,
      N.metric.inner (target t) (deriv target t) (deriv target t) = 1)
    (hend : ∀ s ∈ S, e !₂[s, height s] ∈ target '' Icc a b)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ s ∈ S, ∀ v : AnnulusCoordinates,
      c ^ 2 * (intrinsicBoundarySpeed N.metric 1 s ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e !₂[s, height s])
          (fderiv ℝ e !₂[s, height s] v) (fderiv ℝ e !₂[s, height s] v)) :
    c * (∫ s in S, intrinsicBoundarySpeed N.metric 1 s) ≤ b - a := by
  have hlength := m64Intrinsic_curve_endpoint_projection_measure_le N e he hh hS
    measurableSet_Icc hinj hregular htarget htargetInj hend hc hbound
  have htargetLength :
      (∫⁻ t in Icc a b, ENNReal.ofReal
        (Real.sqrt (N.metric.inner (target t) (deriv target t) (deriv target t)))) =
        ENNReal.ofReal (b - a) := by
    calc
      _ = ∫⁻ _ in Icc a b, (1 : ℝ≥0∞) := by
        apply setLIntegral_congr_fun measurableSet_Icc
        intro t ht
        change ENNReal.ofReal (Real.sqrt
          (N.metric.inner (target t) (deriv target t) (deriv target t))) = 1
        rw [hunit t ht, Real.sqrt_one, ENNReal.ofReal_one]
      _ = _ := by simp
  have hs := (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
  rw [htargetLength, ← ofReal_integral_eq_lintegral_ofReal
    (hs.integrableOn_Icc.mono_set hSsub)
    (Eventually.of_forall (fun _ => Real.sqrt_nonneg _)),
    ← ENNReal.ofReal_mul hc] at hlength
  exact (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hab)).mp hlength

end PoincareConjecture
