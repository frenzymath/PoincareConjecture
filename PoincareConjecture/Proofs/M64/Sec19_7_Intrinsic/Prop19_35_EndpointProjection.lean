import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_EndpointChart

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle Matrix ENNReal

namespace PoincareConjecture

theorem m64Intrinsic_endpoint_projection_length_le
    (N : IntrinsicAnnulus) (e : AnnulusCoordinates → AnnulusCoordinates)
    (he : ContDiff ℝ ∞ e) {height : ℝ → ℝ} (hh : Measurable height)
    {S : Set ℝ} (hS : MeasurableSet S) (hSsub : S ⊆ Ico (0 : ℝ) rampPeriod)
    (hinj : InjOn (fun a => e !₂[a, height a]) S)
    (hregular : ∀ a ∈ S, Function.Injective (mfderiv (𝓡 2) (𝓡 2) e !₂[a, height a]))
    (hend : ∀ a ∈ S, ‖e !₂[a, height a]‖ = 2)
    {c : ℝ} (hc : 0 ≤ c)
    (hbound : ∀ a ∈ S, ∀ v : AnnulusCoordinates,
      c ^ 2 * (intrinsicBoundarySpeed N.metric 1 a ^ 2 * (v 0) ^ 2 + (v 1) ^ 2) ≤
        N.metric.inner (e !₂[a, height a])
          (fderiv ℝ e !₂[a, height a] v) (fderiv ℝ e !₂[a, height a] v)) :
    c * (∫ a in S, intrinsicBoundarySpeed N.metric 1 a) ≤
      intrinsicBoundaryLength N.metric 2 0 rampPeriod := by
  classical
  rcases S.eq_empty_or_nonempty with hEmpty | hNonempty
  · simp only [hEmpty, setIntegral_empty, mul_zero]
    exact m64Intrinsic_boundaryLength_nonneg N 2 0 rampPeriod Real.two_pi_pos.le
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
  obtain ⟨T, hTcount, hTcover⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun a : S => (F a).source) (fun a => (F a).open_source)
  have hTnonempty : T.Nonempty := by
    obtain ⟨a, ha⟩ := hNonempty
    have hmem : !₂[a, height a] ∈ ⋃ b : S, (F b).source :=
      mem_iUnion.mpr ⟨⟨a, ha⟩, hpoint ⟨a, ha⟩⟩
    rw [← hTcover] at hmem
    obtain ⟨b, hb⟩ := mem_iUnion.mp hmem
    obtain ⟨hbT, _⟩ := mem_iUnion.mp hb
    exact ⟨b, hbT⟩
  obtain ⟨v, hv⟩ := hTcount.exists_eq_range hTnonempty
  have hcover (a : ℝ) (ha : a ∈ S) : ∃ n : ℕ, !₂[a, height a] ∈ (F (v n)).source := by
    have hmem : !₂[a, height a] ∈ ⋃ b : S, (F b).source :=
      mem_iUnion.mpr ⟨⟨a, ha⟩, hpoint ⟨a, ha⟩⟩
    rw [← hTcover] at hmem
    obtain ⟨b, hb⟩ := mem_iUnion.mp hmem
    obtain ⟨hbT, hbpoint⟩ := mem_iUnion.mp hb
    rw [hv] at hbT
    obtain ⟨n, rfl⟩ := hbT
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
  let B : ℕ → Set ℝ := fun n => m64IntrinsicEndpointParameters e height (P n)
  have hlocal (n : ℕ) : MeasurableSet (B n) ∧
      ENNReal.ofReal c * (∫⁻ a in P n, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a)) ≤
        ∫⁻ b in B n, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 2 b) :=
    m64Intrinsic_endpoint_chart_measure_le N e (he.differentiable (by simp))
      (F (v n)) (hF (v n)) (hFi (v n)) (hP n) hh (hPsource n)
      (fun a ha => hend a (hPsub n ha)) hc (fun a ha => hbound a (hPsub n ha))
  have hBdisj : Pairwise (fun n m => Disjoint (B n) (B m)) := by
    intro n m hnm
    apply Set.disjoint_left.mpr
    intro b hbn hbm
    obtain ⟨_, a, ha, hab⟩ := hbn
    obtain ⟨_, a', ha', ha'b⟩ := hbm
    have haa' := hinj (hPsub n ha) (hPsub m ha') (hab.trans ha'b.symm)
    exact Set.disjoint_left.mp (disjoint_disjointed A hnm) ha (haa'.symm ▸ ha')
  have hBsub : (⋃ n, B n) ⊆ Ico (0 : ℝ) rampPeriod := by
    intro b hb
    obtain ⟨n, hn⟩ := mem_iUnion.mp hb
    exact hn.1
  have hlength : ENNReal.ofReal c *
      (∫⁻ a in S, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a)) ≤
      ∫⁻ b in Ico (0 : ℝ) rampPeriod, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 2 b) := by
    calc
      _ = ∑' n, ENNReal.ofReal c *
          (∫⁻ a in P n, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 1 a)) := by
        rw [← hPunion, lintegral_iUnion hP (disjoint_disjointed A), ENNReal.tsum_mul_left]
      _ ≤ ∑' n, ∫⁻ b in B n, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 2 b) :=
        ENNReal.tsum_le_tsum (fun n => (hlocal n).2)
      _ = ∫⁻ b in ⋃ n, B n, ENNReal.ofReal (intrinsicBoundarySpeed N.metric 2 b) :=
        (lintegral_iUnion (fun n => (hlocal n).1) hBdisj _).symm
      _ ≤ _ := lintegral_mono_set hBsub
  have hs1 := (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (1 : ℝ) ≠ 0)).continuous
  have hs2 := (m64Intrinsic_contDiff_boundarySpeed N (by norm_num : (2 : ℝ) ≠ 0)).continuous
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hs1.integrableOn_Icc.mono_set (hSsub.trans Ico_subset_Icc_self))
    (Eventually.of_forall (fun _ => Real.sqrt_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal
      (hs2.integrableOn_Icc.mono_set Ico_subset_Icc_self)
      (Eventually.of_forall (fun _ => Real.sqrt_nonneg _)),
    ← ENNReal.ofReal_mul hc] at hlength
  have hout : (∫ b in Ico (0 : ℝ) rampPeriod, intrinsicBoundarySpeed N.metric 2 b) =
      intrinsicBoundaryLength N.metric 2 0 rampPeriod := by
    rw [intrinsicBoundaryLength, intervalIntegral.integral_of_le
      (show (0 : ℝ) ≤ rampPeriod from Real.two_pi_pos.le)]
    exact setIntegral_congr_set Ico_ae_eq_Ioc
  rw [hout] at hlength
  exact (ENNReal.ofReal_le_ofReal_iff
    (m64Intrinsic_boundaryLength_nonneg N 2 0 rampPeriod Real.two_pi_pos.le)).mp hlength

end PoincareConjecture
