import PoincareConjecture.Proofs.M35.Thm12_28.TerminalScalarConvergence
import PoincareConjecture.Proofs.M09.HessianTrace









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization



theorem uniform_of_moving_point_limits
    {X : Type*} [TopologicalSpace X] [FirstCountableTopology X]
    {K : Set X} (hK : IsCompact K) {F : ℕ → X → ℝ} {G : X → ℝ}
    (hG : ContinuousOn G K)
    (hseq : ∀ sigma : ℕ → ℕ, Tendsto sigma atTop atTop →
      ∀ pseq : ℕ → X, (∀ k, pseq k ∈ K) → ∀ p ∈ K,
        Tendsto pseq atTop (𝓝 p) →
          Tendsto (fun k => F (sigma k) (pseq k)) atTop (𝓝 (G p)))
    {eta : ℝ} (heta : 0 < eta) :
    ∃ N : ℕ, ∀ k ≥ N, ∀ p ∈ K, |F k p - G p| < eta := by
  by_contra hnot
  push Not at hnot
  choose k hk p hp hbad using hnot
  obtain ⟨z, hz, rho, hrho, hlim⟩ := hK.tendsto_subseq hp
  have hindex : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  have hF := hseq (k ∘ rho) (hindex.comp hrho.tendsto_atTop)
    (p ∘ rho) (fun n => hp (rho n)) z hz hlim
  have hwithin : Tendsto (p ∘ rho) atTop (𝓝[K] z) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall (fun n => hp (rho n))⟩
  have hGl := (hG z hz).tendsto.comp hwithin
  have herr : Tendsto (fun n => |F (k (rho n)) (p (rho n)) - G (p (rho n))|)
      atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, abs_zero] using (hF.sub hGl).abs
  exact (not_le.mpr heta) (ge_of_tendsto herr (Eventually.of_forall (fun n => hbad (rho n))))



theorem blowupSequence_terminal_scalar_uniform_chart (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (q : L.limit.sliceCarrier.carrier) (j : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hKU : K ⊆ {p | p ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm p ∈ L.exhaustion.space j})
    (eta : ℝ) (heta : 0 < eta) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ p ∈ K,
      |(E.flow.connection (t (L.subsequence k))).scalarCurvature
          (((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
              ((extChartAt (𝓡 3) q).symm p)).val) /
                (blowupSequence P E t x ht hR).scale (L.subsequence k) -
        (L.limit.flow.connection 0).scalarCurvature ((extChartAt (𝓡 3) q).symm p)| < eta := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have hscalar : Continuous (L.limit.flow.connection 0).scalarCurvature :=
    (Proofs.M09.scalarCurvature_contMDiff P.curvature (L.limit.flow.connection 0)).continuous
  have hchart : ContinuousOn (fun z => (L.limit.flow.connection 0).scalarCurvature
      ((extChartAt (𝓡 3) q).symm z)) K :=
    hscalar.comp_continuousOn ((continuousOn_extChartAt_symm
      (show L.limit.carrier.carrier from q)).mono (fun _ hp => (hKU hp).1))
  obtain ⟨N, hN⟩ := uniform_of_moving_point_limits
    (F := fun k p => (E.flow.connection (t (L.subsequence k))).scalarCurvature
      (((L.embedding k).forward 0
        ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
          ((extChartAt (𝓡 3) q).symm p)).val) /
            (blowupSequence P E t x ht hR).scale (L.subsequence k)) hK hchart
    (fun sigma hsigma pseq hpseq p hp hplim =>
      blowupSequence_terminal_scalar_tendsto_chart P E t x ht hR L q j K hK hKU
        sigma hsigma pseq hpseq p hp hplim) heta
  exact ⟨max j N, le_max_left _ _, fun k hk => hN k ((le_max_right _ _).trans hk)⟩




theorem blowupSequence_terminal_scalar_uniform_compact (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (j : ℕ) (K : Set L.limit.sliceCarrier.carrier) (hK : IsCompact K)
    (hKU : K ⊆ L.exhaustion.space j) (eta : ℝ) (heta : 0 < eta) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ y ∈ K,
      |(E.flow.connection (t (L.subsequence k))).scalarCurvature
          (((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val) /
              (blowupSequence P E t x ht hR).scale (L.subsequence k) -
        (L.limit.flow.connection 0).scalarCurvature y| < eta := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  let Good (k : ℕ) (y : L.limit.sliceCarrier.carrier) :=
    |(E.flow.connection (t (L.subsequence k))).scalarCurvature
        (((L.embedding k).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val) /
            (blowupSequence P E t x ht hR).scale (L.subsequence k) -
      (L.limit.flow.connection 0).scalarCurvature y| < eta
  have hlocal : ∀ q ∈ K, ∃ W ∈ 𝓝 q, ∀ᶠ k in atTop, ∀ y ∈ W, Good k y := by
    intro q hq
    let c := extChartAt (𝓡 3) (show L.limit.carrier.carrier from q)
    let V := c.target ∩ c.symm ⁻¹' L.exhaustion.space j
    have hV : IsOpen V := (continuousOn_extChartAt_symm
      (show L.limit.carrier.carrier from q)).isOpen_inter_preimage
        (isOpen_extChartAt_target (show L.limit.carrier.carrier from q))
        (L.exhaustion.space_open j)
    have hqV : c q ∈ V := ⟨mem_extChartAt_target (show L.limit.carrier.carrier from q),
      (congrArg (fun z : L.limit.sliceCarrier.carrier => z ∈ L.exhaustion.space j)
        (c.left_inv (mem_extChartAt_source (show L.limit.carrier.carrier from q)))).mpr
          (hKU hq)⟩
    obtain ⟨C, hC, hqC, hCV⟩ := exists_compact_between isCompact_singleton hV
      (singleton_subset_iff.mpr hqV)
    let W := c.source ∩ c ⁻¹' interior C
    have hchartsource : c.source =
        (chartAt (EuclideanSpace ℝ (Fin 3)) (show L.limit.carrier.carrier from q)).source :=
      extChartAt_source (𝓡 3) (show L.limit.carrier.carrier from q)
    have hccont : ContinuousOn c c.source := hchartsource.symm ▸
      (contMDiffOn_extChartAt (I := 𝓡 3) (n := ∞)
        (x := (show L.limit.carrier.carrier from q))).continuousOn
    have hW : IsOpen W := hccont.isOpen_inter_preimage
      (isOpen_extChartAt_source (show L.limit.carrier.carrier from q)) isOpen_interior
    have hqW : q ∈ W :=
      ⟨mem_extChartAt_source (show L.limit.carrier.carrier from q), hqC (mem_singleton _)⟩
    obtain ⟨N, _, hN⟩ := blowupSequence_terminal_scalar_uniform_chart P E t x ht hR L q j C hC
      (fun z hz => hCV hz) eta heta
    refine ⟨W, hW.mem_nhds hqW, ?_⟩
    filter_upwards [eventually_ge_atTop N] with k hk y hy
    have hcompare := hN k hk (c y) (interior_subset hy.2)
    exact (congrArg (Good k) (c.left_inv hy.1)).mp hcompare
  have hevent : ∀ᶠ k in atTop, ∀ y ∈ K, Good k y := by
    apply hK.induction_on (p := fun S => ∀ᶠ k in atTop, ∀ y ∈ S, Good k y)
    · exact Eventually.of_forall (fun _ _ hy => hy.elim)
    · intro S T hST hT
      exact hT.mono (fun _ hk y hy => hk y (hST hy))
    · intro S T hS hT
      filter_upwards [hS, hT] with k hkS hkT y hy
      exact hy.elim (hkS y) (hkT y)
    · intro y hy
      obtain ⟨W, hWy, hW⟩ := hlocal y hy
      exact ⟨W, mem_nhdsWithin_of_mem_nhds hWy, hW⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  exact ⟨max j N, le_max_left _ _, fun k hk => hN k ((le_max_right _ _).trans hk)⟩

end PoincareConjecture.M35.OrdinaryRealization
