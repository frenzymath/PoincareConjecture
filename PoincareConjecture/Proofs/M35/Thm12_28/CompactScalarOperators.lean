import PoincareConjecture.Proofs.M35.Thm12_28.SelectedScalarOperators
import PoincareConjecture.Proofs.M35.Thm12_28.CompactScalarConvergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Regularity
import PoincareConjecture.Proofs.M04.ScalarEvolutionCoefficients

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem continuous_scalarGradientNorm
    {M : Type*} [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hR : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ D.scalarCurvature) :
    Continuous (scalarGradientNorm g D) := by
  have h := (D.continuous_inner_gradient hR hR).sqrt
  convert h using 1
  ext x
  exact scalarGradientNorm_eq_gradient_norm D x

theorem continuous_scalar_evolution_slice
    {M : Type} [TopologicalSpace M] [ChartedSpace V M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] (P : M35StandardCapPredecessors) {J : Set ℝ}
    (F : RicciFlow 3 M J) {t : ℝ} (ht : t ∈ J) :
    Continuous (fun y => (F.connection t).laplacian (F.connection t).scalarCurvature y +
      2 * (F.connection t).ricciNormSq y) := by
  have hric : Continuous (fun y => (F.connection t).ricciNormSq y) := by
    have hspacetime : ContinuousOn
        (fun p : ℝ × M => (F.connection p.1).ricciNormSq p.2) (J ×ˢ univ) :=
      M04.continuousOn_flow_ricciNormSq (n := 3) (M := M) (J := J) F
    have hmap : MapsTo (fun y : M => (t, y)) univ (J ×ˢ univ) :=
      fun _ _ => ⟨ht, mem_univ _⟩
    have hcont : ContinuousOn (fun y : M => (t, y)) univ :=
      (continuous_const.prodMk continuous_id).continuousOn
    apply continuousOn_univ.mp
    exact ContinuousOn.comp
      (g := fun p : ℝ × M => (F.connection p.1).ricciNormSq p.2)
      (f := fun y : M => (t, y)) hspacetime hcont hmap
  exact ((F.connection t).continuous_laplacian
    (Proofs.M09.scalarCurvature_contMDiff P.curvature (F.connection t))).add
      (continuous_const.mul hric)

namespace OrdinaryRealization

theorem blowupSequence_terminal_scalar_operators_uniform_chart (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (q : L.limit.sliceCarrier.carrier) (j : ℕ)
    (K : Set V) (hK : IsCompact K)
    (hKU : K ⊆ {p | p ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm p ∈ L.exhaustion.space j})
    (eta : ℝ) (heta : 0 < eta) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
    let phi k z := ((L.embedding k).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ p ∈ K,
      let z := (extChartAt (𝓡 3) q).symm p
      |scalarGradientNorm (E.flow.metric (t (L.subsequence k)))
        (E.flow.connection (t (L.subsequence k))) (phi k z) / (Q k * Real.sqrt (Q k)) -
          scalarGradientNorm (L.limit.flow.metric 0) (L.limit.flow.connection 0) z| < eta ∧
      |((E.flow.connection (t (L.subsequence k))).laplacian
          (E.flow.connection (t (L.subsequence k))).scalarCurvature (phi k z) +
            2 * (E.flow.connection (t (L.subsequence k))).ricciNormSq (phi k z)) / Q k ^ 2 -
        ((L.limit.flow.connection 0).laplacian (L.limit.flow.connection 0).scalarCurvature z +
          2 * (L.limit.flow.connection 0).ricciNormSq z)| < eta := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  let c := extChartAt (𝓡 3) (show L.limit.carrier.carrier from q)
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let phi k z := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  have hc : ContinuousOn c.symm K :=
    (continuousOn_extChartAt_symm (show L.limit.carrier.carrier from q)).mono
      (fun _ hp => (hKU hp).1)
  have hgr0 := continuous_scalarGradientNorm (L.limit.flow.connection 0)
    (Proofs.M09.scalarCurvature_contMDiff P.curvature (L.limit.flow.connection 0))
  have hgr := hgr0.comp_continuousOn hc
  have hev0 := continuous_scalar_evolution_slice P L.limit.flow L.limit.zero_mem
  have hev := hev0.comp_continuousOn hc
  obtain ⟨Ng, hNg⟩ := uniform_of_moving_point_limits
    (F := fun k p => scalarGradientNorm (E.flow.metric (t (L.subsequence k)))
      (E.flow.connection (t (L.subsequence k))) (phi k (c.symm p)) /
        (Q k * Real.sqrt (Q k))) hK hgr
    (fun sigma hs pseq hps p hp hpl =>
      (blowupSequence_terminal_scalar_operators_tendsto_chart P E t x ht hR L q j K hK hKU
        sigma hs pseq hps p hp hpl).1) heta
  obtain ⟨Ne, hNe⟩ := uniform_of_moving_point_limits
    (F := fun k p => ((E.flow.connection (t (L.subsequence k))).laplacian
      (E.flow.connection (t (L.subsequence k))).scalarCurvature (phi k (c.symm p)) +
        2 * (E.flow.connection (t (L.subsequence k))).ricciNormSq (phi k (c.symm p))) /
          Q k ^ 2) hK hev
    (fun sigma hs pseq hps p hp hpl =>
      (blowupSequence_terminal_scalar_operators_tendsto_chart P E t x ht hR L q j K hK hKU
        sigma hs pseq hps p hp hpl).2) heta
  refine ⟨max j (max Ng Ne), le_max_left _ _, ?_⟩
  intro k hk p hp
  have hNgk : Ng ≤ k := (le_max_left Ng Ne).trans ((le_max_right _ _).trans hk)
  have hNek : Ne ≤ k := (le_max_right Ng Ne).trans ((le_max_right _ _).trans hk)
  exact ⟨hNg k hNgk p hp, hNe k hNek p hp⟩

theorem blowupSequence_terminal_scalar_operators_uniform_compact (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (j : ℕ) (K : Set L.limit.sliceCarrier.carrier) (hK : IsCompact K)
    (hKU : K ⊆ L.exhaustion.space j) (eta : ℝ) (heta : 0 < eta) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
    let phi k z := ((L.embedding k).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
    ∃ N : ℕ, j ≤ N ∧ ∀ k ≥ N, ∀ z ∈ K,
      |scalarGradientNorm (E.flow.metric (t (L.subsequence k)))
        (E.flow.connection (t (L.subsequence k))) (phi k z) / (Q k * Real.sqrt (Q k)) -
          scalarGradientNorm (L.limit.flow.metric 0) (L.limit.flow.connection 0) z| < eta ∧
      |((E.flow.connection (t (L.subsequence k))).laplacian
          (E.flow.connection (t (L.subsequence k))).scalarCurvature (phi k z) +
            2 * (E.flow.connection (t (L.subsequence k))).ricciNormSq (phi k z)) / Q k ^ 2 -
        ((L.limit.flow.connection 0).laplacian (L.limit.flow.connection 0).scalarCurvature z +
          2 * (L.limit.flow.connection 0).ricciNormSq z)| < eta := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  let phi k z := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  let Good (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
    |scalarGradientNorm (E.flow.metric (t (L.subsequence k)))
      (E.flow.connection (t (L.subsequence k))) (phi k z) / (Q k * Real.sqrt (Q k)) -
        scalarGradientNorm (L.limit.flow.metric 0) (L.limit.flow.connection 0) z| < eta ∧
    |((E.flow.connection (t (L.subsequence k))).laplacian
        (E.flow.connection (t (L.subsequence k))).scalarCurvature (phi k z) +
          2 * (E.flow.connection (t (L.subsequence k))).ricciNormSq (phi k z)) / Q k ^ 2 -
      ((L.limit.flow.connection 0).laplacian (L.limit.flow.connection 0).scalarCurvature z +
        2 * (L.limit.flow.connection 0).ricciNormSq z)| < eta
  have hlocal : ∀ q ∈ K, ∃ W ∈ 𝓝 q, ∀ᶠ k in atTop, ∀ y ∈ W, Good k y := by
    intro q hq
    let c := extChartAt (𝓡 3) (show L.limit.carrier.carrier from q)
    let U := c.target ∩ c.symm ⁻¹' L.exhaustion.space j
    have hU : IsOpen U := (continuousOn_extChartAt_symm
      (show L.limit.carrier.carrier from q)).isOpen_inter_preimage
        (isOpen_extChartAt_target (show L.limit.carrier.carrier from q))
        (L.exhaustion.space_open j)
    have hqU : c q ∈ U := ⟨mem_extChartAt_target (show L.limit.carrier.carrier from q),
      (congrArg (fun z : L.limit.sliceCarrier.carrier => z ∈ L.exhaustion.space j)
        (c.left_inv (mem_extChartAt_source (show L.limit.carrier.carrier from q)))).mpr
          (hKU hq)⟩
    obtain ⟨C, hC, hqC, hCU⟩ := exists_compact_between isCompact_singleton hU
      (singleton_subset_iff.mpr hqU)
    let W := c.source ∩ c ⁻¹' interior C
    have hsource : c.source =
        (chartAt V (show L.limit.carrier.carrier from q)).source :=
      extChartAt_source (𝓡 3) (show L.limit.carrier.carrier from q)
    have hccont : ContinuousOn c c.source := hsource.symm ▸
      (contMDiffOn_extChartAt (I := 𝓡 3) (n := ∞)
        (x := (show L.limit.carrier.carrier from q))).continuousOn
    have hW : IsOpen W := hccont.isOpen_inter_preimage
      (isOpen_extChartAt_source (show L.limit.carrier.carrier from q)) isOpen_interior
    have hqW : q ∈ W :=
      ⟨mem_extChartAt_source (show L.limit.carrier.carrier from q), hqC (mem_singleton _)⟩
    obtain ⟨N, _, hN⟩ := blowupSequence_terminal_scalar_operators_uniform_chart
      P E t x ht hR L q j C hC (fun z hz => hCU hz) eta heta
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

end OrdinaryRealization
end PoincareConjecture.M35
