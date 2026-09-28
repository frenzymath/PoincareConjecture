import PoincareConjecture.Proofs.M09.NormalizedSquareFamily
import PoincareConjecture.Proofs.M09.ForwardRegularizedContinuation
import PoincareConjecture.Proofs.M09.SqrtActionIntegrability









set_option autoImplicit false
set_option maxSynthPendingDepth 3
set_option maxHeartbeats 800000

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

noncomputable def normalizedBackwardFamily {J : Set ℝ} (F : RicciFlow n M J)
    (T τmax : ℝ) (p : M) (Z : TangentSpace (𝓡 n) p) : ℝ → M :=
  fun τ ↦ normalizedSquareFamily F T τmax p Z (Real.sqrt τ)

set_option backward.isDefEq.respectTransparency false in
theorem exists_normalizedBackwardPath {J : Set ℝ}
    [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (p : M) (Z : TangentSpace (𝓡 n) p) (b : ℝ) (hb : 0 < b) (hbmax : b < τmax) :
    ∃ P : BackwardTimePath F T 0 b,
      P.curve = normalizedBackwardFamily F T τmax p Z ∧
      Nonempty (RegularizedLGeodesicData P) := by
  let α := normalizedSquareFamily F T τmax p Z
  let γ := normalizedBackwardFamily F T τmax p Z
  let q0 : TangentBundle (𝓡 n) M := ⟨p, (2 : ℝ) • Z⟩
  let D := maximalRegularizedDomain F T τmax 0 q0
  let K := sqrtParameterInterval 0 b
  have hK : K = Set.Icc 0 (Real.sqrt b) := by simp [K, sqrtParameterInterval]
  have hD : IsOpen D := isOpen_maximalRegularizedDomain F T τmax 0 q0
  have hα : IsLocalRegularizedCurveOn F T α D :=
    maximalRegularizedCurve_isLocal F hM04 T τmax hτmax hwindow 0 q0
  have hforward : Set.Ico 0 (Real.sqrt τmax) ⊆ D :=
    Ico_subset_maximalRegularizedDomain F hM04 T τmax hτmax hwindow hcurvature q0
  have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb
  have hsqrtmax : Real.sqrt b < Real.sqrt τmax := Real.sqrt_lt_sqrt hb.le hbmax
  have hKD : K ⊆ D := by
    rw [hK]
    intro s hs
    exact hforward ⟨hs.1, hs.2.trans_lt hsqrtmax⟩
  have htime : K ⊆ Set.Ioo (-Real.sqrt τmax) (Real.sqrt τmax) := by
    rw [hK]
    intro s hs
    exact ⟨(neg_lt_zero.mpr (Real.sqrt_pos.mpr hτmax)).trans_le hs.1,
      hs.2.trans_lt hsqrtmax⟩
  have hKcompact : IsCompact K := hK ▸ isCompact_Icc
  have hKdiff : UniqueDiffOn ℝ K := hK ▸ uniqueDiffOn_Icc hsqrt
  obtain ⟨E, heq⟩ := exists_regularizedExtensionOn_compact F hM04 T τmax hτmax hwindow
    α D K hD hKD hKcompact hKdiff htime hα.smooth (fun s hs ↦ hα.equation s (hKD hs))
  have henergy : ContinuousOn (regularizedCurveEnergy F T α) K := by
    intro s hs
    exact (regularizedCurveEnergy_hasDerivAt F hM04 T τmax hτmax hwindow
      α D K hD hKD hKdiff hα.smooth E s hs (htime hs) (heq s hs)).continuousAt.continuousWithinAt
  have hαcontinuous : ContinuousOn α K := hα.smooth.continuousOn.mono hKD
  have htimeContinuous : ContinuousOn (fun s : ℝ ↦ T - s ^ 2) K :=
    (continuous_const.sub (continuous_id.pow 2)).continuousOn
  have hgraph : ContinuousOn (fun s : ℝ ↦ (T - s ^ 2, α s)) K :=
    htimeContinuous.prodMk hαcontinuous
  have hR : ContinuousOn (fun z : ℝ × M ↦ (F.connection z.1).scalarCurvature z.2)
      (J ×ˢ Set.univ) := (hM04.scalar_regular n M J F).continuousOn
  have hmaps : Set.MapsTo (fun s : ℝ ↦ (T - s ^ 2, α s)) K (J ×ˢ Set.univ) := by
    intro s hs
    exact ⟨hwindow (squareTime_mem_window T hτmax (htime hs)), Set.mem_univ _⟩
  have hscalar := hR.comp hgraph hmaps
  have hαdiff : ∀ s ∈ D, MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s :=
    fun s hs ↦ (hα.smooth.contMDiffAt (hD.mem_nhds hs)).mdifferentiableAt (by simp)
  have hintegrable : IntervalIntegrable (backwardLIntegrand F T γ) MeasureTheory.volume 0 b := by
    apply intervalIntegrable_backwardLIntegrand_comp_sqrt F T b hb α
    · intro s hs
      apply hαdiff s (hKD ?_)
      rw [hK]
      exact ⟨hs.1.le, hs.2.le⟩
    · simpa only [hK, Function.comp_def] using hscalar
    · simpa only [hK] using henergy
  have hsqrtD : Set.MapsTo Real.sqrt (Set.Icc 0 b) D := by
    intro τ hτ
    apply hKD
    rw [hK]
    exact ⟨Real.sqrt_nonneg τ, Real.sqrt_le_sqrt hτ.2⟩
  have hγcontinuous : ContinuousOn γ (Set.Icc 0 b) :=
    hα.smooth.continuousOn.comp Real.continuous_sqrt.continuousOn hsqrtD
  have hsqrtSmooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ Real.sqrt (Set.Ioo 0 b) := by
    intro τ hτ
    exact (Real.contDiffAt_sqrt hτ.1.ne').contMDiffAt.contMDiffWithinAt
  have hγsmooth : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ γ (Set.Ioo 0 b) :=
    hα.smooth.comp hsqrtSmooth (fun τ hτ ↦ hsqrtD (Set.Ioo_subset_Icc_self hτ))
  let P : BackwardTimePath F T 0 b := {
    curve := γ
    nonnegative := le_rfl
    ordered := hb
    terminal_mem := hwindow ⟨by linarith, le_rfl⟩
    time_mem := fun τ hτ ↦ hwindow ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
    continuous := hγcontinuous
    regular := hγsmooth.of_le (by simp)
    l_integrable := hintegrable
  }
  refine ⟨P, rfl, ⟨{
    path := {
      curve := α
      domain := D
      open_domain := hD
      interval_subset := hKD
      smooth := hα.smooth
      agrees := ?_
    }
    velocity_extension := E
    equation := heq
  }⟩⟩
  intro s hs
  have hs0 : 0 ≤ s := by simpa only [sqrtParameterInterval, Real.sqrt_zero] using hs.1
  change α s = α (Real.sqrt (s ^ 2))
  rw [Real.sqrt_sq hs0]

end PoincareConjecture.Proofs.M09
