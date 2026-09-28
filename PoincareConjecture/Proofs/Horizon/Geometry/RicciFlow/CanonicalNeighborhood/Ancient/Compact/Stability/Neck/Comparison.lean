import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Convergence.UniformJets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Scalar.Terminal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology
open Poincare.Analysis.Calculus

namespace PoincareConjecture.TerminalNeck

theorem exists_staticCylinder_comparison_tolerance
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ (B₀ B₁ : RoundCylinderTwoTensor),
      RoundCylinderClose δ 0 B₀ → RoundCylinderTensorSmoothOn ε B₁ →
      (∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
        ∀ j, j ≤ ⌊ε⁻¹⌋₊ → ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient B₁
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
              roundCylinderTensorCoefficient B₀
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η) →
      RoundCylinderClose ε 0 B₁ := by
  obtain ⟨C, hC, hCb⟩ := exists_evolvingCylinderJetErrorSquared_bound
    (J := Icc (-ε⁻¹) ε⁻¹) isCompact_Icc ⌊ε⁻¹⌋₊
  have hgap : 0 < ε ^ 2 - δ ^ 2 := by nlinarith
  let θ := (ε ^ 2 - δ ^ 2) / (2 * δ ^ 2)
  have hθ : 0 < θ := div_pos hgap (by positivity)
  have hθeq : θ * (2 * δ ^ 2) = ε ^ 2 - δ ^ 2 :=
    div_mul_cancel₀ _ (by positivity)
  let η := Real.sqrt (θ * (ε ^ 2 - δ ^ 2) / (4 * ((1 + θ) * C + 1)))
  have hη : 0 < η := Real.sqrt_pos.2 (by positivity)
  have hηsq : η ^ 2 = θ * (ε ^ 2 - δ ^ 2) / (4 * ((1 + θ) * C + 1)) :=
    Real.sq_sqrt (by positivity)
  have hηeq : (4 * ((1 + θ) * C + 1)) * η ^ 2 = θ * (ε ^ 2 - δ ^ 2) := by
    rw [hηsq, mul_div_cancel₀ _ (by positivity)]
  refine ⟨η, hη, ?_⟩
  intro B₀ B₁ hclose hsmooth hjet
  have hs₀ : RoundCylinderTensorSmoothOn ε B₀ := fun q a b =>
    (hclose.1 q a b).mono (prod_mono subset_rfl (DeepHorn.neckInterval_subset hδ hδε.le))
  refine ⟨hsmooth, (3 * ε ^ 2 + δ ^ 2) / 4, by nlinarith, ?_⟩
  intro z hz
  have herr : roundCylinderJetErrorSquared 0 (cylinderDifference 0 B₁ B₀)
      ⌊ε⁻¹⌋₊ z ≤ C * η ^ 2 := by
    apply hCb 0 (by constructor <;> norm_num) _ z ⟨hz.1.le, hz.2.le⟩ η hη.le
    · intro a b
      simp only [cylinderDifference_coefficient]
      have hp : (0, z.2) ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) z.1).target ×ˢ
          Ioo (-ε⁻¹) ε⁻¹ := by
        rw [roundCylinder_sphereChart_target]
        exact ⟨mem_univ _, hz⟩
      have hn := ((chartAt (EuclideanSpace ℝ (Fin 2)) z.1).open_target.prod
        isOpen_Ioo).mem_nhds hp
      exact ((hsmooth z.1 a b).contDiffAt hn).sub ((hs₀ z.1 a b).contDiffAt hn)
    · simpa only [cylinderDifference_coefficient] using hjet z hz
  have hlimit : roundCylinderJetErrorSquared 0 B₀ ⌊ε⁻¹⌋₊ z ≤ δ ^ 2 := by
    obtain ⟨_, bound, hb, hbound⟩ := hclose
    exact (DeepHorn.evolvingCylinderJetErrorSquared_mono (by norm_num) B₀ z
      (Nat.floor_mono ((inv_le_inv₀ (hδ.trans hδε) hδ).2 hδε.le))).trans
      ((hbound z (DeepHorn.neckInterval_subset hδ hδε.le hz)).trans hb.le)
  have hweighted := cylinderDifference_jetError_weighted_le (by norm_num : (0 : ℝ) < 1)
    B₁ B₀ hsmooth hs₀ ⌊ε⁻¹⌋₊ z hz hθ
  have hbound := hweighted.trans (add_le_add
    (mul_le_mul_of_nonneg_left hlimit (by positivity))
    (mul_le_mul_of_nonneg_left herr (by positivity)))
  apply (mul_le_mul_iff_right₀ hθ).mp
  have hηnonneg : 0 ≤ η ^ 2 := sq_nonneg _
  nlinarith

theorem eventually_roundCylinderClose_of_coefficientJets
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    {B₀ : RoundCylinderTwoTensor} {B : ℕ → RoundCylinderTwoTensor}
    (hclose : RoundCylinderClose δ 0 B₀)
    (hsmooth : ∀ᶠ k in atTop, RoundCylinderTensorSmoothOn ε (B k))
    (hjet : ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop,
      ∀ z : RoundCylinderSpace, z.2 ∈ Ioo (-ε⁻¹) ε⁻¹ →
        ∀ j, j ≤ ⌊ε⁻¹⌋₊ → ∀ a b : Fin 3,
          ‖iteratedFDeriv ℝ j (fun y =>
            roundCylinderTensorCoefficient (B k)
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
              roundCylinderTensorCoefficient B₀
                (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η) :
    ∀ᶠ k in atTop, RoundCylinderClose ε 0 (B k) := by
  obtain ⟨η, hη, hbound⟩ := exists_staticCylinder_comparison_tolerance hδ hδε
  filter_upwards [hsmooth, hjet η hη] with k hks hkj
  exact hbound B₀ (B k) hclose hks hkj

private theorem constant_jets_tendsto
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀)) (m : ℕ) (K : Set E) :
    TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fun _ : E => s k))
      (iteratedFDeriv ℝ m (fun _ : E => s₀)) atTop K := by
  cases m with
  | zero =>
    have h := ((continuousMultilinearCurryFin0 ℝ E ℝ).symm.continuous.tendsto s₀).comp hs
    exact h.tendstoUniformlyOn_const K
  | succ m =>
    simp_rw [iteratedFDeriv_succ_const]
    exact tendsto_const_nhds.tendstoUniformlyOn_const K

theorem smooth_zero_convergence_scalar_errors
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {e : ℕ → E → F} {A : E → F}
    (hA : ContDiffOn ℝ ∞ A U)
    (helocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (e i) W)
    (hejet : ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (e i)) (fun _ => 0) atTop K)
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀)) :
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (fun y => s i • e i y + (s i - s₀) • A y) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (fun y => s i • e i y + (s i - s₀) • A y))
      (fun _ => 0) atTop K := by
  obtain ⟨hfl, hfj⟩ := smooth_convergence_bilinear_on_finiteDimensional hU
    (ContinuousLinearMap.lsmul ℝ ℝ) (contDiffOn_const (c := s₀))
    (contDiffOn_const (c := (0 : F)))
    (fun x _ => ⟨univ, isOpen_univ, mem_univ x,
      Eventually.of_forall fun _ => contDiffOn_const⟩)
    helocal (fun m K _ _ => constant_jets_tendsto hs m K)
    (fun m K hK hKU => (hejet m K hK hKU).congr_right (fun _ _ => by simp))
  have hdelta : Tendsto (fun i => s i - s₀) atTop (𝓝 (0 : ℝ)) := by
    simpa only [sub_self] using hs.sub_const s₀
  obtain ⟨hgl, hgj⟩ := smooth_convergence_bilinear_on_finiteDimensional hU
    (ContinuousLinearMap.lsmul ℝ ℝ) (contDiffOn_const (c := (0 : ℝ))) hA
    (fun x _ => ⟨univ, isOpen_univ, mem_univ x,
      Eventually.of_forall fun _ => contDiffOn_const⟩)
    (fun x hx => ⟨U, hU, hx, Eventually.of_forall fun _ => hA⟩)
    (fun m K _ _ => constant_jets_tendsto hdelta m K)
    (fun m K _ _ => by
      apply Metric.tendstoUniformlyOn_iff.mpr
      intro ε hε
      exact Eventually.of_forall fun _ _ _ => by simpa only [dist_self] using hε)
  have hflocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (fun y => s i • e i y) W := by
    intro x hx
    obtain ⟨W, hW, hxW, _, hi⟩ := hfl x hx
    exact ⟨W, hW, hxW, hi⟩
  have hglocal : ∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (fun y => (s i - s₀) • A y) W := by
    intro x hx
    obtain ⟨W, hW, hxW, _, hi⟩ := hgl x hx
    exact ⟨W, hW, hxW, hi⟩
  constructor
  · intro x hx
    obtain ⟨V, hV, hxV, hf⟩ := hflocal x hx
    obtain ⟨W, hW, hxW, hg⟩ := hglocal x hx
    refine ⟨V ∩ W, hV.inter hW, ⟨hxV, hxW⟩, ?_⟩
    filter_upwards [hf, hg] with i hif hig
    exact (hif.mono inter_subset_left).add (hig.mono inter_subset_right)
  · intro m K hK hKU
    have h := (hfj m K hK hKU).add (hgj m K hK hKU)
    apply (h.congr ?_).congr_right ?_
    · filter_upwards [eventually_contDiffAt_on_compact hK hKU hflocal,
        eventually_contDiffAt_on_compact hK hKU hglocal] with i hif hig x hx
      exact (iteratedFDeriv_add_apply
        ((hif x hx).of_le (by exact_mod_cast le_top))
        ((hig x hx).of_le (by exact_mod_cast le_top))).symm
    · intro x hx
      simp

end PoincareConjecture.TerminalNeck

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}
  (hconv : M23TerminalMetricConvergence G e)
  (hfixed : ∀ j (s t : ℝ) (x : G.limit.carrier.carrier),
    s ≤ 0 → t ≤ 0 → x ∈ G.exhaustion j →
      ((e j).toFun (s, x)).2 = ((e j).toFun (t, x)).2)

include hconv hfixed

theorem smooth_zero_convergence_terminal_normalized_parametrized
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (d : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3))
    {U : Set E} (hU : IsOpen U) {f : E → G.limit.carrier.carrier}
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡 3) ∞ f U)
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀)) :
    let A := fun k y => s k •
      ((S.term (G.subsequence k)).flow.flow.metric 0).parametrizedCoefficients
        (fun x => ((e k).toFun (0, f x)).2) y -
      s₀ • (G.limit.flow.flow.metric 0).parametrizedCoefficients f y
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (A k)) (fun _ => 0) atTop K := by
  let B := fun k y => ((S.term (G.subsequence k)).flow.flow.metric 0).parametrizedCoefficients
    (fun x => ((e k).toFun (0, f x)).2) y
  let B₀ := (G.limit.flow.flow.metric 0).parametrizedCoefficients f
  obtain ⟨hloc, hjet⟩ := hconv.smooth_zero_convergence_movingTime_parametrized
    hfixed (J := {0}) isCompact_singleton (by simp) (fun _ => 0) (by simp) d hU hf
  have hB₀ : ContDiffOn ℝ ∞ B₀ U := fun x hx =>
    ((G.limit.flow.flow.metric 0).contDiffAt_parametrizedCoefficients
      (hf.contMDiffAt (hU.mem_nhds hx))).contDiffWithinAt
  have hc := TerminalNeck.smooth_zero_convergence_scalar_errors hU hB₀ hloc hjet hs
  have heq (k : ℕ) : (fun y => s k • (B k y - B₀ y) + (s k - s₀) • B₀ y) =
      (fun y => s k • B k y - s₀ • B₀ y) := by
    ext y v w
    change s k * (B k y v w - B₀ y v w) + (s k - s₀) * B₀ y v w =
      s k * B k y v w - s₀ * B₀ y v w
    ring
  change (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
    ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (fun y => s k • B k y - s₀ • B₀ y) W) ∧ _
  constructor
  · intro x hx
    obtain ⟨W, hW, hxW, hk⟩ := hc.1 x hx
    refine ⟨W, hW, hxW, hk.mono fun k hks => ?_⟩
    change ContDiffOn ℝ ∞ (fun y => s k • (B k y - B₀ y) + (s k - s₀) • B₀ y) W at hks
    simpa only [heq k] using hks
  · intro m K hK hKU
    exact (hc.2 m K hK hKU).congr (Eventually.of_forall fun k x _ =>
      congrArg (fun f => iteratedFDeriv ℝ m f x) (heq k))

theorem smooth_zero_convergence_terminal_normalized_changing_parametrized
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (d : E ≃L[ℝ] EuclideanSpace ℝ (Fin 3))
    {U V : Set E} (hU : IsOpen U) (hV : IsOpen V)
    {f : E → G.limit.carrier.carrier}
    (hf : ContMDiffOn 𝓘(ℝ, E) (𝓡 3) ∞ f U)
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀))
    {c : ℕ → E → E}
    (hclocal : ∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (c k) W)
    (hcbound : ∀ K, IsCompact K → K ⊆ V → ∀ m, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (c k) x‖ ≤ C)
    (hctarget : ∀ K, IsCompact K → K ⊆ V → ∃ T,
      IsCompact T ∧ T ⊆ U ∧ ∀ᶠ k in atTop, MapsTo (c k) K T) :
    let A := fun k y => s k •
      ((S.term (G.subsequence k)).flow.flow.metric 0).parametrizedCoefficients
        (fun x => ((e k).toFun (0, f (c k x))).2) y -
      s₀ • (G.limit.flow.flow.metric 0).parametrizedCoefficients (f ∘ c k) y
    (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W) ∧
    ∀ m K, IsCompact K → K ⊆ V → TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ m (A k)) (fun _ => 0) atTop K := by
  let F := fun k y => ((e k).toFun (0, f y)).2
  let B := fun k => ((S.term (G.subsequence k)).flow.flow.metric 0).parametrizedCoefficients (F k)
  let B₀ := (G.limit.flow.flow.metric 0).parametrizedCoefficients f
  let D := fun k y => (s k • B k (c k y) - s₀ • B₀ (c k y)).bilinearComp
    (fderiv ℝ (c k) y) (fderiv ℝ (c k) y)
  let A := fun k y => s k •
    ((S.term (G.subsequence k)).flow.flow.metric 0).parametrizedCoefficients (F k ∘ c k) y -
    s₀ • (G.limit.flow.flow.metric 0).parametrizedCoefficients (f ∘ c k) y
  obtain ⟨hloc, hjet⟩ := hconv.smooth_zero_convergence_terminal_normalized_parametrized
    hfixed d hU hf hs
  obtain ⟨hDlocal, hDjet⟩ := smooth_zero_convergence_pullback_of_bounded hV
    hloc hclocal hjet hcbound hctarget
  have hnear (K : Set E) (hK : IsCompact K) (hKV : K ⊆ V) :
      ∃ W, IsOpen W ∧ K ⊆ W ∧ ∀ᶠ k in atTop, EqOn (D k) (A k) W := by
    obtain ⟨K', hK', hKK', hK'V⟩ := exists_compact_between hK hV hKV
    obtain ⟨T, hT, hTU, hmap⟩ := hctarget K' hK' hK'V
    obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
      (hT.image_of_continuousOn (hf.continuousOn.mono hTU))
    refine ⟨interior K', isOpen_interior, hKK', ?_⟩
    filter_upwards [hmap, eventually_ge_atTop j,
      eventually_contDiffAt_on_compact hK' hK'V hclocal] with k hkmap hkj hkc x hx
    have hxT := hkmap (interior_subset hx)
    have hfx := hf.contMDiffAt (hU.mem_nhds (hTU hxT))
    have hF : MDifferentiableAt 𝓘(ℝ, E) (𝓡 3) (F k) (c k x) :=
      (((e k).terminalSpatialMap_contMDiffAt (G.exhaustion_open k) (t := 0) le_rfl
        (G.exhaustion_monotone hkj (hj (mem_image_of_mem f hxT)))).comp
          (c k x) hfx).mdifferentiableAt (by simp)
    have hc := (hkc x (interior_subset hx)).differentiableAt (by simp)
    have hb := ((S.term (G.subsequence k)).flow.flow.metric 0).parametrizedCoefficients_comp_of_eventuallyEq
      hF hc Filter.EventuallyEq.rfl
    have hb₀ := (G.limit.flow.flow.metric 0).parametrizedCoefficients_comp_of_eventuallyEq
      (hfx.mdifferentiableAt (by simp)) hc Filter.EventuallyEq.rfl
    ext v w
    exact congrArg₂ (fun a b => s k * a - s₀ * b)
      (congrArg (fun T => T v w) hb) (congrArg (fun T => T v w) hb₀)
  change (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
    ∀ᶠ k in atTop, ContDiffOn ℝ ∞ (A k) W) ∧ _
  constructor
  · intro x hx
    obtain ⟨W, hW, hxW, _, hk⟩ := hDlocal x hx
    obtain ⟨W', hW', hxW', heq⟩ := hnear {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    refine ⟨W ∩ W', hW.inter hW', ⟨hxW, hxW' (mem_singleton x)⟩, ?_⟩
    filter_upwards [hk, heq] with k hks hkeq
    exact (hks.mono inter_subset_left).congr (fun y hy => (hkeq hy.2).symm)
  · intro m K hK hKV
    obtain ⟨W, hW, hKW, heq⟩ := hnear K hK hKV
    apply (hDjet m K hK hKV).congr
    filter_upwards [heq] with k hk x hx
    exact (eqOn_iteratedFDeriv_of_isOpen hW hk m) (hKW hx)

theorem smooth_zero_convergence_terminal_normalized_cylinder_parametrizations
    {δ : ℝ} {Φ : RoundCylinderSpace → G.limit.carrier.carrier}
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹))
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀))
    (p : UnitTwoSphere) (q : ℕ → UnitTwoSphere)
    (hpq : ∀ i, ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2) :
    let U : Set RoundCylinderCoordinates :=
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ Ioo (-δ⁻¹) δ⁻¹
    let F := fun i (x : RoundCylinderCoordinates) =>
      Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2)
    let A := fun i x => s i •
      ((S.term (G.subsequence i)).flow.flow.metric 0).parametrizedCoefficients
        (fun y => ((e i).toFun (0, F i y)).2) x -
      s₀ • (G.limit.flow.flow.metric 0).parametrizedCoefficients (F i) x
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (A i) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (A i)) (fun _ => 0) atTop K := by
  let U : Set RoundCylinderCoordinates :=
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 3 ×ˢ Ioo (-δ⁻¹) δ⁻¹
  let V : Set RoundCylinderCoordinates :=
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ Ioo (-δ⁻¹) δ⁻¹
  have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_Ioo
  have hV : IsOpen V := Metric.isOpen_ball.prod isOpen_Ioo
  let f := fun x : RoundCylinderCoordinates =>
    Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) p).symm x.1, x.2)
  let F := fun i (x : RoundCylinderCoordinates) =>
    Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2)
  let c := fun i => roundCylinderCoordinateTransition p (q i)
  let A := fun i x => s i •
    ((S.term (G.subsequence i)).flow.flow.metric 0).parametrizedCoefficients
      (fun y => ((e i).toFun (0, F i y)).2) x -
    s₀ • (G.limit.flow.flow.metric 0).parametrizedCoefficients (F i) x
  let D := fun i x => s i •
    ((S.term (G.subsequence i)).flow.flow.metric 0).parametrizedCoefficients
      (fun y => ((e i).toFun (0, f (c i y))).2) x -
    s₀ • (G.limit.flow.flow.metric 0).parametrizedCoefficients (f ∘ c i) x
  let d : RoundCylinderCoordinates ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hf : ContMDiffOn 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ f U :=
    hΦ.comp (cylinderChart_symm_smooth p).contMDiffOn (fun x hx => ⟨mem_univ _, hx.2⟩)
  obtain ⟨hDlocal, hDjet⟩ := hconv.smooth_zero_convergence_terminal_normalized_changing_parametrized
    hfixed d hU hV hf hs
    (fun x hx => ⟨V, hV, hx, Eventually.of_forall fun i =>
      (contDiffOn_roundCylinderCoordinateTransition p (q i) (hpq i)).mono
        (prod_mono subset_rfl (subset_univ _))⟩)
    (fun K hK hKV m => by
      obtain ⟨C, _, hC⟩ := exists_uniform_roundCylinderCoordinateTransition_jet_bound
        p q hpq hK (fun x hx => ⟨(hKV hx).1, mem_univ _⟩) m
      exact ⟨C, Eventually.of_forall hC⟩)
    (fun K hK hKV => by
      refine ⟨Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 2 ×ˢ (Prod.snd '' K),
        (isCompact_closedBall _ _).prod (hK.image continuous_snd), ?_, ?_⟩
      · intro x hx
        refine ⟨Metric.mem_ball.mpr
          ((Metric.mem_closedBall.mp hx.1).trans_lt (by norm_num)), ?_⟩
        rcases hx.2 with ⟨y, hy, hyx⟩
        exact hyx ▸ (hKV hy).2
      · apply Eventually.of_forall
        intro i x hx
        constructor
        · simpa only [Metric.mem_closedBall, dist_zero_right] using
            norm_roundCylinderCoordinateTransition_fst_le_two p (q i) (hpq i)
              (show x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ univ
                from ⟨(hKV hx).1, mem_univ _⟩)
        · change x.2 ∈ Prod.snd '' K
          exact mem_image_of_mem Prod.snd hx)
  have heq (i : ℕ) : EqOn (D i) (A i) V := by
    intro x hx
    have hpair := roundCylinderCoordinateTransition_chart_inverse_eventuallyEq
      p (q i) (hpq i) ⟨hx.1, mem_univ _⟩
    have hf : (f ∘ c i) =ᶠ[𝓝 x] F i := hpair.fun_comp Φ
    have hsource : (fun y => ((e i).toFun (0, f (c i y))).2) =ᶠ[𝓝 x]
        (fun y => ((e i).toFun (0, F i y)).2) :=
      hf.fun_comp (fun z => ((e i).toFun (0, z)).2)
    exact congrArg₂ (fun v w => s i • v - s₀ • w)
      (((S.term (G.subsequence i)).flow.flow.metric 0).parametrizedCoefficients_congr_of_eventuallyEq hsource)
      ((G.limit.flow.flow.metric 0).parametrizedCoefficients_congr_of_eventuallyEq hf)
  change (∀ x ∈ V, ∃ W, IsOpen W ∧ x ∈ W ∧
    ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (A i) W) ∧ _
  constructor
  · intro x hx
    obtain ⟨W, hW, hxW, hk⟩ := hDlocal x hx
    refine ⟨V ∩ W, hV.inter hW, ⟨hx, hxW⟩, ?_⟩
    exact hk.mono fun i hi => (hi.mono inter_subset_right).congr
      (fun y hy => (heq i hy.1).symm)
  · intro m K hK hKV
    exact (hDjet m K hK hKV).congr (Eventually.of_forall fun i x hx =>
      (eqOn_iteratedFDeriv_of_isOpen hV (heq i) m) (hKV hx))

theorem smooth_zero_convergence_terminal_normalized_cylinder_coefficients
    {δ : ℝ} {Φ : RoundCylinderSpace → G.limit.carrier.carrier}
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹))
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀))
    (p : UnitTwoSphere) (q : ℕ → UnitTwoSphere)
    (hpq : ∀ i, ‖(q i : EuclideanSpace ℝ (Fin 3)) - p‖ < 1 / 2)
    (v w : Fin 3) :
    let U : Set RoundCylinderCoordinates :=
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ Ioo (-δ⁻¹) δ⁻¹
    let B := fun i z v w => s i *
      roundCylinderPullback ((S.term (G.subsequence i)).flow.flow.metric 0)
        (fun z => ((e i).toFun (0, Φ z)).2) z v w
    let B₀ := fun z v w => s₀ * roundCylinderPullback (G.limit.flow.flow.metric 0) Φ z v w
    let A := fun i x =>
      roundCylinderTensorCoefficient (B i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w -
      roundCylinderTensorCoefficient B₀ (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w
    (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
      ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (A i) W) ∧
    ∀ m K, IsCompact K → K ⊆ U → TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ m (A i)) (fun _ => 0) atTop K := by
  let U : Set RoundCylinderCoordinates :=
    Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) (1 / 2) ×ˢ Ioo (-δ⁻¹) δ⁻¹
  have hU : IsOpen U := Metric.isOpen_ball.prod isOpen_Ioo
  have hstrip : IsOpen (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹ : Set RoundCylinderSpace) :=
    isOpen_univ.prod isOpen_Ioo
  let f := fun i (z : RoundCylinderSpace) => ((e i).toFun (0, Φ z)).2
  let F := fun i (x : RoundCylinderCoordinates) =>
    Φ ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2)
  let E := fun i x => s i •
    ((S.term (G.subsequence i)).flow.flow.metric 0).parametrizedCoefficients
      (fun y => ((e i).toFun (0, F i y)).2) x -
    s₀ • (G.limit.flow.flow.metric 0).parametrizedCoefficients (F i) x
  let B := fun i z v w => s i *
    roundCylinderPullback ((S.term (G.subsequence i)).flow.flow.metric 0) (f i) z v w
  let B₀ := fun z v w => s₀ * roundCylinderPullback (G.limit.flow.flow.metric 0) Φ z v w
  let A := fun i x =>
    roundCylinderTensorCoefficient (B i) (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w -
    roundCylinderTensorCoefficient B₀ (chartAt (EuclideanSpace ℝ (Fin 2)) (q i)) x v w
  let L := (ContinuousLinearMap.apply ℝ ℝ (roundCylinderCoordinateBasis w)).comp
    (ContinuousLinearMap.apply ℝ (RoundCylinderCoordinates →L[ℝ] ℝ) (roundCylinderCoordinateBasis v))
  obtain ⟨hElocal, hEjet⟩ := hconv.smooth_zero_convergence_terminal_normalized_cylinder_parametrizations
    hfixed hΦ hs p q hpq
  obtain ⟨hDlocal, hDjet⟩ := smooth_convergence_continuousLinearMap_comp L hU
    (contDiffOn_const (c := (0 : RoundCylinderCoordinates →L[ℝ] RoundCylinderCoordinates →L[ℝ] ℝ)))
    hElocal (fun m K hK hKU => (hEjet m K hK hKU).congr_right (fun _ _ => by simp))
  have hnear (K : Set RoundCylinderCoordinates) (hK : IsCompact K) (hKU : K ⊆ U) :
      ∃ W, IsOpen W ∧ K ⊆ W ∧ ∀ᶠ i in atTop, EqOn (L ∘ E i) (A i) W := by
    obtain ⟨D, hD, hKD, hDU⟩ := exists_compact_between hK hU hKU
    have hcompact : IsCompact (univ ×ˢ (Prod.snd '' D) : Set RoundCylinderSpace) :=
      isCompact_univ.prod (hD.image continuous_snd)
    have hdomain : univ ×ˢ (Prod.snd '' D) ⊆
        (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹ : Set RoundCylinderSpace) := by
      rintro z ⟨hz, y, hy, hyz⟩
      exact ⟨hz, hyz ▸ (hDU hy).2⟩
    obtain ⟨j, hj⟩ := G.exists_exhaustion_superset
      (hcompact.image_of_continuousOn (hΦ.continuousOn.mono hdomain))
    refine ⟨interior D, isOpen_interior, hKD, ?_⟩
    filter_upwards [eventually_ge_atTop j] with i hji x hx
    have hmem : F i x ∈ G.exhaustion i := G.exhaustion_monotone hji
      (hj (mem_image_of_mem Φ ⟨mem_univ _, mem_image_of_mem Prod.snd (interior_subset hx)⟩))
    have hΦx : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
        ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2) :=
      hΦ.contMDiffAt (hstrip.mem_nhds ⟨mem_univ _, (hDU (interior_subset hx)).2⟩)
    have hfs : MDifferentiableAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) (f i)
        ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2) :=
      (((e i).terminalSpatialMap_contMDiffAt (G.exhaustion_open i) (t := 0) le_rfl hmem).comp
        ((chartAt (EuclideanSpace ℝ (Fin 2)) (q i)).symm x.1, x.2) hΦx).mdifferentiableAt (by simp)
    have hsource := roundCylinderTensorCoefficient_pullback_eq
      ((S.term (G.subsequence i)).flow.flow.metric 0) (q i) (f i) x hfs v w
    have hlimit := roundCylinderTensorCoefficient_pullback_eq
      (G.limit.flow.flow.metric 0) (q i) Φ x (hΦx.mdifferentiableAt (by simp)) v w
    exact (congrArg₂ (fun a b => s i * a - s₀ * b) hsource hlimit).symm
  change (∀ x ∈ U, ∃ W, IsOpen W ∧ x ∈ W ∧
    ∀ᶠ i in atTop, ContDiffOn ℝ ∞ (A i) W) ∧ _
  constructor
  · intro x hx
    obtain ⟨V, hV, hxV, hk⟩ := hDlocal x hx
    obtain ⟨W, hW, hxW, heq⟩ := hnear {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    refine ⟨V ∩ W, hV.inter hW, ⟨hxV, hxW (mem_singleton x)⟩, ?_⟩
    filter_upwards [hk, heq] with i hi hEq
    exact (hi.mono inter_subset_left).congr (fun y hy => (hEq hy.2).symm)
  · intro m K hK hKU
    obtain ⟨W, hW, hKW, heq⟩ := hnear K hK hKU
    apply ((hDjet m K hK hKU).congr ?_).congr_right (fun _ _ => by simp [Function.comp_def])
    filter_upwards [heq] with i hi x hx
    exact (eqOn_iteratedFDeriv_of_isOpen hW hi m) (hKW hx)

theorem eventually_terminalCylinder_normalized_coefficientJets
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    {Φ : RoundCylinderSpace → G.limit.carrier.carrier}
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹))
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀))
    (m : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ k in atTop, ∀ z : RoundCylinderSpace, z.2 ∈ Icc (-ε⁻¹) ε⁻¹ →
      ∀ j, j ≤ m → ∀ a b : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient
              (fun z v w => s k *
                roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
                  (fun z => ((e k).toFun (0, Φ z)).2) z v w)
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b -
            roundCylinderTensorCoefficient
              (fun z v w => s₀ * roundCylinderPullback (G.limit.flow.flow.metric 0) Φ z v w)
              (chartAt (EuclideanSpace ℝ (Fin 2)) z.1) y a b) (0, z.2)‖ ≤ η := by
  have hall := TerminalNeck.eventually_uniform_coefficientJets_of_locally_moving
    (I := ({0} : Set ℝ)) (J := Icc (-ε⁻¹) ε⁻¹)
    (B₀ := fun _ z v w => s₀ * roundCylinderPullback (G.limit.flow.flow.metric 0) Φ z v w)
    (B := fun k _ z v w => s k *
      roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
        (fun z => ((e k).toFun (0, Φ z)).2) z v w) ?_ m hη
  · exact hall.mono fun k hk z hz => hk 0 (mem_singleton 0) z hz
  · intro p q hpq τ hτ a b j
    have hc := hconv.smooth_zero_convergence_terminal_normalized_cylinder_coefficients
      hfixed hΦ hs p q hpq a b
    apply hc.2 j _ (isCompact_singleton.prod isCompact_Icc)
    rintro ⟨x, z⟩ ⟨hx, hz⟩
    have hx0 : x = 0 := mem_singleton_iff.mp hx
    subst x
    have hinv : ε⁻¹ < δ⁻¹ := (inv_lt_inv₀ (hδ.trans hδε) hδ).mpr hδε
    exact ⟨Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2),
      (neg_lt_neg hinv).trans_le hz.1, hz.2.trans_lt hinv⟩

theorem eventually_terminalCylinder_normalizedClose
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    {Φ : RoundCylinderSpace → G.limit.carrier.carrier}
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹))
    {s : ℕ → ℝ} {s₀ : ℝ} (hs : Tendsto s atTop (𝓝 s₀))
    (hclose : RoundCylinderClose δ 0
      (fun z v w => s₀ * roundCylinderPullback (G.limit.flow.flow.metric 0) Φ z v w)) :
    ∀ᶠ k in atTop, RoundCylinderClose ε 0
      (fun z v w => s k *
        roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
          (fun z => ((e k).toFun (0, Φ z)).2) z v w) := by
  apply TerminalNeck.eventually_roundCylinderClose_of_coefficientJets hδ hδε hclose
  · filter_upwards [eventually_terminalCylinder_tensorSmoothOn (G := G) (e := e) hδ hδε hΦ]
      with k hk q a b
    exact contDiffOn_const.mul (hk 0 q a b)
  · intro η hη
    exact (hconv.eventually_terminalCylinder_normalized_coefficientJets hfixed hδ hδε hΦ hs
      ⌊ε⁻¹⌋₊ hη).mono fun k hk z hz => hk z ⟨hz.1.le, hz.2.le⟩

theorem eventually_terminalCylinder_scalarClose
    {δ ε : ℝ} (hδ : 0 < δ) (hδε : δ < ε)
    {Φ : RoundCylinderSpace → G.limit.carrier.carrier}
    (hΦ : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ Φ
      (univ ×ˢ Ioo (-δ⁻¹) δ⁻¹))
    (p : G.limit.carrier.carrier)
    (hclose : RoundCylinderClose δ 0 (fun z v w =>
      (G.limit.flow.flow.connection 0).scalarCurvature p *
        roundCylinderPullback (G.limit.flow.flow.metric 0) Φ z v w)) :
    ∀ᶠ k in atTop, RoundCylinderClose ε 0 (fun z v w =>
      ((S.term (G.subsequence k)).flow.flow.connection 0).scalarCurvature
          ((e k).toFun (0, p)).2 *
        roundCylinderPullback ((S.term (G.subsequence k)).flow.flow.metric 0)
          (fun z => ((e k).toFun (0, Φ z)).2) z v w) := by
  have hfixed0 : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2 :=
    fun k t ht x hx => hfixed k t 0 x ht le_rfl hx
  have hprod := hconv.tendsto_terminal_scalarCurvature_prod hfixed0 p
  have hp : Tendsto (fun k : ℕ => (k, p)) atTop (atTop ×ˢ 𝓝 p) :=
    tendsto_id.prodMk tendsto_const_nhds
  have hscalar := hprod.comp hp
  exact hconv.eventually_terminalCylinder_normalizedClose hfixed hδ hδε hΦ hscalar hclose

end M23TerminalMetricConvergence
end PoincareConjecture
