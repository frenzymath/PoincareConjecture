import PoincareConjecture.Proofs.M08.MinimizingSequence
import PoincareConjecture.Proofs.M08.PathEnergy
import PoincareConjecture.Proofs.M08.PathTightness
import PoincareConjecture.Proofs.M08.ChartCoercivity
import PoincareConjecture.Proofs.M08.ChartCover
import PoincareConjecture.Proofs.M08.IntegratedEnergy
import Mathlib.Topology.Order.ProjIcc









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle intervalIntegral Topology ENNReal
open MeasureTheory Set Filter

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [mTop : TopologicalSpace M]
  [mChart : ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [mSmooth : IsManifold (𝓡 n) ∞ M] [mConnected : ConnectedSpace M] [mT3 : T3Space M]


theorem exists_backward_minimizing_uniform_limit {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u}) (hT : T ∈ J)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hτ₁ : 0 ≤ τ₁) (hordered : τ₁ < τ₂) (hτ₂ : τ₂ ≤ τmax) (p₁ p₂ : M) :
    letI : MetricSpace M := referenceMetricSpace (F.metric T)
    ∃ (p : ℕ → BackwardTimePath F T τ₁ τ₂) (γ : ℝ → M),
      (∀ k, (p k).curve τ₁ = p₁ ∧ (p k).curve τ₂ = p₂) ∧
      Antitone (fun k ↦ backwardLLength F T τ₁ τ₂ (p k).curve) ∧
      Tendsto (fun k ↦ backwardLLength F T τ₁ τ₂ (p k).curve)
        atTop (𝓝 (sInf (backwardActionValues F T τ₁ τ₂ p₁ p₂))) ∧
      Continuous γ ∧ γ (Real.sqrt τ₁) = p₁ ∧ γ (Real.sqrt τ₂) = p₂ ∧
      TendstoUniformlyOn (fun k ↦ squareReparameterizedCurve (p k).curve) γ atTop
        (sqrtParameterInterval τ₁ τ₂) := by
  letI : MetricSpace M := referenceMetricSpace (F.metric T)
  have hτmax : 0 ≤ τmax := hτ₁.trans (hordered.le.trans hτ₂)
  letI : CompleteSpace M := referenceMetricSpace_complete (F.metric T)
    (hcurvature.1 T ⟨sub_le_self T hτmax, le_rfl⟩)
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) (𝓡 n)
  obtain ⟨p, hp, hanti, hmin⟩ := exists_backward_minimizing_sequence
    hM04 hT hwindow hcurvature hτ₁ hordered hτ₂ p₁ p₂
  obtain ⟨K, hK, hRm⟩ := hcurvature.2
  let a := Real.sqrt τ₁
  let b := Real.sqrt τ₂
  have hab : a < b := Real.sqrt_lt_sqrt hτ₁ hordered
  let C := 2 * (Real.exp (2 * (n : ℝ) * K * τmax) *
    (backwardLLength F T τ₁ τ₂ (p 0).curve +
      (Real.sqrt τ₂ * (n : ℝ) ^ 2 * K) * (τ₂ - τ₁)))
  have hE (k : ℕ) :
      IntervalIntegrable
        (referenceSpeedSq (F.metric T) (squareReparameterizedCurve (p k).curve)) volume a b ∧
      (∫ s in a..b,
        referenceSpeedSq (F.metric T) (squareReparameterizedCurve (p k).curve) s) ≤ C := by
    have href := referenceWeightedEnergy_bound hM04 hwindow hK hRm (p k) hτ₂
    have hsquare := squarePath_referenceEnergy (p k) (F.metric T) href.1
    refine ⟨hsquare.1, ?_⟩
    rw [hsquare.2]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
    apply href.2.trans
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    exact add_le_add (hanti (Nat.zero_le k)) le_rfl
  let f : ℕ → Icc a b → M := fun k s ↦ squareReparameterizedCurve (p k).curve s
  have hmod (s t : Icc a b) (k : ℕ) :
      dist (f k s) (f k t) ≤ Real.sqrt C * Real.sqrt (dist s t) := by
    have h := dist_le_sqrt_energy (F.metric T) hab
      (squarePath_continuousOn (p k)) (squarePath_regular (p k))
      (hE k).1 (hE k).2 s s.2 t t.2
    simpa only [f, Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using h
  have hf : Equicontinuous f := by
    apply UniformEquicontinuous.equicontinuous
    apply Metric.uniformEquicontinuous_of_continuity_modulus
      (fun r ↦ Real.sqrt C * Real.sqrt r) _ f hmod
    simpa only [Real.sqrt_zero, mul_zero] using
      (tendsto_const_nhds.mul (Real.continuous_sqrt.tendsto (0 : ℝ)))
  let left : Icc a b := ⟨a, le_rfl, hab.le⟩
  let right : Icc a b := ⟨b, hab.le, le_rfl⟩
  have hleft (k : ℕ) : f k left = p₁ := by
    simpa only [f, left, a, squareReparameterizedCurve, Real.sq_sqrt hτ₁] using (hp k).1
  have hright (k : ℕ) : f k right = p₂ := by
    simpa only [f, right, b, squareReparameterizedCurve,
      Real.sq_sqrt (hτ₁.trans hordered.le)] using (hp k).2
  letI : PreconnectedSpace (Icc a b) := isPreconnected_iff_preconnectedSpace.mp
    isPreconnected_Icc
  obtain ⟨g, φ, hφ, hlim⟩ := exists_uniform_subsequence_of_anchored f hf left p₁ hleft
  let γ : ℝ → M := fun s ↦ g (projIcc a b hab.le s)
  have hγ : Continuous γ := g.continuous.comp continuous_projIcc
  have hγleft : γ a = p₁ := by
    have h := hlim.tendsto_at left
    simp only [hleft] at h
    have hg := tendsto_nhds_unique h tendsto_const_nhds
    simpa [γ, left] using hg
  have hγright : γ b = p₂ := by
    have h := hlim.tendsto_at right
    simp only [hright] at h
    have hg := tendsto_nhds_unique h tendsto_const_nhds
    simpa [γ, right] using hg
  refine ⟨fun k ↦ p (φ k), γ, fun k ↦ hp (φ k), hanti.comp_monotone hφ.monotone,
    hmin.comp hφ.tendsto_atTop, hγ, hγleft, hγright, ?_⟩
  change TendstoUniformlyOn (fun k ↦ squareReparameterizedCurve (p (φ k)).curve)
    γ atTop (Icc a b)
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  have hclamp : (fun s : Icc a b ↦ γ s) = g := by
    funext s
    change g (projIcc a b hab.le s) = g s
    rw [projIcc_of_mem _ s.2]
  simpa only [f, Function.comp_def, hclamp] using hlim


theorem finite_chartH1_limit {ι : Type*} [Fintype ι]
    (g : RiemannianMetric n M) (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i)
    (x : ι → M) (K : ι → Set M) (hK : ∀ i, IsCompact (K i))
    (hsrc : ∀ i, K i ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source)
    (α : ℕ → ℝ → M) (γ : ℝ → M)
    (hα : ∀ i k, ContinuousOn (α k) (Icc (a i) (b i)))
    (hreg : ∀ i k, ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (α k) (Ioo (a i) (b i)))
    (hαK : ∀ i k, MapsTo (α k) (Icc (a i) (b i)) (K i))
    (hγK : ∀ i, MapsTo γ (Icc (a i) (b i)) (K i))
    (hpoint : ∀ i s, s ∈ Icc (a i) (b i) →
      Tendsto (fun k ↦ α k s) atTop (𝓝 (γ s)))
    (hE : ∀ i k, IntervalIntegrable (referenceSpeedSq g (α k)) volume (a i) (b i))
    (C : ι → ℝ) (hbound : ∀ i k, (∫ s in a i..b i, referenceSpeedSq g (α k) s) ≤ C i) :
    ∃ (v : ∀ i, ℕ → ChartL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i))
      (w : ∀ i, ChartL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i))
      (B : ι → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i k, ‖v i k‖ ≤ B i ∧
        (v i k : ℝ → EuclideanSpace ℝ (Fin n)) =ᵐ[volume.restrict (Icc (a i) (b i))]
          deriv ((extChartAt (𝓡 n) (x i)) ∘ α k)) ∧
      (∀ i, ∀ s ∈ Icc (a i) (b i),
        extChartAt (𝓡 n) (x i) (γ s) = extChartAt (𝓡 n) (x i) (γ (a i)) +
          ∫ r in a i..s, w i r) ∧
      ∀ i, ∀ l : ChartL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i) →L[ℝ] ℝ,
        Tendsto (fun k ↦ l (v i (φ k))) atTop (𝓝 (l (w i))) := by
  classical
  choose c hc hcbound using fun i ↦ chart_velocity_L2_bound g (x i) (hK i) (hsrc i)
  choose hLp hvbound using fun i k ↦
    hcbound i (hab i) (α k) (hreg i k) (hαK i k) (hE i k) (hbound i k)
  let v : ∀ i, ℕ → ChartL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i) :=
    fun i k ↦ (hLp i k).toLp (deriv ((extChartAt (𝓡 n) (x i)) ∘ α k))
  letI : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  letI (i : ι) : TopologicalSpace.SeparableSpace
      (ChartL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i)) := inferInstance
  obtain ⟨φ, hφ, w, hweak⟩ := exists_finite_weak_subsequence v
    (fun i ↦ Real.sqrt ((c i)⁻¹ * C i)) hvbound
  refine ⟨v, w, (fun i ↦ Real.sqrt ((c i)⁻¹ * C i)), φ, hφ,
    (fun i k ↦ ⟨hvbound i k, (hLp i k).coeFn_toLp⟩), ?_, fun i ↦ (hweak i).2⟩
  intro i s hs
  apply chart_primitive_of_weak_limit
    (fun k ↦ (extChartAt (𝓡 n) (x i)) ∘ α (φ k))
    ((extChartAt (𝓡 n) (x i)) ∘ γ) (fun k ↦ v i (φ k)) (w i) _ _ (hweak i).2 hs
  · intro k r hr
    have hαsrc : ∀ t ∈ Icc (a i) (b i),
        α (φ k) t ∈ (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source := by
      intro t ht
      exact (hsrc i) (hαK i (φ k) ht)
    apply chart_primitive_of_deriv
      ((continuousOn_extChartAt (I := 𝓡 n) (x i)).comp (hα i (φ k))
        (fun t ht ↦ by simpa only [extChartAt_source] using hαsrc t ht)) _
      (hLp i (φ k)) hr
    intro t ht
    have hm := ((hreg i (φ k) t ht).contMDiffAt (isOpen_Ioo.mem_nhds ht)).mdifferentiableAt
      (by norm_num)
    exact ((mdifferentiableAt_extChartAt
      (hαsrc t (Ioo_subset_Icc_self ht))).comp t hm).differentiableAt.hasDerivAt
  · intro t ht
    have hsrc' : γ t ∈ (extChartAt (𝓡 n) (x i)).source := by
      simpa only [extChartAt_source] using hsrc i (hγK i ht)
    exact ((continuousAt_extChartAt' hsrc').tendsto.comp
      (hpoint i t ht)).comp hφ.tendsto_atTop

set_option synthInstance.maxHeartbeats 200000 in


theorem finite_chart_action_le {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {ι : Type*} [Fintype ι]
    (a b : ι → ℝ) (hab : ∀ i, a i ≤ b i) (x : ι → M)
    (K : ι → Set M) (hK : ∀ i, IsCompact (K i))
    (hsrc : ∀ i, K i ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source)
    (htime : ∀ i s, s ∈ Icc (a i) (b i) → T - s ^ 2 ∈ J)
    (α : ℕ → ℝ → M) (γ : ℝ → M)
    (hα : ∀ i k, ContinuousOn (α k) (Icc (a i) (b i)))
    (hγ : ∀ i, ContinuousOn γ (Icc (a i) (b i)))
    (hαK : ∀ i k, MapsTo (α k) (Icc (a i) (b i)) (K i))
    (hγK : ∀ i, MapsTo γ (Icc (a i) (b i)) (K i))
    (hlim : letI : MetricSpace M := referenceMetricSpace (F.metric T)
      ∀ i, TendstoUniformlyOn α γ atTop (Icc (a i) (b i)))
    (v : ∀ i, ℕ → ChartL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i))
    (w : ∀ i, ChartL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i))
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i) (hbound : ∀ i k, ‖v i k‖ ≤ C i)
    (hweak : ∀ i, ∀ l : ChartL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i) →L[ℝ] ℝ,
      Tendsto (fun k ↦ l (v i k)) atTop (𝓝 (l (w i))))
    (action : ℕ → ℝ) (L : ℝ) (haction : Tendsto action atTop (𝓝 L))
    (henergy : ∀ k,
      (∑ i : ι, ((∫ s in a i..b i, regularizedChartMetric F T (x i) (s, α k s)
          (v i k s) (v i k s)) +
        ∫ s in a i..b i, 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α k s)))
        ≤ action k) :
    (∑ i : ι, ((∫ s in a i..b i, regularizedChartMetric F T (x i) (s, γ s)
        (w i s) (w i s)) +
      ∫ s in a i..b i, 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (γ s))) ≤ L := by
  classical
  letI : MetricSpace M := referenceMetricSpace (F.metric T)
  let B i k s := regularizedChartMetric F T (x i) (s, α k s)
  let D i s := regularizedChartMetric F T (x i) (s, γ s)
  have hBcont (i : ι) (k : ℕ) : ContinuousOn (B i k) (Icc (a i) (b i)) :=
    (regularizedChartMetric_continuousOn F T (x i) (htime i) (hsrc i)).comp
      (continuousOn_id.prodMk (hα i k)) (fun s hs ↦ ⟨hs, hαK i k hs⟩)
  have hDcont (i : ι) : ContinuousOn (D i) (Icc (a i) (b i)) :=
    (regularizedChartMetric_continuousOn F T (x i) (htime i) (hsrc i)).comp
      (continuousOn_id.prodMk (hγ i)) (fun s hs ↦ ⟨hs, hγK i hs⟩)
  have hB (i : ι) (k : ℕ) :
      MemLp (B i k) ∞ (volume.restrict (Icc (a i) (b i))) :=
    continuousOn_memLp_top_Icc (f := B i k) (a := a i) (b := b i) (hBcont i k)
  have hD (i : ι) :
      MemLp (D i) ∞ (volume.restrict (Icc (a i) (b i))) :=
    continuousOn_memLp_top_Icc (f := D i) (a := a i) (b := b i) (hDcont i)
  let Qk i k := integratedFormMap _ ((hB i k).toLp (B i k))
  let Q i := integratedFormMap _ ((hD i).toLp (D i))
  have hQ (i : ι) : Tendsto (fun k ↦ ‖Qk i k - Q i‖) atTop (𝓝 (0 : ℝ)) := by
    apply integratedForm_tendsto_of_uniform (B i) (D i) (hB i) (hD i)
    exact uniform_composition_on_compact_core (hK i) _
      (regularizedChartMetric_continuousOn F T (x i) (htime i) (hsrc i)) α γ
      (Eventually.of_forall (hαK i)) (hγK i) (hlim i)
  have hQpos (i : ι) (z : ChartL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i)) :
      0 ≤ Q i z z := by
    apply integratedForm_nonneg (hD i) _ z
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact regularizedChartMetric_nonneg F T (x i) s (hsrc i (hγK i hs))
  have hQeq (i : ι) (z : ChartL2 (EuclideanSpace ℝ (Fin n)) (a i) (b i)) :
      Q i z z = ∫ s in a i..b i, D i s (z s) (z s) := by
    rw [intervalIntegral.integral_of_le (hab i), ← integral_Icc_eq_integral_Ioc]
    rw [integratedFormMap_apply]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp
      (E := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (f := D i) (hD i)] with s hs
    rw [hs]
  have hQkeq (i : ι) (k : ℕ) :
      Qk i k (v i k) (v i k) = ∫ s in a i..b i, B i k s (v i k s) (v i k s) := by
    rw [intervalIntegral.integral_of_le (hab i), ← integral_Icc_eq_integral_Ioc]
    rw [integratedFormMap_apply]
    apply integral_congr_ae
    filter_upwards [MemLp.coeFn_toLp
      (E := EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      (f := B i k) (hB i k)] with s hs
    rw [hs]
  let V : ι → ℝ × M → ℝ := fun _ z ↦
    2 * z.1 ^ 2 * (F.connection (T - z.1 ^ 2)).scalarCurvature z.2
  have hV (i : ι) : ContinuousOn (V i) (Icc (a i) (b i) ×ˢ K i) :=
    regularizedPotential_continuousOn F hM04 T (htime i)
  have hpotential (i : ι) : Tendsto (fun k ↦ ∫ s in a i..b i, V i (s, α k s)) atTop
      (𝓝 (∫ s in a i..b i, V i (s, γ s))) := by
    apply TendstoUniformlyOn.tendsto_intervalIntegral_of_continuousOn
    · apply Eventually.of_forall
      intro k
      rw [uIcc_of_le (hab i)]
      exact (hV i).comp (continuousOn_id.prodMk (hα i k))
        (fun s hs ↦ ⟨hs, hαK i k hs⟩)
    · rw [uIcc_of_le (hab i)]
      exact uniform_composition_on_compact_core (hK i) (V i) (hV i) α γ
        (Eventually.of_forall (hαK i)) (hγK i) (hlim i)
  have htotal := finite_quadratic_action_le v w C hC hbound hweak Q Qk hQpos hQ
    (fun k ↦ ∑ i, ∫ s in a i..b i, V i (s, α k s)) action
    (∑ i, ∫ s in a i..b i, V i (s, γ s)) L
    (tendsto_finsetSum Finset.univ (fun i _ ↦ hpotential i)) haction
    (fun k ↦ by simpa only [hQkeq, ← Finset.sum_add_distrib, B, V] using henergy k)
  simpa only [hQeq, ← Finset.sum_add_distrib, D, V] using htotal


theorem chart_piece_action_eq {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) {a b : ℝ} (hab : a ≤ b)
    (x : M) (α : ℝ → M) (hα : ContinuousOn α (Icc a b))
    (hreg : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 α (Ioo a b))
    (hsrc : MapsTo α (Icc a b) (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
    (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (hint : IntervalIntegrable (regularizedLIntegrand F T α) volume a b)
    (v : ChartL2 (EuclideanSpace ℝ (Fin n)) a b)
    (hv : (v : ℝ → EuclideanSpace ℝ (Fin n)) =ᵐ[volume.restrict (Icc a b)]
      deriv ((extChartAt (𝓡 n) x) ∘ α)) :
    (∫ s in a..b, regularizedChartMetric F T x (s, α s) (v s) (v s)) +
      (∫ s in a..b, 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s)) =
      ∫ s in a..b, regularizedLIntegrand F T α s := by
  let V := fun s ↦ 2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s)
  have hVcont : ContinuousOn V (Icc a b) :=
    (regularizedPotential_continuousOn F hM04 T (K := univ) htime).comp
      (continuousOn_id.prodMk hα) (fun s hs ↦ ⟨hs, mem_univ _⟩)
  have hV : IntervalIntegrable V volume a b := by
    apply hVcont.intervalIntegrable_of_Icc hab
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

private theorem sum_integral_fin_partition {m : ℕ} (t : Fin (m + 1) → ℝ)
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
    have hsum := ih (fun i ↦ t i.castSucc) (ht.comp (fun _ _ hij ↦ hij)) hfirst
    simpa only [Fin.castSucc_zero, Fin.succ_last] using
      hsum ▸ intervalIntegral.integral_add_adjacent_intervals hfirst hlast

set_option maxHeartbeats 800000 in

set_option synthInstance.maxHeartbeats 200000 in

theorem exists_backward_minimizing_chart_limit {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u}) (hT : T ∈ J)
    (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (hτ₁ : 0 ≤ τ₁) (hordered : τ₁ < τ₂) (hτ₂ : τ₂ ≤ τmax) (p₁ p₂ : M) :
    ∃ (γ : ℝ → M) (m : ℕ) (t : Fin (m + 1) → ℝ) (x : Fin m → M)
      (K : Fin m → Set M)
      (w : ∀ i : Fin m, ChartL2 (EuclideanSpace ℝ (Fin n)) (t i.castSucc) (t i.succ)),
      Continuous γ ∧ γ (Real.sqrt τ₁) = p₁ ∧ γ (Real.sqrt τ₂) = p₂ ∧
      Monotone t ∧ t 0 = Real.sqrt τ₁ ∧ t (Fin.last m) = Real.sqrt τ₂ ∧
      (∀ i, IsCompact (K i) ∧
        γ '' Icc (t i.castSucc) (t i.succ) ⊆ interior (K i) ∧
        K i ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) (x i)).source) ∧
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
  letI : LocallyCompactSpace M :=
    Manifold.locallyCompact_of_finiteDimensional (M := M) (𝓡 n)
  let a := Real.sqrt τ₁
  let b := Real.sqrt τ₂
  have hab : a < b := Real.sqrt_lt_sqrt hτ₁ hordered
  obtain ⟨p, γ, hp, hanti, hmin, hγ, hγa, hγb, hlim⟩ :=
    exists_backward_minimizing_uniform_limit hM04 hT hwindow hcurvature
      hτ₁ hordered hτ₂ p₁ p₂
  obtain ⟨m, t, x, K, N, ht, hta, htb, hK, htail⟩ :=
    exists_compact_partition_of_uniform_limit
      (fun x : M ↦ (chartAt (EuclideanSpace ℝ (Fin n)) x).source)
      (fun x ↦ (chartAt (EuclideanSpace ℝ (Fin n)) x).open_source)
      (fun y ↦ ⟨y, mem_chart_source _ y⟩) hab.le γ hγ
      (fun k ↦ squareReparameterizedCurve (p k).curve) hlim
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
    have hsum := sum_integral_fin_partition t ht (regularizedLIntegrand F T (α (φ k)))
      (by simpa only [hta, htb] using haction.1)
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
  refine ⟨γ, m, t, x, K, w, ?_⟩
  exact ⟨hγ, hγa, hγb, ht, hta, htb, hK, hprimitive, hLSC⟩

end PoincareConjecture.M08
