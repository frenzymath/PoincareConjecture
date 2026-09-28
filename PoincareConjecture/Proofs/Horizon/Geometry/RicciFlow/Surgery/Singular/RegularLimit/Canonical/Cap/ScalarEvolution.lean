import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.ScalarRatio
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Compact.QuotientHomothety

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}

theorem tendstoUniformlyOn_scalarEvolution (G : RicciFlow n M J)
    {T : ℝ} (hT : T ∈ J) {A : Set M} (hA : IsCompact A) :
    TendstoUniformlyOn
      (fun t x => (G.connection t).laplacian (G.connection t).scalarCurvature x +
        2 * (G.connection t).ricciNormSq x)
      (fun x => (G.connection T).laplacian (G.connection T).scalarCurvature x +
        2 * (G.connection T).ricciNormSq x) (𝓝[J] T) A := by
  have hcontinuous : ContinuousOn
      (fun p : ℝ × M => (G.connection p.1).laplacian (G.connection p.1).scalarCurvature p.2 +
        2 * (G.connection p.1).ricciNormSq p.2) (J ×ˢ univ) :=
    (RicciFlowAnalysis.continuousOn_flow_timeDependentLaplacian G
      G.contMDiffOn_scalarCurvature).add
      (continuousOn_const.mul (RicciFlowAnalysis.continuousOn_flow_ricciNormSq G))
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨V, hV, hbound⟩ := hA.mem_uniformity_of_prod
    (f := fun t x => (G.connection t).laplacian (G.connection t).scalarCurvature x +
      2 * (G.connection t).ricciNormSq x)
    (hcontinuous.mono (prod_mono subset_rfl (subset_univ A)))
    hT (Metric.dist_mem_uniformity hε)
  filter_upwards [hV] with t ht x hx
  have hb : dist ((G.connection t).laplacian (G.connection t).scalarCurvature x +
      2 * (G.connection t).ricciNormSq x)
      ((G.connection T).laplacian (G.connection T).scalarCurvature x +
        2 * (G.connection T).ricciNormSq x) < ε := hbound t ht x hx
  rwa [dist_comm] at hb

theorem tendstoUniformlyOn_scalarCurvature_sq (G : RicciFlow n M J)
    {T : ℝ} (hT : T ∈ J) {A : Set M} (hA : IsCompact A) :
    TendstoUniformlyOn (fun t x => ((G.connection t).scalarCurvature x) ^ 2)
      (fun x => ((G.connection T).scalarCurvature x) ^ 2) (𝓝[J] T) A := by
  have hcontinuous : ContinuousOn
      (fun p : ℝ × M => ((G.connection p.1).scalarCurvature p.2) ^ 2) (J ×ˢ univ) :=
    G.contMDiffOn_scalarCurvature.continuousOn.pow 2
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  obtain ⟨V, hV, hbound⟩ := hA.mem_uniformity_of_prod
    (f := fun t x => ((G.connection t).scalarCurvature x) ^ 2)
    (hcontinuous.mono
      (prod_mono subset_rfl (subset_univ A))) hT (Metric.dist_mem_uniformity hε)
  filter_upwards [hV] with t ht x hx
  have hb : dist (((G.connection t).scalarCurvature x) ^ 2)
      (((G.connection T).scalarCurvature x) ^ 2) < ε := hbound t ht x hx
  rwa [dist_comm] at hb

end PoincareConjecture.RicciFlow

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem terminalFlow_scalarEvolution_of_lt
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (t : ℝ) (ht : t ∈ Ico H.reference.tMinus T) (x : H.regularRegion P04) :
    ((H.terminalFlow P04).connection t).laplacian
        ((H.terminalFlow P04).connection t).scalarCurvature x +
        2 * ((H.terminalFlow P04).connection t).ricciNormSq x =
      (F.connection t).laplacian (F.connection t).scalarCurvature
          (H.reference.forward t ht x) +
        2 * (F.connection t).ricciNormSq (H.reference.forward t ht x) := by
  let f : H.regularRegion P04 → (F.slice t).carrier :=
    fun x => H.reference.forward t ht x
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f :=
    (H.reference.forward_smooth t ht).comp contMDiff_subtype_val
  have hmetric : ∀ y ∈ (univ : Set (H.regularRegion P04)),
      ∀ v w : TangentSpace (𝓡 3) y,
      ((H.terminalFlow P04).metric t).inner y v w =
        (F.metric t).inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
          (mfderiv (𝓡 3) (𝓡 3) f y w) := by
    intro y _ v w
    have hd := mfderiv_comp y
      ((H.reference.forward_smooth t ht).mdifferentiable (by simp) y)
      ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) y)
    change mfderiv (𝓡 3) (𝓡 3) f y = _ at hd
    rw [hd, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      Poincare.Geometry.Manifold.RegularLevel.mfderiv_opens_subtypeVal]
    change ((H.terminalFlow P04).metric t).inner y v w =
      (F.metric t).inner (H.reference.forward t ht y)
        (mfderiv (𝓡 3) (𝓡 3) (H.reference.forward t ht) y v)
        (mfderiv (𝓡 3) (𝓡 3) (H.reference.forward t ht) y w)
    rw [H.reference.metric_pullback]
    exact H.terminalMetricFamily_inner_of_ne P04 ht.2.ne y v w
  rw [DeepHorn.scalar_laplacian_eq_of_local_isometry
    ((H.terminalFlow P04).connection t) (F.connection t)
    isOpen_univ hf.contMDiffOn hmetric (mem_univ x),
    LeviCivitaData.ricciNormSq_eq_of_local_isometry
      ((H.terminalFlow P04).connection t) (F.connection t)
      (P04.tensor_calculus 3 _ _ _) isOpen_univ hf.contMDiffOn hmetric (mem_univ x)]

theorem terminalFlow_scalarEvolution_at_terminal
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    (x : H.regularRegion P04) :
    ((H.terminalFlow P04).connection T).laplacian
        ((H.terminalFlow P04).connection T).scalarCurvature x +
        2 * ((H.terminalFlow P04).connection T).ricciNormSq x =
      (H.terminalConnection P04).laplacian (H.terminalConnection P04).scalarCurvature x +
        2 * (H.terminalConnection P04).ricciNormSq x :=
  congrArg (fun g : RiemannianMetric 3 (H.regularRegion P04) =>
    g.leviCivitaData.laplacian g.leviCivitaData.scalarCurvature x +
      2 * g.leviCivitaData.ricciNormSq x) (H.terminalMetricFamily_at_terminal P04)

theorem eventually_captured_cap_terminal_scalarEvolution_bound
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀) :
    ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
      ∀ N : CapCertificate (F.metric t), N.cap_constant ≤ H.constant →
      N.connection = F.connection t →
      H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
      H.reference.forward t ht x₀ ∈ N.core →
      ∃ b : ℝ, b < 2 * H.constant ∧
        ∀ x ∈ H.regularReferencePreimage P04 t ht N.carrier,
          |(H.terminalConnection P04).laplacian (H.terminalConnection P04).scalarCurvature x +
            2 * (H.terminalConnection P04).ricciNormSq x| ≤
              b * ((H.terminalConnection P04).scalarCurvature x) ^ 2 := by
  let G := H.terminalFlow P04
  let m := (H.terminalConnection P04).scalarCurvature x₀ / 2
  have hm : 0 < m := half_pos hx₀
  let a := m / (2 * H.constant)
  have ha : 0 < a := by dsimp [a]; positivity [H.constant_pos]
  let δ := H.constant * a ^ 2 / (4 * (H.constant + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity [H.constant_pos]
  have hδeq : (H.constant + 1) * δ = H.constant * a ^ 2 / 4 := by
    dsimp [δ]
    field_simp [ne_of_gt (add_pos H.constant_pos zero_lt_one)]
  have hfilter : 𝓝[<] T ≤ 𝓝[Ioc H.reference.tMinus T] T :=
    nhdsWithin_le_of_mem (Ioc_mem_nhdsLT H.reference.tMinus_lt)
  have hscalar : ∀ᶠ t in 𝓝[<] T, m < H.reference.scalar t x₀ :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually (Ioi_mem_nhds (half_lt_self hx₀))
  have hclose := Metric.tendstoUniformlyOn_iff.mp
    (H.tendstoUniformlyOn_terminal_scalarCurvature P04 hA) a ha
  have hevolution := hfilter (Metric.tendstoUniformlyOn_iff.mp
    (G.tendstoUniformlyOn_scalarEvolution ⟨H.reference.tMinus_lt, le_rfl⟩ hA) δ hδ)
  have hsquare := hfilter (Metric.tendstoUniformlyOn_iff.mp
    (G.tendstoUniformlyOn_scalarCurvature_sq ⟨H.reference.tMinus_lt, le_rfl⟩ hA) δ hδ)
  filter_upwards [hscalar, hclose, hevolution, hsquare] with t hscalar hclose hevolution hsquare
  intro ht N hconstant hconnection hcapture hx₀core
  refine ⟨3 * H.constant / 2, by nlinarith [H.constant_pos], ?_⟩
  intro x hx
  have hxA := H.regularReferencePreimage_subset P04 t ht N.carrier hcapture hx
  have hpos := N.scalar_pos _ hx
  have hratio := N.scalar_lt_constant_mul hx (N.core_subset_carrier hx₀core)
  rw [hconnection, H.reference.scalar_pullback, H.reference.scalar_pullback] at hratio
  rw [hconnection, H.reference.scalar_pullback] at hpos
  have hlower : m ≤ H.constant * H.reference.scalar t x :=
    hscalar.le.trans (hratio.le.trans (mul_le_mul_of_nonneg_right hconstant hpos.le))
  have herror := hclose x hxA
  rw [Real.dist_eq] at herror
  have hmul := mul_lt_mul_of_pos_left (abs_sub_lt_iff.mp herror).2 H.constant_pos
  have hacancel : H.constant * a = m / 2 := by
    dsimp [a]
    field_simp [H.constant_pos.ne']
  have hnewlower : a ≤ (H.terminalConnection P04).scalarCurvature x := by
    apply (mul_le_mul_iff_right₀ H.constant_pos).mp
    nlinarith
  have hnewpow : a ^ 2 ≤ ((H.terminalConnection P04).scalarCurvature x) ^ 2 :=
    pow_le_pow_left₀ ha.le hnewlower 2
  have hnum := hevolution x hxA
  rw [Real.dist_eq, H.terminalFlow_scalarEvolution_at_terminal P04,
    H.terminalFlow_scalarEvolution_of_lt P04 t ht] at hnum
  have hsq := hsquare x hxA
  rw [Real.dist_eq, H.terminalFlow_scalar_at_terminal P04,
    H.terminalFlow_scalar_of_ne P04 ht.2.ne] at hsq
  obtain ⟨b, hb, hbound⟩ := N.laplacian_bound
  have hold := (hbound _ hx).trans (mul_le_mul_of_nonneg_right
    (hb.le.trans hconstant) (sq_nonneg _))
  rw [hconnection, H.reference.scalar_pullback] at hold
  change |(F.connection t).laplacian (F.connection t).scalarCurvature
      (H.reference.forward t ht x) +
      2 * (F.connection t).ricciNormSq (H.reference.forward t ht x)| ≤
    H.constant * H.reference.scalar t x ^ 2 at hold
  have htriangle := abs_sub_abs_le_abs_sub
    ((H.terminalConnection P04).laplacian (H.terminalConnection P04).scalarCurvature x +
      2 * (H.terminalConnection P04).ricciNormSq x)
    ((F.connection t).laplacian (F.connection t).scalarCurvature
        (H.reference.forward t ht x) +
      2 * (F.connection t).ricciNormSq (H.reference.forward t ht x))
  have hsqmul := mul_lt_mul_of_pos_left (abs_sub_lt_iff.mp hsq).2 H.constant_pos
  have hmargin := mul_le_mul_of_nonneg_left hnewpow H.constant_pos.le
  have hnum' := htriangle.trans_lt hnum
  have hnonneg := mul_nonneg H.constant_pos.le
    (sq_nonneg ((H.terminalConnection P04).scalarCurvature x))
  nlinarith only [hold, hnum', hsqmul, hmargin, hδeq, hnonneg]

end PoincareConjecture.SingularTimeAssumptions
