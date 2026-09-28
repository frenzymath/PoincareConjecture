import PoincareConjecture.Proofs.M32.Claim11_35.SliceCapContainment
import PoincareConjecture.Proofs.M32.Claim11_35.CapGraphObstruction
import PoincareConjecture.Proofs.M32.Claim11_34.NeckProductGraph.Graph

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u v

namespace PoincareConjecture.M32

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space FlowCarrier.t3Space

theorem exists_blowup_slice_cap_exclusion :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 200 ∧
      ∀ {S : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
        (G : GeneralizedBlowupConvergence S J) {t : ℝ}, t ∈ J →
      ∀ {C : Type v} [TopologicalSpace C] [T2Space C] [ConnectedSpace C]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) C] [IsManifold (𝓡 2) ∞ C]
        (gC : RiemannianMetric 2 C)
        (Phi : (C × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯ G.limit.carrier.carrier),
        (∀ (z : C × ℝ) (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
          (G.limit.flow.metric t).inner (Phi z)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi z v)
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) Phi z w) =
            gC.inner z.1 v.1 w.1 + v.2 * w.2) →
      ∀ {K : Set G.limit.carrier.carrier}, IsCompact K →
        (∀ x ∈ K, 0 < (G.limit.flow.connection t).scalarCurvature x) →
      ∀ {B : ℝ}, 0 < B →
        ∀ᶠ k in atTop, ∃ htk : t ∈ Icc (-G.exhaustion.time k) 0,
          K ⊆ G.exhaustion.space k ∧
          ∀ x ∈ K, ∀ N : CapCertificate ((S.flow (G.subsequence k)).metric
              ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))),
            N.epsilon ≤ epsilon₀ → N.cap_constant ≤ B →
            N.connection = (S.flow (G.subsequence k)).connection
              ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k)) →
            blowup_sliceEmbedding G k t htk x ∉ N.core := by
  obtain ⟨epsilon₀, hpos, hsmall, hgraph⟩ := exists_neckSlice_product_graph.{u, u, v}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro S J G t ht C topC t2C connC chartC smoothC gC Phi hproduct K hK hpositive B hB
  obtain ⟨Kplus, hplus, hKK, Lambda, hLambda, hcontain⟩ :=
    blowup_eventually_caps_contained_on_slice G ht hK hpositive hB
  let delta := 1 / (200 * Lambda)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hdeltaLambda : delta * Lambda ≤ (1 / 100 : ℝ) := by
    dsimp [delta]
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 200) hLambda)).mpr
    nlinarith
  filter_upwards [hcontain, blowup_eventually_sliceMetric_error G ht hplus
    (by norm_num : (0 : ℝ) < 1 / 2),
    blowup_eventually_sliceRicci_error G ht hplus hdelta] with k hc hm hr
  obtain ⟨htk, hsource, hcaps⟩ := hc
  obtain ⟨_, _, hmetric⟩ := hm
  obtain ⟨_, _, hricci⟩ := hr
  let E := blowup_sliceEmbedding G k t htk
  let gM := (S.flow (G.subsequence k)).metric
    ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))
  let DM := (S.flow (G.subsequence k)).connection
    ((S.base (G.subsequence k)).1 + t / S.scale (G.subsequence k))
  have hE : ContMDiffOn (𝓡 3) (𝓡 3) ∞ E E.source :=
    (blowup_sliceEmbedding_smooth G k t htk).1
  have hEi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ E.symm E.target :=
    (blowup_sliceEmbedding_smooth G k t htk).2
  have hmetric' : ∀ y ∈ Kplus, ∀ v : TangentSpace (𝓡 3) y,
      (G.limit.flow.metric t).inner y v v ≤ 2 * S.scale (G.subsequence k) *
        gM.inner (E y) (mfderiv (𝓡 3) (𝓡 3) E y v)
          (mfderiv (𝓡 3) (𝓡 3) E y v) := by
    intro y hy v
    have h := (abs_le.mp (hmetric y hy v)).1
    change -(1 / 2 * (G.limit.flow.metric t).inner y v v) ≤
      S.scale (G.subsequence k) *
        gM.inner (E y) (mfderiv (𝓡 3) (𝓡 3) E y v)
          (mfderiv (𝓡 3) (𝓡 3) E y v) - (G.limit.flow.metric t).inner y v v at h
    linarith
  have hricci' : ∀ y ∈ Kplus, ∀ v : TangentSpace (𝓡 3) y,
      |DM.ricci (E y) (mfderiv (𝓡 3) (𝓡 3) E y v)
          (mfderiv (𝓡 3) (𝓡 3) E y v) - (G.limit.flow.connection t).ricci y v v| ≤
        delta * (G.limit.flow.metric t).inner y v v := by
    intro y hy v
    exact hricci y hy v
  refine ⟨htk, hKK.trans hsource, ?_⟩
  intro x hx N hepsilon hconstant hconnection hcore
  obtain ⟨htarget, hinverse, hscale⟩ := hcaps x hx N hconstant hconnection hcore
  have ha : (0 : ℝ) ∈ Ioo (-N.boundary_neck.epsilon⁻¹) N.boundary_neck.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.boundary_neck.epsilon_pos),
      inv_pos.mpr N.boundary_neck.epsilon_pos⟩
  have hsphere (q : UnitTwoSphere) : N.boundary_neck.coordinate_map (q, 0) ∈ N.boundary_sphere := by
    rw [N.boundary_eq_neck_sphere, N.boundary_neck.central_sphere_eq]
    exact ⟨(q, 0), ⟨mem_univ _, mem_singleton _⟩, rfl⟩
  have htarget' (q : UnitTwoSphere) : N.boundary_neck.coordinate_map (q, 0) ∈ E.target :=
    htarget (N.boundary_subset (hsphere q))
  have hinverse' (q : UnitTwoSphere) : E.symm (N.boundary_neck.coordinate_map (q, 0)) ∈ Kplus :=
    hinverse (mem_image_of_mem _ (N.boundary_subset (hsphere q)))
  have hepsilon' : N.boundary_neck.epsilon ≤ epsilon₀ := by
    rw [N.boundary_neck_epsilon]
    exact hepsilon
  obtain ⟨d, H, _, hH, hrange⟩ := hgraph gM gC (G.limit.flow.metric t)
    (G.limit.flow.connection t) DM Phi hproduct E hE hEi N.boundary_neck ha
    hplus hsource (S.base_scalar_pos (G.subsequence k)) hLambda hdelta.le
    hscale hdeltaLambda hepsilon' htarget' hinverse' hmetric' hricci'
  apply cap_not_in_partial_product_with_graph_boundary N E htarget Phi.toHomeomorph H hH.continuous
  intro y hy
  rw [N.boundary_eq_neck_sphere, N.boundary_neck.central_sphere_eq] at hy
  obtain ⟨⟨q, a⟩, ha', rfl⟩ := hy
  have ha0 : a = 0 := ha'.2
  subst a
  have h := mem_range_self (f := fun q : UnitTwoSphere =>
    Phi.symm (E.symm (N.boundary_neck.coordinate_map (q, 0)))) q
  rw [hrange] at h
  exact h

end PoincareConjecture.M32
