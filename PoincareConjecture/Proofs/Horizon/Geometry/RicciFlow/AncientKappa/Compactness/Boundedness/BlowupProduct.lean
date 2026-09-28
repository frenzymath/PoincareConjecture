import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Line
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Factor
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.TerminalNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Rescaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Curvature.SphereCover











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance productCarrierConnected {n : ℕ} (C : FlowCarrier n) :
    ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected

variable {M : Type} [TopologicalSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]


structure SelectedAncientRescalings {b : ℝ} (F : RicciFlow 3 M (Iic b))
    (κ : ℝ) (p : M) where
  center : ℕ → M
  radius : ℕ → ℝ
  flow : ℕ → RicciFlow 3 M (Iic 0)
  scalar_pos : ∀ i, 0 < (F.connection b).scalarCurvature (center i)
  radius_pos : ∀ i, 0 < radius i
  homothety : ∀ i s, MetricHomothetyCalculus
    (F.metric (b + s / (F.connection b).scalarCurvature (center i)))
    ((flow i).metric s) (Diffeomorph.refl (𝓡 3) M ∞)
    ((F.connection b).scalarCurvature (center i))
  complete : ∀ i t, t ≤ 0 → MetricComplete ((flow i).metric t)
  nonnegative : ∀ i t, t ≤ 0 → ∀ x,
    ((flow i).connection t).NonnegativeCurvatureOperator x
  noncollapsed : ∀ i, AncientKappaNoncollapsed (flow i) κ
  normalized : ∀ i, ((flow i).connection 0).scalarCurvature (center i) = 1
  scalar_base_le : ∀ i t, t ≤ 0 → ((flow i).connection t).scalarCurvature (center i) ≤ 1
  curvature_bound : ∀ i t, t ≤ 0 → ∀ x ∈ ((flow i).metric 0).ball (center i)
    (radius i * Real.sqrt ((F.connection b).scalarCurvature (center i))),
      |((flow i).connection t).curvatureTensorNorm x| ≤ 4
  centers_escape : Tendsto (fun i => ((F.metric b).edist p (center i)).toReal) atTop atTop
  scalars_diverge : Tendsto (fun i => (F.connection b).scalarCurvature (center i)) atTop atTop
  radii_diverge : Tendsto (fun i => radius i *
    Real.sqrt ((F.connection b).scalarCurvature (center i))) atTop atTop
  distances_diverge : Tendsto (fun i => ((F.metric b).edist p (center i)).toReal *
    Real.sqrt ((F.connection b).scalarCurvature (center i))) atTop atTop
  relative_radius_tends_zero : Tendsto
    (fun i => radius i / ((F.metric b).edist p (center i)).toReal) atTop (𝓝 0)



structure RoundProductBlowup {b κ : ℝ} {F : RicciFlow 3 M (Iic b)} {p : M}
    (S : SelectedAncientRescalings F κ p) (δ : ℝ) where
  convergence : AncientPointedGeometricConvergence
    (fun _ => FlowCarrier.ofConnectedManifold 3 M)
    (fun i t => (S.flow i).metric (t - δ)) S.center δ
  complete : ∀ t < δ, convergence.limitCarrier.metricComplete (convergence.limitFlow.metric t)
  curvature_bound : ∀ t < δ, ∀ x,
    (convergence.limitFlow.connection t).curvatureTensorNorm x ≤ 4
  nonnegative : ∀ t < δ, ∀ x,
    (convergence.limitFlow.connection t).NonnegativeCurvatureOperator x
  scalar_base_ge : (1 / 2 : ℝ) ≤
    (convergence.limitFlow.connection 0).scalarCurvature convergence.base
  solution : AncientKappaSolution 3 convergence.limitCarrier.carrier
  solution_kappa : solution.kappa = κ / 27
  solution_metric : solution.flow.metric = convergence.limitFlow.metric
  line : ℝ → convergence.limitCarrier.carrier
  line_edist : ∀ s t, (convergence.limitFlow.metric 0).edist (line s) (line t) =
    ENNReal.ofReal |s - t|
  line_center : line 0 = convergence.base
  surface : FlowCarrier.{0} 2
  factor : AncientKappaSolution 2 surface.carrier
  factor_kappa : factor.kappa = κ / 54
  round : TwoDimensionalAncientRoundCertificate factor
  product : (surface.carrier × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
    convergence.limitCarrier.carrier
  product_metric : ∀ t ≤ 0, ∀ (z : surface.carrier × ℝ)
    (v w : TangentSpace ((𝓡 2).prod 𝓘(ℝ, ℝ)) z),
    (convergence.limitFlow.metric t).inner (product z)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) product z v)
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) product z w) =
        (factor.flow.metric t).inner z.1 v.1 w.1 + v.2 * w.2
  product_curvature : ∀ t ≤ 0, ∀ x,
    (factor.flow.connection t).curvatureTensorNorm (product.symm x).1 =
      (convergence.limitFlow.connection t).curvatureTensorNorm x

private theorem curvatureNorm_eq_of_metric_eq
    {X : Type} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    [IsManifold (𝓡 3) ∞ X] {g h : RiemannianMetric 3 X}
    (D : LeviCivitaData g) (E : LeviCivitaData h) (heq : g = h) (x : X) :
    D.curvatureTensorNorm x = E.curvatureTensorNorm x := by
  subst h
  exact D.horizon_curvatureTensorNorm_eq E x

namespace SelectedAncientRescalings

variable {b κ : ℝ} {F : RicciFlow 3 M (Iic b)} {p : M}
  (S : SelectedAncientRescalings F κ p)



theorem terminal_metric_eq_rescaled (i : ℕ) :
    (S.flow i).metric 0 = rescaledMetric (F.metric b)
      ((F.connection b).scalarCurvature (S.center i)) (S.scalar_pos i) := by
  let g := F.metric b
  let h := (S.flow i).metric 0
  let Q := (F.connection b).scalarCurvature (S.center i)
  have hnn (a : RiemannianMetric 3 M) (x : M) (v : TangentSpace (𝓡 3) x) :
      0 ≤ a.inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (a.pos x v hv).le
  have hself (x : M) (v : TangentSpace (𝓡 3) x) : h.inner x v v = Q * g.inner x v v := by
    have hh := (S.homothety i 0).tangent_norm_sq x v
    simpa only [Diffeomorph.coe_refl, id_eq, mfderiv_id,
      ContinuousLinearMap.id_apply, zero_div, add_zero, RiemannianMetric.tangentNorm,
      Real.sq_sqrt (hnn _ _ _)] using hh
  have hinner (x : M) (v w : TangentSpace (𝓡 3) x) :
      h.inner x v w = Q * g.inner x v w := by
    have hh := hself x (v + w)
    simp only [map_add, add_apply] at hh
    rw [h.symm x w v, g.symm x w v, hself x v, hself x w] at hh
    linarith
  have heq : h.inner = (rescaledMetric g Q (S.scalar_pos i)).inner := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    exact hinner x v w
  have hext {a c : RiemannianMetric 3 M} (hh : a.inner = c.inner) : a = c := by
    cases a
    cases c
    cases hh
    rfl
  exact hext heq




theorem exists_originalSliceNeck (i : ℕ)
    (N : EpsilonNeck ((S.flow i).metric 0)) (hscale : N.scale = 1) :
    ∃ N' : EpsilonNeck (F.metric b),
      N'.epsilon = N.epsilon ∧
      N'.scale = 1 / Real.sqrt ((F.connection b).scalarCurvature (S.center i)) ∧
      N'.center = N.center ∧ N'.carrier = N.carrier ∧
      N'.coordinate_map = N.coordinate_map ∧ N'.coordinate_inverse = N.coordinate_inverse ∧
      N'.central_sphere = N.central_sphere := by
  obtain ⟨A, hεA, hsA, hcA, hcarrierA, hmapA, hinverseA, hsphereA⟩ :=
    EpsilonNeck.exists_of_metric_eq (S.terminal_metric_eq_rescaled i) N
  obtain ⟨B, hεB, hsB, hcB, hcarrierB, hmapB, hinverseB, hsphereB⟩ :=
    EpsilonNeck.exists_of_rescaledMetric _ (S.scalar_pos i) A
  exact ⟨B, hεB.trans hεA, by rw [hsB, hsA, hscale], hcB.trans hcA,
    hcarrierB.trans hcarrierA, hmapB.trans hmapA, hinverseB.trans hinverseA,
    hsphereB.trans hsphereA⟩



theorem exists_roundProductBlowup
    (P : M23NormalizedKappaCompactnessPredecessors) (hκ : 0 < κ)
    (hc : MetricComplete (F.metric b))
    (hop : ∀ x, (F.connection b).NonnegativeCurvatureOperator x)
    (hmono : ∀ s t, s ≤ t → t ≤ b → ∀ x,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ, 0 < δ ∧ δ < 1 ∧ δ ≤ η ∧ Nonempty (RoundProductBlowup S δ) := by
  let C := fun _ : ℕ => FlowCarrier.ofConnectedManifold 3 M
  let L := fun i => S.radius i * Real.sqrt ((F.connection b).scalarCurvature (S.center i))
  obtain ⟨δ, hδ, hδone, hδη, G, hcomplete, hbound, hoperator, hscalar⟩ :=
    RawAncientSequence.exists_complete_bounded_nonflat_interior_geometric_limit_of_time_cap
      C S.flow S.center P hκ S.complete S.nonnegative S.noncollapsed L S.radii_diverge
      S.curvature_bound S.normalized S.scalar_base_le η hη
  have hmonoS (i : ℕ) := scalar_monotone_of_terminalHomothety
    (S.scalar_pos i) (S.homothety i) hmono
  obtain ⟨K, hKκ, hKmetric⟩ := RawAncientSequence.exists_ancientKappaSolution_on_closedPast
    C S.flow S.center P hκ hδ S.nonnegative S.noncollapsed hmonoS G hcomplete hbound
    hoperator (lt_of_lt_of_le (by norm_num) hscalar)
  letI := G.limitCarrier.metricSpaceOf (G.limitFlow.metric 0)
  obtain ⟨γ, hγ, hγzero⟩ := F.exists_line_of_closed_selected_rescalings P hc hop p
    S.center S.radius (fun i => (F.connection b).scalarCurvature (S.center i))
    S.radius_pos S.scalar_pos S.flow S.homothety S.complete S.nonnegative
    S.curvature_bound S.centers_escape S.distances_diverge S.radii_diverge
    S.relative_radius_tends_zero hδ G (hcomplete 0 hδ)
  have hγed (s t : ℝ) : (G.limitFlow.metric 0).edist (γ s) (γ t) =
      ENNReal.ofReal |s - t| := by
    have h := hγ.edist_eq s t
    change (G.limitFlow.metric 0).edist (γ s) (γ t) = edist s t at h
    simpa only [edist_dist, Real.dist_eq] using h
  have hKnorm (t : ℝ) (x : G.limitCarrier.carrier) :
      (K.flow.connection t).curvatureTensorNorm x =
        (G.limitFlow.connection t).curvatureTensorNorm x :=
    curvatureNorm_eq_of_metric_eq (K.flow.connection t) (G.limitFlow.connection t)
      (congrFun hKmetric t) x
  have hKbound : ∀ t ≤ 0, ∀ x, (K.flow.connection t).curvatureTensorNorm x ≤ 4 := by
    intro t ht x
    rw [hKnorm]
    exact hbound t (ht.trans_lt hδ) x
  obtain ⟨D, A, hAκ, ⟨hround⟩, e, hemetric, henorm⟩ :=
    K.exists_compact_round_surface_product_of_minimizing_line P (by norm_num) hKbound
      G.base γ (by intro s t; rw [congrFun hKmetric 0]; exact hγed s t)
  refine ⟨δ, hδ, hδone, hδη, ⟨{
    convergence := G
    complete := hcomplete
    curvature_bound := hbound
    nonnegative := hoperator
    scalar_base_ge := hscalar
    solution := K
    solution_kappa := hKκ
    solution_metric := hKmetric
    line := γ
    line_edist := hγed
    line_center := hγzero
    surface := D
    factor := A
    factor_kappa := by rw [hAκ, hKκ]; ring
    round := hround
    product := e
    product_metric := ?_
    product_curvature := ?_
  }⟩⟩
  · intro t ht z v w
    rw [← congrFun hKmetric t]
    exact hemetric t ht z v w
  · intro t ht x
    exact (henorm t ht x).trans (hKnorm t x)






theorem exists_terminal_epsilonNeck_threshold
    (P : M23NormalizedKappaCompactnessPredecessors)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ η > 0, ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 → δ ≤ η →
      ∀ G : AncientPointedGeometricConvergence
          (fun _ => FlowCarrier.ofConnectedManifold 3 M)
          (fun i t => (S.flow i).metric (t - δ)) S.center δ,
        G.limitCarrier.metricComplete (G.limitFlow.metric 0) →
        (1 / 2 : ℝ) ≤ (G.limitFlow.connection 0).scalarCurvature G.base →
      ∀ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
          G.limitCarrier.carrier) (q : UnitTwoSphere),
        Φ (q, 0) = G.base →
        (fun z v w => (G.limitFlow.connection 0).scalarCurvature G.base *
          roundCylinderPullback (G.limitFlow.metric 0) Φ z v w) =
            EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop, ∃ N : EpsilonNeck ((S.flow (G.subsequence i)).metric 0),
          N.epsilon = ε ∧ N.scale = 1 ∧ N.center = S.center (G.subsequence i) ∧
          N.connection = (S.flow (G.subsequence i)).connection 0 ∧
          N.coordinate_map = (fun z => G.embedding i (Φ z)) := by
  exact RawAncientSequence.exists_terminal_epsilonNeck_threshold
    (fun _ => FlowCarrier.ofConnectedManifold 3 M) S.flow S.center P
    S.complete S.nonnegative
    (fun i => S.radius i * Real.sqrt ((F.connection b).scalarCurvature (S.center i)))
    S.radii_diverge S.curvature_bound S.normalized S.scalar_base_le hε hεhalf



theorem original_scales_tendsto_zero :
    Tendsto (fun i => 1 / Real.sqrt ((F.connection b).scalarCurvature (S.center i)))
      atTop (𝓝 0) := by
  simpa only [one_div, Function.comp_def] using
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp S.scalars_diverge)




theorem exists_roundProductBlowup_with_terminal_necks
    (P : M23NormalizedKappaCompactnessPredecessors) (hκ : 0 < κ)
    (hc : MetricComplete (F.metric b))
    (hop : ∀ x, (F.connection b).NonnegativeCurvatureOperator x)
    (hmono : ∀ s t, s ≤ t → t ≤ b → ∀ x,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x)
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ δ, 0 < δ ∧ δ < 1 ∧ ∃ B : RoundProductBlowup S δ,
      ∀ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
          B.convergence.limitCarrier.carrier) (q : UnitTwoSphere),
        Φ (q, 0) = B.convergence.base →
        (fun z v w => (B.convergence.limitFlow.connection 0).scalarCurvature
          B.convergence.base * roundCylinderPullback (B.convergence.limitFlow.metric 0)
            Φ z v w) = EvolvingRoundCylinderMetric 0 →
        ∀ᶠ i in atTop, ∃ N : EpsilonNeck (F.metric b),
          N.epsilon = ε ∧
          N.scale = 1 / Real.sqrt ((F.connection b).scalarCurvature
            (S.center (B.convergence.subsequence i))) ∧
          N.center = S.center (B.convergence.subsequence i) ∧
          N.coordinate_map = (fun z => B.convergence.embedding i (Φ z)) := by
  obtain ⟨η, hη, hterminal⟩ := S.exists_terminal_epsilonNeck_threshold P hε hεhalf
  obtain ⟨δ, hδ, hδone, hδη, ⟨B⟩⟩ := S.exists_roundProductBlowup P hκ hc hop hmono η hη
  refine ⟨δ, hδ, hδone, B, ?_⟩
  intro Φ q hq hround
  have hnecks := hterminal hδ hδone.le hδη B.convergence (B.complete 0 hδ)
    B.scalar_base_ge Φ q hq hround
  filter_upwards [hnecks] with i hi
  obtain ⟨N, hNε, hNs, hNcenter, _, hNmap⟩ := hi
  obtain ⟨A, hAε, hAs, hAcenter, _, hAmap, _, _⟩ :=
    S.exists_originalSliceNeck (B.convergence.subsequence i) N hNs
  exact ⟨A, hAε.trans hNε, hAs, hAcenter.trans hNcenter, hAmap.trans hNmap⟩

end SelectedAncientRescalings





theorem exists_selected_roundProductBlowup
    (P : M23NormalizedKappaCompactnessPredecessors)
    {b κ : ℝ} (F : RicciFlow 3 M (Iic b)) (hκ : 0 < κ)
    (hc : ∀ t ≤ b, MetricComplete (F.metric t))
    (hop : ∀ t ≤ b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hmono : ∀ s t, s ≤ t → t ≤ b → ∀ x,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x)
    (hnc : ∀ t ≤ b, ∀ p : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ 3) ≤ calibratedMetricVolume (F.metric t)
        ((F.metric t).ball p r))
    (p : M) (hunbounded : ¬ BddAbove (range (F.connection b).scalarCurvature)) :
    ∃ S : SelectedAncientRescalings F κ p,
      ∀ η > 0, ∃ δ, 0 < δ ∧ δ < 1 ∧ δ ≤ η ∧ Nonempty (RoundProductBlowup S δ) := by
  obtain ⟨q, r, H, hsource, hd, hQ, hL, hD, hsmall⟩ :=
    F.exists_escaping_normalized_ancient_rescaling_sequence P hc hop
      (fun s hs x => hmono s b hs le_rfl x) hnc p hunbounded
  choose hpos hr hcal hcH hopH hncH hnorm hbase hbound using hsource
  let S : SelectedAncientRescalings F κ p := {
    center := q
    radius := r
    flow := H
    scalar_pos := hpos
    radius_pos := hr
    homothety := hcal
    complete := hcH
    nonnegative := hopH
    noncollapsed := hncH
    normalized := hnorm
    scalar_base_le := hbase
    curvature_bound := hbound
    centers_escape := hd
    scalars_diverge := hQ
    radii_diverge := hL
    distances_diverge := hD
    relative_radius_tends_zero := hsmall
  }
  exact ⟨S, fun η hη => S.exists_roundProductBlowup P hκ (hc b le_rfl)
    (hop b le_rfl) hmono η hη⟩




theorem exists_selected_roundProductBlowup_with_terminal_necks
    (P : M23NormalizedKappaCompactnessPredecessors)
    {b κ : ℝ} (F : RicciFlow 3 M (Iic b)) (hκ : 0 < κ)
    (hc : ∀ t ≤ b, MetricComplete (F.metric t))
    (hop : ∀ t ≤ b, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hmono : ∀ s t, s ≤ t → t ≤ b → ∀ x,
      (F.connection s).scalarCurvature x ≤ (F.connection t).scalarCurvature x)
    (hnc : ∀ t ≤ b, ∀ p : M, ∀ r : ℝ, 0 < r →
      (∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (F.metric t).ball p r,
        |(F.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) →
      ENNReal.ofReal (κ * r ^ 3) ≤ calibratedMetricVolume (F.metric t)
        ((F.metric t).ball p r))
    (p : M) (hunbounded : ¬ BddAbove (range (F.connection b).scalarCurvature))
    {ε : ℝ} (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∃ (S : SelectedAncientRescalings F κ p) (δ : ℝ),
      0 < δ ∧ δ < 1 ∧ ∃ B : RoundProductBlowup S δ,
        ∀ (Φ : RoundCylinderSpace ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), 𝓡 3⟯
            B.convergence.limitCarrier.carrier) (q : UnitTwoSphere),
          Φ (q, 0) = B.convergence.base →
          (fun z v w => (B.convergence.limitFlow.connection 0).scalarCurvature
            B.convergence.base * roundCylinderPullback (B.convergence.limitFlow.metric 0)
              Φ z v w) = EvolvingRoundCylinderMetric 0 →
          ∀ᶠ i in atTop, ∃ N : EpsilonNeck (F.metric b),
            N.epsilon = ε ∧
            N.scale = 1 / Real.sqrt ((F.connection b).scalarCurvature
              (S.center (B.convergence.subsequence i))) ∧
            N.center = S.center (B.convergence.subsequence i) ∧
            N.coordinate_map = (fun z => B.convergence.embedding i (Φ z)) := by
  obtain ⟨S, _⟩ := F.exists_selected_roundProductBlowup P hκ hc hop hmono hnc p hunbounded
  obtain ⟨δ, hδ, hδone, B, hnecks⟩ :=
    S.exists_roundProductBlowup_with_terminal_necks P hκ (hc b le_rfl)
      (hop b le_rfl) hmono hε hεhalf
  exact ⟨S, δ, hδ, hδone, B, hnecks⟩

end PoincareConjecture.RicciFlow
