import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Connected
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Services
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Positive.Regions.Selection












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.NoncompactKappa.Positive

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]



structure SoulNeckRegion (K : AncientKappaSolution 3 M)
    (S : RiemannianMetric.PointSoulData (K.flow.metric 0)) (epsilon D R : ℝ) where
  neck : StrongEvolvingNeck K 0 epsilon
  inside : Set M
  outside : Set M
  inside_open : IsOpen inside
  outside_open : IsOpen outside
  inside_connected : IsConnected inside
  outside_connected : IsConnected outside
  disjoint : Disjoint inside outside
  complement_sphere : inside ∪ outside = neck.terminal_neck.central_sphereᶜ
  inside_frontier : frontier inside = neck.terminal_neck.central_sphere
  outside_frontier : frontier outside = neck.terminal_neck.central_sphere
  sides : (neck.terminal_neck.region (-epsilon⁻¹) 0 ⊆ inside ∧
      neck.terminal_neck.region 0 epsilon⁻¹ ⊆ outside) ∨
    (neck.terminal_neck.region (-epsilon⁻¹) 0 ⊆ outside ∧
      neck.terminal_neck.region 0 epsilon⁻¹ ⊆ inside)
  compact_side : IsCompact (closure inside)
  center_radius : ((K.flow.metric 0).edist S.center neck.center).toReal =
    R * soulScalar K S.center ^ (-1 / 2 : ℝ)
  neck_scale_bound : (8 * Real.pi + 4 * epsilon⁻¹ + 4) * neck.terminal_neck.scale <
    R * soulScalar K S.center ^ (-1 / 2 : ℝ)
  inner_ball_subset : (K.flow.metric 0).ball S.center
    (D * soulScalar K S.center ^ (-1 / 2 : ℝ)) ⊆ inside \ neck.terminal_neck.carrier
  carrier_subset_ball : inside ∪ neck.terminal_neck.carrier ⊆
    (K.flow.metric 0).ball S.center ((2 * R) * soulScalar K S.center ^ (-1 / 2 : ℝ))
  strong_outside_core : ∀ x : M, x ∉ interior (inside \ neck.terminal_neck.carrier) →
    ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x



theorem exists_soulNeckRegion_of_services
    (P : NoncompactKappaServices.{u}) {epsilon D : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ neckSeparationThreshold) (hD : 1 < D) :
    ∃ R : ℝ, 4 * D ≤ R ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        [NoncompactSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {D₁ : ℝ}, SoulCenteredCoreEstimate K S epsilon D D₁ →
        Nonempty (SoulNeckRegion K S epsilon D R) := by
  obtain ⟨R, hDR, hneck⟩ := exists_enclosing_strong_neck_radius_of_services P hD
    (show 0 ≤ 8 * Real.pi + 4 * epsilon⁻¹ + 4 by positivity)
  refine ⟨R, hDR, ?_⟩
  intro M _ _ _ _ _ _ _ _ _ _ K S D₁ H
  obtain ⟨N, hcenter, hscale⟩ := hneck K S H
  have hneckscale := N.terminal_neck.scale_pos
  obtain ⟨A, B, hA, hB, hAc, hBc, hd, hu, hfA, hfB, hc, hp, hi, ho, hsides⟩ :=
    exists_quantitative_neck_regions S (K.complete 0 le_rfl) N.terminal_neck
      (N.terminal_epsilon.trans_le hsmall)
  have hpos : 0 < soulScalar K S.center ^ (-1 / 2 : ℝ) :=
    Real.rpow_pos_of_pos H.soul_scalar_pos _
  have hRpos : 0 < R := by linarith
  have hRscale := mul_pos hRpos hpos
  have hDscale : 4 * D * soulScalar K S.center ^ (-1 / 2 : ℝ) ≤
      R * soulScalar K S.center ^ (-1 / 2 : ℝ) :=
    mul_le_mul_of_nonneg_right hDR hpos.le
  have hcenter' : ((K.flow.metric 0).edist S.center N.terminal_neck.center).toReal =
      R * soulScalar K S.center ^ (-1 / 2 : ℝ) := N.terminal_center ▸ hcenter
  have hdiam : (2 * Real.pi + 2 * epsilon⁻¹) * N.terminal_neck.scale <
      R * soulScalar K S.center ^ (-1 / 2 : ℝ) / 2 := by
    nlinarith [N.terminal_neck.scale_pos, Real.pi_pos,
      mul_pos Real.pi_pos N.terminal_neck.scale_pos]
  have hdist (x : M) (hx : x ∈ N.terminal_neck.carrier) :
      ((K.flow.metric 0).edist N.terminal_neck.center x).toReal <
        R * soulScalar K S.center ^ (-1 / 2 : ℝ) / 2 := by
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (N.terminal_neck.edist_center_le_of_mem_carrier hx)
    rw [N.terminal_epsilon, ENNReal.toReal_ofReal (by positivity)] at hb
    exact hb.trans_lt hdiam
  have havoid : Disjoint ((K.flow.metric 0).ball S.center
      (D * soulScalar K S.center ^ (-1 / 2 : ℝ))) N.terminal_neck.carrier := by
    apply Set.disjoint_left.mpr
    intro x hx hn
    have hx' := (ENNReal.lt_ofReal_iff_toReal_lt
      ((K.flow.metric 0).edist_ne_top S.center x)).mp hx
    have hreverse := abs_le.mp
      ((K.flow.metric 0).abs_toReal_edist_sub_le S.center N.terminal_neck.center x)
    rw [hcenter'] at hreverse
    have hdistance := hdist x hn
    nlinarith
  have hinner : (K.flow.metric 0).ball S.center
      (D * soulScalar K S.center ^ (-1 / 2 : ℝ)) ⊆ A := by
    intro x hx
    refine hi _ (mul_pos (by linarith : 0 < D) hpos) ?_ ?_
    · rw [hcenter']
      have hpi : (2 * Real.pi) * N.terminal_neck.scale ≤
          (2 * Real.pi + 2 * epsilon⁻¹) * N.terminal_neck.scale := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
          hneckscale.le
      nlinarith
    · exact (ENNReal.lt_ofReal_iff_toReal_lt
        ((K.flow.metric 0).edist_ne_top S.center x)).mp hx
  have hcoreball : (K.flow.metric 0).ball S.center
      (D * soulScalar K S.center ^ (-1 / 2 : ℝ)) ⊆ interior (A \ N.terminal_neck.carrier) := by
    have hopen : IsOpen ((K.flow.metric 0).ball S.center
        (D * soulScalar K S.center ^ (-1 / 2 : ℝ))) := by
      let := (K.flow.metric 0).toMetricSpace
      rw [← (K.flow.metric 0).toMetricSpace_ball]
      exact Metric.isOpen_ball
    exact hopen.subset_interior_iff.mpr
      (fun _ hx => ⟨hinner hx, Set.disjoint_left.mp havoid hx⟩)
  refine ⟨{
    neck := N
    inside := A
    outside := B
    inside_open := hA
    outside_open := hB
    inside_connected := hAc
    outside_connected := hBc
    disjoint := hd
    complement_sphere := hu
    inside_frontier := hfA
    outside_frontier := hfB
    sides := by simpa only [N.terminal_epsilon] using hsides
    compact_side := hc
    center_radius := hcenter
    neck_scale_bound := hscale
    inner_ball_subset := fun _ hx => ⟨hinner hx, Set.disjoint_left.mp havoid hx⟩
    carrier_subset_ball := ?_
    strong_outside_core := fun x hx => H.strong_outside x (fun hb => hx (hcoreball hb)) }⟩
  · intro x hx
    apply (ENNReal.lt_ofReal_iff_toReal_lt
      ((K.flow.metric 0).edist_ne_top S.center x)).mpr
    rcases hx with hx | hx
    · have hb := ho (subset_closure hx)
      change ((K.flow.metric 0).edist S.center x).toReal ≤ _ at hb
      rw [hcenter'] at hb
      have hpi : (2 * Real.pi) * N.terminal_neck.scale ≤
          (2 * Real.pi + 2 * epsilon⁻¹) * N.terminal_neck.scale := by
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
          hneckscale.le
      nlinarith
    · have hb := (K.flow.metric 0).toReal_edist_triangle S.center N.terminal_neck.center x
      rw [hcenter'] at hb
      have := hdist x hx
      nlinarith



theorem exists_soulNeckRegion
    (P : M26CanonicalNeighborhoodPredecessors.{u}) {epsilon D : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ neckSeparationThreshold) (hD : 1 < D) :
    ∃ R : ℝ, 4 * D ≤ R ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
        [NoncompactSpace M]
        (K : AncientKappaSolution 3 M) (S : RiemannianMetric.PointSoulData (K.flow.metric 0))
        {D₁ : ℝ}, SoulCenteredCoreEstimate K S epsilon D D₁ →
        Nonempty (SoulNeckRegion K S epsilon D R) := by
  exact exists_soulNeckRegion_of_services P.noncompactServices hepsilon hsmall hD

namespace SoulNeckRegion

variable {K : AncientKappaSolution 3 M}
  {S : RiemannianMetric.PointSoulData (K.flow.metric 0)} {epsilon D R : ℝ}
  (G : SoulNeckRegion K S epsilon D R)

theorem strong_on_end (x : M) (hx : x ∈ G.outside ∪ G.neck.terminal_neck.carrier) :
    ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x := by
  apply G.strong_outside_core x
  intro hcore
  have hc := interior_subset hcore
  rcases hx with hx | hx
  · exact Set.disjoint_left.mp G.disjoint hc.1 hx
  · exact hc.2 hx

theorem core_or_strong (x : M) : x ∈ interior (G.inside \ G.neck.terminal_neck.carrier) ∨
    ∃ N : StrongEvolvingNeck K 0 epsilon, N.center = x := by
  classical
  by_cases hx : x ∈ interior (G.inside \ G.neck.terminal_neck.carrier)
  · exact Or.inl hx
  · exact Or.inr (G.strong_outside_core x hx)

theorem inner_ball_subset_interior_core : (K.flow.metric 0).ball S.center
    (D * soulScalar K S.center ^ (-1 / 2 : ℝ)) ⊆
      interior (G.inside \ G.neck.terminal_neck.carrier) := by
  have hopen : IsOpen ((K.flow.metric 0).ball S.center
      (D * soulScalar K S.center ^ (-1 / 2 : ℝ))) := by
    let := (K.flow.metric 0).toMetricSpace
    rw [← (K.flow.metric 0).toMetricSpace_ball]
    exact Metric.isOpen_ball
  exact hopen.subset_interior_iff.mpr G.inner_ball_subset

theorem center_mem_interior_core (hD : 0 < D) (hscalar : 0 < soulScalar K S.center) :
    S.center ∈ interior (G.inside \ G.neck.terminal_neck.carrier) := by
  apply G.inner_ball_subset_interior_core
  change (K.flow.metric 0).edist S.center S.center < _
  simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
  exact ENNReal.ofReal_pos.mpr (mul_pos hD (Real.rpow_pos_of_pos hscalar _))

theorem compact_core : IsCompact (G.inside \ G.neck.terminal_neck.carrier) := by
  have heq : G.inside \ G.neck.terminal_neck.carrier =
      closure G.inside \ G.neck.terminal_neck.carrier := by
    apply subset_antisymm (sdiff_subset_sdiff_left subset_closure)
    intro x hx
    refine ⟨?_, hx.2⟩
    by_contra hn
    apply hx.2
    apply G.neck.terminal_neck.central_sphere_subset
    rw [← G.inside_frontier]
    exact ⟨hx.1, fun hi => hn (interior_subset hi)⟩
  rw [heq]
  exact G.compact_side.diff G.neck.terminal_neck.carrier_open

theorem compact_carrier_closure :
    IsCompact (closure (G.inside ∪ G.neck.terminal_neck.carrier)) :=
  ((K.flow.metric 0).isCompact_closure_ball_of_metricComplete (K.complete 0 le_rfl)
    S.center ((2 * R) * soulScalar K S.center ^ (-1 / 2 : ℝ))).of_isClosed_subset
      isClosed_closure (closure_mono G.carrier_subset_ball)

theorem connected_carrier : IsConnected (G.inside ∪ G.neck.terminal_neck.carrier) := by
  have hx : G.neck.terminal_neck.center ∈ closure G.inside :=
    frontier_subset_closure (G.inside_frontier ▸ G.neck.terminal_neck.center_on_central_sphere)
  obtain ⟨x, hxN, hxA⟩ := mem_closure_iff.mp hx G.neck.terminal_neck.carrier
    G.neck.terminal_neck.carrier_open
    (G.neck.terminal_neck.central_sphere_subset G.neck.terminal_neck.center_on_central_sphere)
  exact G.inside_connected.union ⟨x, hxA, hxN⟩ G.neck.terminal_neck.isConnected_carrier

theorem connected_end : IsConnected (G.outside ∪ G.neck.terminal_neck.carrier) := by
  have hx : G.neck.terminal_neck.center ∈ closure G.outside :=
    frontier_subset_closure (G.outside_frontier ▸ G.neck.terminal_neck.center_on_central_sphere)
  obtain ⟨x, hxN, hxB⟩ := mem_closure_iff.mp hx G.neck.terminal_neck.carrier
    G.neck.terminal_neck.carrier_open
    (G.neck.terminal_neck.central_sphere_subset G.neck.terminal_neck.center_on_central_sphere)
  exact G.outside_connected.union ⟨x, hxB, hxN⟩ G.neck.terminal_neck.isConnected_carrier

theorem cover : (G.inside ∪ G.neck.terminal_neck.carrier) ∪
    (G.outside ∪ G.neck.terminal_neck.carrier) = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hs : x ∈ G.neck.terminal_neck.central_sphere
  · exact Or.inl (Or.inr (G.neck.terminal_neck.central_sphere_subset hs))
  · have hx : x ∈ G.inside ∪ G.outside := G.complement_sphere ▸ hs
    rcases hx with hx | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr (Or.inl hx)

theorem overlap : (G.inside ∪ G.neck.terminal_neck.carrier) ∩
    (G.outside ∪ G.neck.terminal_neck.carrier) = G.neck.terminal_neck.carrier := by
  ext x
  constructor
  · rintro ⟨ha | hn, hb | hn⟩
    · exact (Set.disjoint_left.mp G.disjoint ha hb).elim
    all_goals exact hn
  · exact fun hx => ⟨Or.inr hx, Or.inr hx⟩

end SoulNeckRegion

end PoincareConjecture.NoncompactKappa.Positive
