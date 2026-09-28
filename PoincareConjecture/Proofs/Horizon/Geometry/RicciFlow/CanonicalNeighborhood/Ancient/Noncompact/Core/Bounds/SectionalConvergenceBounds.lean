import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Bounds.SectionalConvergence
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Noncompact.Core.Escaping.Metric








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

private theorem exists_pos_eventually_uniform_lower_bound
    {α X : Type*} [TopologicalSpace X] {l : Filter α}
    {K : Set X} (hK : IsCompact K) (F : α → X → ℝ)
    (hlocal : ∀ x ∈ K, ∃ c > 0, ∀ᶠ z : α × X in l ×ˢ 𝓝 x, c < F z.1 z.2) :
    ∃ c > 0, ∀ᶠ i in l, ∀ x ∈ K, c < F i x := by
  classical
  have hnbhd (x : X) (hx : x ∈ K) :
      ∃ c > 0, ∃ U ∈ 𝓝 x, ∀ᶠ i in l, ∀ y ∈ U, c < F i y := by
    obtain ⟨c, hc, he⟩ := hlocal x hx
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp he
    exact ⟨c, hc, {y | Q y}, hQ, hP.mono fun i hi y hy => hPQ hi hy⟩
  choose c hc U hU hbound using hnbhd
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover' U hU
  by_cases hse : s.Nonempty
  · let d := s.inf' hse (fun x : K => c x x.2)
    have hd : 0 < d := by
      obtain ⟨x, hx, heq⟩ := Finset.exists_mem_eq_inf' hse (fun x : K => c x x.2)
      rw [show d = c x x.2 from heq]
      exact hc x x.2
    refine ⟨d, hd, ?_⟩
    filter_upwards [s.eventually_all.mpr (fun x _ => hbound x x.2)] with i hi x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hx)
    exact (Finset.inf'_le _ hp).trans_lt (hi p hp x hxp)
  · refine ⟨1, zero_lt_one, Eventually.of_forall ?_⟩
    intro i x hx
    obtain ⟨p, hp, _⟩ := mem_iUnion₂.mp (hs hx)
    exact (hse ⟨p, hp⟩).elim

private theorem independent_of_orthonormal_pair
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {u v : V} (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    (huv : inner ℝ u v = 0) : LinearIndependent ℝ ![u, v] := by
  apply linearIndependent_fin2.mpr
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨fun hz => by simp [hz] at hv, ?_⟩
  intro r hr
  have hh := congrArg (fun w => inner ℝ w v) hr
  rw [real_inner_smul_left, hv, huv, mul_one] at hh
  subst r
  simp only [zero_smul] at hr
  simp [← hr] at hu

private theorem isCompact_coordinate_two_frames (n : ℕ) :
    IsCompact {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      inner ℝ z.1 z.1 = 1 ∧ inner ℝ z.2 z.2 = 1 ∧ inner ℝ z.1 z.2 = 0} := by
  have hclosed : IsClosed {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) |
      inner ℝ z.1 z.1 = 1 ∧ inner ℝ z.2 z.2 = 1 ∧ inner ℝ z.1 z.2 = 0} :=
    (isClosed_eq (continuous_fst.inner continuous_fst) continuous_const).inter
      ((isClosed_eq (continuous_snd.inner continuous_snd) continuous_const).inter
        (isClosed_eq (continuous_fst.inner continuous_snd) continuous_const))
  apply ((isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1).prod
    (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).of_isClosed_subset hclosed
  intro z hz
  have hu : ‖z.1‖ ^ 2 = 1 := (real_inner_self_eq_norm_sq z.1).symm.trans hz.1
  have hv : ‖z.2‖ ^ 2 = 1 := (real_inner_self_eq_norm_sq z.2).symm.trans hz.2.1
  simp only [mem_prod, Metric.mem_closedBall, dist_zero_right]
  constructor <;> nlinarith [norm_nonneg z.1, norm_nonneg z.2]

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}



theorem exists_pos_eventually_coordinate_sectional_lower_bound
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (q : G.limit.carrier.carrier) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ (extChartAt (𝓡 3) q).target)
    (hpos : ∀ u v : TangentSpace (𝓡 3) ((extChartAt (𝓡 3) q).symm p),
      LinearIndependent ℝ ![u, v] →
      0 < (G.limit.flow.flow.connection 0).sectionalCurvature
        ((extChartAt (𝓡 3) q).symm p) u v) :
    ∃ c > 0, ∀ᶠ z : ℕ × EuclideanSpace ℝ (Fin 3) in atTop ×ˢ 𝓝 p,
      ∀ u v : EuclideanSpace ℝ (Fin 3), LinearIndependent ℝ ![u, v] →
      let φ := fun y => ((e z.1).toFun (0, (extChartAt (𝓡 3) q).symm y)).2
      c < ((S.term (G.subsequence z.1)).flow.flow.connection 0).sectionalCurvature
        (φ z.2) (mfderiv (𝓡 3) (𝓡 3) φ z.2 u) (mfderiv (𝓡 3) (𝓡 3) φ z.2 v) := by
  let V := EuclideanSpace ℝ (Fin 3)
  let K : Set (V × V) := {z | inner ℝ z.1 z.1 = 1 ∧
    inner ℝ z.2 z.2 = 1 ∧ inner ℝ z.1 z.2 = 0}
  let φ := fun (i : ℕ) y => ((e i).toFun (0, (extChartAt (𝓡 3) q).symm y)).2
  let F := fun (z : ℕ × V) (w : V × V) =>
    ((S.term (G.subsequence z.1)).flow.flow.connection 0).sectionalCurvature
      (φ z.1 z.2) (mfderiv (𝓡 3) (𝓡 3) (φ z.1) z.2 w.1)
        (mfderiv (𝓡 3) (𝓡 3) (φ z.1) z.2 w.2)
  have hloc (w : V × V) (hw : w ∈ K) :
      ∃ c > 0, ∀ᶠ z : (ℕ × V) × (V × V) in
        (atTop ×ˢ 𝓝 p) ×ˢ 𝓝 w, c < F z.1 z.2 := by
    have hwlin := independent_of_orthonormal_pair hw.1 hw.2.1 hw.2.2
    let dc := mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p
    have hdc : dc.IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hp
    have himage : LinearIndependent ℝ ![dc w.1, dc w.2] := by
      convert! hwlin.map' dc.toLinearMap (LinearMap.ker_eq_bot.mpr hdc.injective) using 1
      ext i
      fin_cases i <;> rfl
    have hlimpos := hpos _ _ himage
    have ht := hconv.tendsto_terminal_coordinate_sectionalCurvature hfixed
      (tendsto_fst.comp tendsto_fst) (tendsto_snd.comp tendsto_fst)
      ((continuous_fst.tendsto w).comp tendsto_snd)
      ((continuous_snd.tendsto w).comp tendsto_snd) hwlin q hp
    refine ⟨_, half_pos hlimpos, ?_⟩
    exact ht.eventually (Ioi_mem_nhds (half_lt_self hlimpos))
  obtain ⟨c, hc, he⟩ := exists_pos_eventually_uniform_lower_bound
    (isCompact_coordinate_two_frames 3) F hloc
  refine ⟨c, hc, he.mono ?_⟩
  intro z hz u v huv
  obtain ⟨a, b, c', d, hdet, ha, hb, hab⟩ :=
    LeviCivitaData.exists_orthonormal_changeBasis u v huv
  have hbnd := hz (a • u + b • v, c' • u + d • v) ⟨ha, hb, hab⟩
  dsimp only [F] at hbnd
  simp only [map_add, map_smul] at hbnd
  rw [LeviCivitaData.sectionalCurvature_changeBasis _ _ _ _ _ _ _ _ hdet] at hbnd
  exact hbnd



theorem exists_pos_eventually_terminal_sectional_lower_bound_at
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    (p : G.limit.carrier.carrier)
    (hpos : ∀ u v : TangentSpace (𝓡 3) p, LinearIndependent ℝ ![u, v] →
      0 < (G.limit.flow.flow.connection 0).sectionalCurvature p u v) :
    ∃ c > 0, ∀ᶠ z : ℕ × G.limit.carrier.carrier in atTop ×ˢ 𝓝 p,
      ∀ u v : TangentSpace (𝓡 3) ((e z.1).toFun (0, z.2)).2,
        LinearIndependent ℝ ![u, v] →
        c < ((S.term (G.subsequence z.1)).flow.flow.connection 0).sectionalCurvature
          ((e z.1).toFun (0, z.2)).2 u v := by
  let c := extChartAt (𝓡 3) p
  have hp : p ∈ c.source := mem_extChartAt_source p
  have hcp : c.symm (c p) = p := c.left_inv hp
  have hpos' : ∀ u v : TangentSpace (𝓡 3) (c.symm (c p)),
      LinearIndependent ℝ ![u, v] →
      0 < (G.limit.flow.flow.connection 0).sectionalCurvature (c.symm (c p)) u v := by
    rw [hcp]
    exact hpos
  obtain ⟨a, ha, he⟩ := hconv.exists_pos_eventually_coordinate_sectional_lower_bound
    hfixed p (c.map_source hp) hpos'
  have he' : ∀ᶠ z : ℕ × EuclideanSpace ℝ (Fin 3) in atTop ×ˢ 𝓝 (c p),
      ∀ u v : TangentSpace (𝓡 3) ((e z.1).toFun (0, c.symm z.2)).2,
        LinearIndependent ℝ ![u, v] →
        a < ((S.term (G.subsequence z.1)).flow.flow.connection 0).sectionalCurvature
          ((e z.1).toFun (0, c.symm z.2)).2 u v := by
    filter_upwards [he, eventually_terminal_chart_domain (G := G) p (c.map_source hp)]
      with z hz hdom
    let φ := fun y => ((e z.1).toFun (0, c.symm y)).2
    let L := mfderiv (𝓡 3) (𝓡 3) φ z.2
    have hL := ((e z.1).terminal_chart_map_regular (G.exhaustion_open z.1) p
      hdom.1 hdom.2).2
    let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (φ z.2)) :=
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.finiteDimensional_of_finite
    have hsurj : Function.Surjective L :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        (show Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) =
          Module.finrank ℝ (TangentSpace (𝓡 3) (φ z.2)) from rfl)).mp hL
    intro u v huv
    obtain ⟨u', hu⟩ := hsurj u
    obtain ⟨v', hv⟩ := hsurj v
    have huv' : LinearIndependent ℝ ![u', v'] := by
      apply LinearIndependent.of_comp L.toLinearMap
      convert! huv using 1
      ext i
      fin_cases i
      · exact hu
      · exact hv
    have hbnd := hz u' v' huv'
    change a < ((S.term (G.subsequence z.1)).flow.flow.connection 0).sectionalCurvature
      (φ z.2) (L u') (L v') at hbnd
    rw [hu, hv] at hbnd
    exact hbnd
  have hmap := (tendsto_id.prodMap (continuousAt_extChartAt p).tendsto).eventually he'
  refine ⟨a, ha, ?_⟩
  filter_upwards [hmap, tendsto_snd.eventually (extChartAt_source_mem_nhds (I := 𝓡 3) p)]
    with z hz hzs
  change (∀ u v : TangentSpace (𝓡 3) ((e z.1).toFun (0, c.symm (c z.2))).2,
    LinearIndependent ℝ ![u, v] →
    a < ((S.term (G.subsequence z.1)).flow.flow.connection 0).sectionalCurvature
      ((e z.1).toFun (0, c.symm (c z.2))).2 u v) at hz
  rw [c.left_inv hzs] at hz
  exact hz





theorem exists_pos_eventually_terminal_sectional_lower_bound_on_compact
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    {A : Set G.limit.carrier.carrier} (hA : IsCompact A)
    (hpos : ∀ x ∈ A, ∀ u v : TangentSpace (𝓡 3) x,
      (G.limit.flow.flow.metric 0).inner x u u = 1 →
      (G.limit.flow.flow.metric 0).inner x v v = 1 →
      (G.limit.flow.flow.metric 0).inner x u v = 0 →
      0 < (G.limit.flow.flow.connection 0).sectionalCurvature x u v) :
    ∃ c > 0, ∀ᶠ k in atTop, ∀ x ∈ A,
      ∀ u v : TangentSpace (𝓡 3) ((e k).toFun (0, x)).2,
        LinearIndependent ℝ ![u, v] →
        c < ((S.term (G.subsequence k)).flow.flow.connection 0).sectionalCurvature
          ((e k).toFun (0, x)).2 u v := by
  classical
  have hlocal (x : G.limit.carrier.carrier) (hx : x ∈ A) :
      ∃ c > 0, ∃ U ∈ 𝓝 x, ∀ᶠ k in atTop, ∀ y ∈ U,
      ∀ u v : TangentSpace (𝓡 3) ((e k).toFun (0, y)).2,
        LinearIndependent ℝ ![u, v] →
        c < ((S.term (G.subsequence k)).flow.flow.connection 0).sectionalCurvature
          ((e k).toFun (0, y)).2 u v := by
    obtain ⟨c, hc, he⟩ := hconv.exists_pos_eventually_terminal_sectional_lower_bound_at
      hfixed x (fun u v huv =>
        (G.limit.flow.flow.connection 0).sectionalCurvature_pos_of_independent x (hpos x hx) huv)
    obtain ⟨P, hP, Q, hQ, hPQ⟩ := eventually_prod_iff.mp he
    exact ⟨c, hc, {y | Q y}, hQ, hP.mono fun k hk y hy => hPQ hk hy⟩
  choose c hc U hU hbound using hlocal
  obtain ⟨s, hs⟩ := hA.elim_nhds_subcover' U hU
  by_cases hse : s.Nonempty
  · let d := s.inf' hse (fun x : A => c x x.2)
    have hd : 0 < d := by
      obtain ⟨x, _, heq⟩ := Finset.exists_mem_eq_inf' hse (fun x : A => c x x.2)
      rw [show d = c x x.2 from heq]
      exact hc x x.2
    refine ⟨d, hd, ?_⟩
    filter_upwards [s.eventually_all.mpr (fun x _ => hbound x x.2)] with k hk x hx
    obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp (hs hx)
    intro u v huv
    exact (Finset.inf'_le _ hp).trans_lt (hk p hp x hxp u v huv)
  · refine ⟨1, zero_lt_one, Eventually.of_forall ?_⟩
    intro k x hx
    obtain ⟨p, hp, _⟩ := mem_iUnion₂.mp (hs hx)
    exact (hse ⟨p, hp⟩).elim

end M23TerminalMetricConvergence




theorem M23TerminalExtension.exists_pos_eventually_source_ball_sectional_lower_bound
    {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
    {G : M23InteriorConvergence S} (hterminal : M23TerminalExtension G)
    (hpos : (G.limit.flow.flow.connection 0).StrictlyPositiveSectionalCurvature)
    {D : ℝ} (hD : 0 < D) :
    ∃ c > 0, ∀ᶠ k in atTop,
      ∀ x ∈ ((S.term (G.subsequence k)).flow.flow.metric 0).ball
        (S.term (G.subsequence k)).base D,
      ∀ u v : TangentSpace (𝓡 3) x, LinearIndependent ℝ ![u, v] →
        c < ((S.term (G.subsequence k)).flow.flow.connection 0).sectionalCurvature x u v := by
  obtain ⟨e, hcompat, hfixed, hconv⟩ := hterminal.terminal_embedding
  have hcompact := (G.limit.flow.flow.metric 0).isCompact_closure_ball_of_metricComplete
    (G.limit.flow.complete 0 le_rfl) G.limit.base (2 * D)
  obtain ⟨c, hc, hbound⟩ :=
    hconv.exists_pos_eventually_terminal_sectional_lower_bound_on_compact
      (fun k t ht x hx => hfixed k t 0 x ht le_rfl hx) hcompact (fun x _ => hpos x)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hbound, hconv.eventually_source_ball_subset_terminal_image
    (fun k => (hcompat k).2) hD (by norm_num : (1 : ℝ) < 2)] with k hk hcover
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hcover hx
  exact hk y (subset_closure hy)

end PoincareConjecture
