import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

omit [MeasurableSpace M] [BorelSpace M] [T2Space M] [SecondCountableTopology M] in
private theorem metric_ball_neighborhood (g : RiemannianMetric 3 M)
    {x : M} {U : Set M} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ g.ball x r ⊆ U ∧
      IsOpen (g.ball x (r / 2)) ∧ x ∈ g.ball x (r / 2) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := .ofRiemannianMetric (𝓡 3) M
  obtain ⟨e, he, heU⟩ := EMetric.mem_nhds_iff.mp (hU.mem_nhds hx)
  obtain ⟨r, hr, hre⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp he
  have hr' : 0 < (r : ℝ) := by exact_mod_cast hr
  refine ⟨r, hr', ?_, ?_, ?_⟩
  · intro y hy
    apply heU
    change g.edist y x < e
    change g.edist x y < ENNReal.ofReal (r : ℝ) at hy
    rw [show g.edist y x = g.edist x y from Manifold.riemannianEDist_comm]
    exact hy.trans (by simpa only [ENNReal.ofReal_coe_nnreal] using hre)
  · exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  · change g.edist x x < ENNReal.ofReal ((r : ℝ) / 2)
    rw [show g.edist x x = 0 from Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (half_pos hr')

theorem exists_open_uniform_curvature_derivative_tail
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {x : M} (hx : x ∈ H.reference.regularLimitSet) :
    ∃ (s : ℝ) (U : Set M), H.reference.tMinus < s ∧ s < T ∧
      IsOpen U ∧ x ∈ U ∧ U ⊆ H.reference.regularLimitSet ∧
        ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico s T, ∀ y ∈ U,
          (H.reference.flow.connection t).curvatureDerivativeNorm k y ≤ C := by
  let : CompactSpace M := H.compact_reference
  obtain ⟨a, K, V, ha, haT, hK, hV, hxV, hVreg, hRm⟩ :=
    H.exists_open_uniform_curvature_tail P04 hx
  obtain ⟨r, hr, hrV, hball, hxball⟩ :=
    metric_ball_neighborhood (H.reference.flow.metric a) hV hxV
  let s := (a + T) / 2
  have has : a < s := by dsimp [s]; linarith
  have hsT : s < T := by dsimp [s]; linarith
  have hhalf : (H.reference.flow.metric a).ball x (r / 2) ⊆
      (H.reference.flow.metric a).ball x r := by
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal (by linarith : r / 2 ≤ r))
  refine ⟨s, (H.reference.flow.metric a).ball x (r / 2), ha.trans has, hsT,
    hball, hxball, fun y hy => hVreg (hrV (hhalf hy)), ?_⟩
  intro k
  obtain ⟨C, hC, hShi⟩ := P04.local_derivative_estimates 3 k K (K * (T - a)) r
    hK (mul_pos hK (sub_pos.mpr haT)) hr
  refine ⟨C / (s - a) ^ ((k : ℝ) / 2), by positivity, ?_⟩
  intro t ht y hy
  have hat : a < t := has.trans_le ht.1
  have hdom : (fun z : ℝ => z + a) '' Icc 0 (t - a) ⊆ Ico H.reference.tMinus T := by
    rintro _ ⟨z, hz, rfl⟩
    constructor <;> linarith [hz.1, hz.2, ht.2]
  have hpos : 0 < t - a := sub_pos.mpr hat
  let G := H.reference.flow.translate a hdom ordConnected_Icc
    ⟨0, ⟨le_rfl, hpos.le⟩, t - a, ⟨hpos.le, le_rfl⟩, hpos.ne⟩
  have htime : t - a ≤ K * (T - a) / K := by
    rw [mul_div_cancel_left₀ _ hK.ne']
    linarith [ht.2]
  have hcompact : IsCompact (closure ((G.metric 0).ball x r)) := isClosed_closure.isCompact
  have hbound : ∀ z ∈ Icc 0 (t - a), ∀ w ∈ (G.metric 0).ball x r,
      (G.connection z).curvatureTensorNorm w ≤ K := by
    intro z hz w hw
    change (H.reference.flow.connection (z + a)).curvatureTensorNorm w ≤ K
    apply hRm (z + a) ⟨by linarith [hz.1], by linarith [hz.2, ht.2]⟩ w
    apply hrV
    simpa only [G, RicciFlow.translate, zero_add] using hw
  have hyG : y ∈ (G.metric 0).ball x (r / 2) := by
    simpa only [G, RicciFlow.translate, zero_add] using hy
  have hder := hShi M (t - a) (sub_pos.mpr hat) htime G x hcompact hbound
    (t - a) ⟨sub_pos.mpr hat, le_rfl⟩ y hyG
  have hder' : (H.reference.flow.connection t).curvatureDerivativeNorm k y ≤
      C / (t - a) ^ ((k : ℝ) / 2) := by
    change (H.reference.flow.connection (t - a + a)).curvatureDerivativeNorm k y ≤ _ at hder
    rw [sub_add_cancel] at hder
    exact hder
  exact hder'.trans (div_le_div_of_nonneg_left hC.le (by positivity)
    (Real.rpow_le_rpow (sub_nonneg.mpr has.le) (by linarith [ht.1]) (by positivity)))

theorem exists_uniform_curvature_derivative_tail_on_compact
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set M} (hA : IsCompact A) (hreg : A ⊆ H.reference.regularLimitSet) :
    ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico s T, ∀ y ∈ A,
        (H.reference.flow.connection t).curvatureDerivativeNorm k y ≤ C := by
  apply hA.induction_on
    (p := fun B => ∃ s : ℝ, H.reference.tMinus < s ∧ s < T ∧
      ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Ico s T, ∀ y ∈ B,
        (H.reference.flow.connection t).curvatureDerivativeNorm k y ≤ C)
  · obtain ⟨s, hs, hsT⟩ := exists_between H.reference.tMinus_lt
    exact ⟨s, hs, hsT, fun _ => ⟨1, zero_lt_one, fun _ _ _ hy => False.elim hy⟩⟩
  · rintro B D hBD ⟨s, hs, hsT, hb⟩
    refine ⟨s, hs, hsT, fun k => ?_⟩
    obtain ⟨C, hC, hbound⟩ := hb k
    exact ⟨C, hC, fun t ht y hy => hbound t ht y (hBD hy)⟩
  · rintro B D ⟨s, hs, hsT, hb⟩ ⟨a, ha, haT, hd⟩
    refine ⟨max s a, hs.trans_le (le_max_left _ _), max_lt hsT haT, fun k => ?_⟩
    obtain ⟨C, hC, hCbound⟩ := hb k
    obtain ⟨E, hE, hEbound⟩ := hd k
    refine ⟨max C E, hC.trans_le (le_max_left _ _), ?_⟩
    intro t ht y hy
    rcases hy with hy | hy
    · exact (hCbound t ⟨(le_max_left _ _).trans ht.1, ht.2⟩ y hy).trans
        (le_max_left _ _)
    · exact (hEbound t ⟨(le_max_right _ _).trans ht.1, ht.2⟩ y hy).trans
        (le_max_right _ _)
  · intro x hx
    obtain ⟨s, U, hs, hsT, hU, hxU, _, hb⟩ :=
      H.exists_open_uniform_curvature_derivative_tail P04 (hreg hx)
    exact ⟨U, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hxU), s, hs, hsT, hb⟩

end PoincareConjecture.SingularTimeAssumptions
