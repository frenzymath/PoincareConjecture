import PoincareConjecture.Proofs.M09.RiemannianProper
import PoincareConjecture.Proofs.M09.TimeTranslatedFlow
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import PoincareConjecture.Definitions.Ch06.LGeometry

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem exists_uniform_curvatureDerivative_bound {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T τmax : ℝ) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (k : ℕ) (b : ℝ) (_hb : 0 ≤ b) (hbmax : b < τmax) :
    ∃ C : ℝ, 0 < C ∧ ∀ τ ∈ Set.Icc 0 b, ∀ x : M,
      (F.connection (T - τ)).curvatureDerivativeNorm k x ≤ C := by
  obtain ⟨K, _hK, hbound⟩ := hcurvature.2
  let K0 : ℝ := max K 1
  have hK0 : 0 < K0 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let a : ℝ := T - τmax
  let α : ℝ := τmax * K0
  have hα : 0 < α := mul_pos hτmax hK0
  have htime_mem : ∀ t ∈ Set.Icc 0 τmax, a + t ∈ Set.Icc (T - τmax) T := by
    intro t ht
    dsimp [a]
    constructor <;> linarith [ht.1, ht.2]
  have htime : ∀ t ∈ Set.Icc 0 τmax, a + t ∈ J :=
    fun t ht ↦ hwindow (htime_mem t ht)
  let G := timeTranslatedFlow F a τmax hτmax htime
  have hcomplete : MetricComplete (G.metric 0) :=
    hcurvature.1 (a + 0) (htime_mem 0 ⟨le_rfl, hτmax.le⟩)
  have hGbound : ∀ t ∈ Set.Icc 0 τmax, ∀ x : M,
      (G.connection t).curvatureTensorNorm x ≤ K0 := by
    intro t ht x
    exact ((le_abs_self _).trans (hbound (a + t) (htime_mem t ht) x)).trans (le_max_left _ _)
  have htime_length : τmax ≤ α / K0 := by
    dsimp [α]
    rw [mul_div_cancel_right₀ _ hK0.ne']
  obtain ⟨C0, hC0, hestimate⟩ :=
    hM04.local_derivative_estimates n k K0 α 2 hK0 hα (by norm_num)
  let δ : ℝ := τmax - b
  have hδ : 0 < δ := sub_pos.mpr hbmax
  have hpower : 0 < δ ^ ((k : ℝ) / 2) := Real.rpow_pos_of_pos hδ _
  refine ⟨C0 / δ ^ ((k : ℝ) / 2), div_pos hC0 hpower, ?_⟩
  intro τ hτ x
  have hx : x ∈ (G.metric 0).ball x (2 / 2) := by
    letI : MetricSpace M := selectedMetricSpace (G.metric 0)
    change edist x x < ENNReal.ofReal (2 / 2)
    norm_num
  have ht : τmax - τ ∈ Set.Ioc 0 τmax := ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
  have he := hestimate M τmax hτmax htime_length G x
    (isCompact_closure_metric_ball (G.metric 0) hcomplete x 2)
    (fun t ht y _hy ↦ hGbound t ht y) (τmax - τ) ht x hx
  have htranslate : a + (τmax - τ) = T - τ := by dsimp [a]; ring
  change (F.connection (a + (τmax - τ))).curvatureDerivativeNorm k x ≤
    C0 / (τmax - τ) ^ ((k : ℝ) / 2) at he
  rw [htranslate] at he
  apply he.trans
  apply div_le_div_of_nonneg_left hC0.le hpower
  apply Real.rpow_le_rpow hδ.le
  · dsimp [δ]
    linarith [hτ.2]
  · positivity

end PoincareConjecture.Proofs.M09
