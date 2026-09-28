import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Positivity
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Control
import Mathlib.Topology.Order.LiminfLimsup

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

namespace Poincare.AncientVolume

theorem exists_finite_ratio_sequence
    {X : Type*} [MetricSpace X] [ProperSpace X] [NoncompactSpace X]
    (p : X) (R : X → ℝ) (hR : ∀ x, 0 ≤ R x)
    (hfinite : ¬ ∀ L A : ℝ, ∃ x : X, L < dist p x ∧ A < R x * dist p x ^ 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ q : ℕ → X,
      Tendsto (fun i => dist p (q i)) atTop atTop ∧
      Tendsto (fun i => R (q i) * dist p (q i) ^ 2) atTop (𝓝 A) ∧
      ∀ C : ℝ, A < C → ∃ L : ℝ, 0 < L ∧
        ∀ x : X, L ≤ dist p x → R x * dist p x ^ 2 ≤ C := by
  classical
  let f := fun x => R x * dist p x ^ 2
  have hnonneg : ∀ᶠ x in cocompact X, 0 ≤ f x :=
    Eventually.of_forall (fun x => mul_nonneg (hR x) (sq_nonneg _))
  have hlower := isBoundedUnder_of_eventually_ge hnonneg
  have hupper : (cocompact X).IsBoundedUnder (· ≤ ·) f := by
    push Not at hfinite
    obtain ⟨L, C, hC⟩ := hfinite
    apply isBoundedUnder_of_eventually_le (a := C)
    filter_upwards [(tendsto_dist_left_cocompact_atTop p).eventually_gt_atTop L] with x hx
    exact hC x hx
  let : IsCountablyGenerated (cocompact X) := by
    rw [← comap_dist_left_atTop_eq_cocompact p]
    infer_instance
  obtain ⟨q, hqratio, hqescape⟩ := exists_seq_tendsto_limsup
    (f := cocompact X) (u := f) hlower.isCobounded_le hupper
  refine ⟨limsup f (cocompact X),
    le_limsup_of_frequently_le hnonneg.frequently hupper, q,
    (tendsto_dist_left_cocompact_atTop p).comp hqescape, hqratio, ?_⟩
  intro C hC
  have hevent := eventually_lt_of_limsup_lt hC hupper
  rw [← comap_dist_left_atTop_eq_cocompact p, eventually_comap] at hevent
  obtain ⟨L, hL⟩ := eventually_atTop.mp hevent
  refine ⟨max L 0 + 1, by positivity, ?_⟩
  intro x hx
  exact (hL (dist p x) (by linarith [le_max_left L 0]) x rfl).le

end Poincare.AncientVolume

namespace PoincareConjecture.RicciFlow

universe u

theorem exists_finite_scalar_ratio_sequence_of_bounded_ancient
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M] [NoncompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hnonflat : ∃ p : M, 0 < (F.connection 0).scalarCurvature p)
    (t : ℝ) (ht : t ≤ 0) (p : M)
    (hfinite : ¬ ∀ L A : ℝ, ∃ x : M,
      L < ((F.metric t).edist p x).toReal ∧
      A < (F.connection t).scalarCurvature x * ((F.metric t).edist p x).toReal ^ 2) :
    ∃ A : ℝ, 0 ≤ A ∧ ∃ q : ℕ → M,
      (∀ i, 0 < (F.connection t).scalarCurvature (q i)) ∧
      Tendsto (fun i => ((F.metric t).edist p (q i)).toReal) atTop atTop ∧
      Tendsto (fun i => (F.connection t).scalarCurvature (q i) *
        ((F.metric t).edist p (q i)).toReal ^ 2) atTop (𝓝 A) ∧
      ∀ C : ℝ, A < C → ∃ L : ℝ, 0 < L ∧ ∀ x : M,
        L ≤ ((F.metric t).edist p x).toReal →
        (F.connection t).scalarCurvature x * ((F.metric t).edist p x).toReal ^ 2 ≤ C := by
  let := (F.metric t).toMetricSpace
  let : ProperSpace M := (F.metric t).properSpace_toMetricSpace (hcomplete t ht)
  have hpos := F.scalarCurvature_pos_of_bounded_ancient hC hcomplete hoperator hK hbound hnonflat
  obtain ⟨A, hA, q, hd, hratio, htail⟩ :=
    Poincare.AncientVolume.exists_finite_ratio_sequence p
      (F.connection t).scalarCurvature (fun x => (hpos t ht x).le) hfinite
  exact ⟨A, hA, q, fun i => hpos t ht (q i), hd, hratio, htail⟩

end PoincareConjecture.RicciFlow
