import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.Cylinders.Scalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.TimeTranslation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.RicciFlow

theorem exists_terminal_cylinder_derivative_constant
    {m : ℕ} (hC : RicciFlowCurvatureTheory.{u}) (hm : 0 < m) (k : ℕ)
    {S A r scale : ℝ} (hS : 0 < S) (hA : 0 < A) (hr : 0 < r)
    (hscale : 0 < scale) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [T3Space M] [SecondCountableTopology M]
        [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) M]
        [IsManifold (𝓡 (m + 1)) ∞ M] (J : Set ℝ)
        (F : RicciFlow (m + 1) M J) (a b : ℝ),
        a < b → Icc a b ⊆ interior J →
        (∀ t ∈ Icc a b, MetricComplete (F.metric t)) →
        (∀ t ∈ Icc a b, ∀ x : M,
          (F.connection t).NonnegativeCurvatureOperator x) →
        ∀ p : M, b - a ≤ A / (((m + 1 : ℕ) : ℝ) ^ 2 * S) →
        r / 4 + (4 * ((m + 1 : ℕ) : ℝ) * scale + 8 * S / scale) * (b - a) < r / 2 →
        (∀ t ∈ Icc a b, ∀ x ∈ (F.metric b).ball p r,
          (F.connection t).scalarCurvature x ≤ S) →
        ∀ t ∈ Ioc a b, ∀ x : M,
          (F.metric b).edist p x ≤ ENNReal.ofReal (r / 4) →
          (F.connection t).curvatureDerivativeNorm k x ≤ C / (t - a) ^ ((k : ℝ) / 2) := by
  let K := ((m + 1 : ℕ) : ℝ) ^ 2 * S
  have hK : 0 < K := by dsimp only [K]; positivity
  obtain ⟨C, hCpos, hShi⟩ := hC.local_derivative_estimates (m + 1) k K A r hK hA hr
  refine ⟨C, hCpos, ?_⟩
  intro M _ _ _ _ _ J F a b hab hJ hcomplete hoperator p htime hgap hscalar
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  have hRic (t : ℝ) (ht : t ∈ Icc a b) (x : M)
      (v : TangentSpace (𝓡 (m + 1)) x) : 0 ≤ (F.connection t).ricci x v v :=
    ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) M (F.metric t) (F.connection t)) x (hoperator t ht x) v).1
  have hball (t : ℝ) (ht : t ∈ Icc a b) (R : ℝ) :
      (F.metric t).ball p R ⊆ (F.metric b).ball p R :=
    F.ball_subset_ball_of_ricci_nonneg hJ p R ht hb ht.2
      (fun s hs x _ v => hRic s hs x v)
  have hupper (t : ℝ) (ht : t ∈ Icc a b) (x : M)
      (hx : x ∈ (F.metric t).ball p (r / 2)) (v : TangentSpace (𝓡 (m + 1)) x) :
      (F.connection t).ricci x v v ≤ S * (F.metric t).inner x v v := by
    have hx' : x ∈ (F.metric b).ball p r :=
      (hball t ht (r / 2) hx).trans_le (ENNReal.ofReal_le_ofReal (by linarith))
    have h := ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator
      (hC.tensor_calculus (m + 1) M (F.metric t) (F.connection t)) x
        (hoperator t ht x) v).2
    have hv : 0 ≤ (F.metric t).inner x v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact ((F.metric t).pos x v hv).le
    exact h.trans (mul_le_mul_of_nonneg_right (hscalar t ht x hx') hv)
  have hshift : (fun t : ℝ => t + a) '' Icc 0 (b - a) ⊆ J := by
    rintro _ ⟨t, ht, rfl⟩
    exact interior_subset (hJ ⟨by linarith [ht.1], by linarith [ht.2]⟩)
  have hne : (Icc (0 : ℝ) (b - a)).Nontrivial :=
    ⟨0, ⟨le_rfl, by linarith⟩, b - a, ⟨by linarith, le_rfl⟩, by linarith⟩
  let Ft := F.translate a hshift ordConnected_Icc hne
  have hcompact : IsCompact (closure ((Ft.metric 0).ball p r)) := by
    change IsCompact (closure ((F.metric (0 + a)).ball p r))
    rw [zero_add]
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨(F.metric a).toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (m + 1)))
        (TangentSpace (𝓡 (m + 1)) : M → Type _) :=
      ⟨⟨(F.metric a).inner, (F.metric a).toContinuousRiemannianMetric.continuous,
        fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 (m + 1)) M
    apply ((F.metric a).isCompact_closedBall_of_metricComplete (hcomplete a ha) p r).of_isClosed_subset
      isClosed_closure
    apply closure_minimal
    · exact fun x hx => (show (F.metric a).edist p x < ENNReal.ofReal r from hx).le
    · exact isClosed_le (continuous_const.edist continuous_id) continuous_const
  have hcurv : ∀ t ∈ Icc 0 (b - a), ∀ x ∈ (Ft.metric 0).ball p r,
      (Ft.connection t).curvatureTensorNorm x ≤ K := by
    intro t ht x hx
    have ht' : t + a ∈ Icc a b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hx' : x ∈ (F.metric a).ball p r := by
      simpa only [Ft, translate, zero_add] using hx
    have h := (F.connection (t + a)).curvatureTensorNorm_le_scalarCurvature
      (hC.tensor_calculus (m + 1) M (F.metric (t + a)) (F.connection (t + a))) x
      (hoperator (t + a) ht' x)
    exact h.trans (mul_le_mul_of_nonneg_left
      (hscalar (t + a) ht' x (hball a ha r hx')) (by positivity))
  have hderiv := hShi M (b - a) (by linarith) htime Ft p hcompact hcurv
  intro t ht x hx
  have hxinitial := (terminal_closedBall_distance_bound hC F hm hab.le hJ hcomplete hRic p
    hS.le hscale (by positivity : 0 ≤ r / 4) hupper hgap a ha x hx).2
  have hx' : x ∈ (Ft.metric 0).ball p (r / 2) := by
    simpa only [Ft, translate, zero_add] using hxinitial
  have h := hderiv (t - a) ⟨by linarith [ht.1], by linarith [ht.2]⟩ x hx'
  change (F.connection (t - a + a)).curvatureDerivativeNorm k x ≤
    C / (t - a) ^ ((k : ℝ) / 2) at h
  rwa [_root_.sub_add_cancel] at h

end PoincareConjecture.RicciFlow
