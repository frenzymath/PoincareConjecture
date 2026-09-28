import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.AncientCriterion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.Scaling
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Rescaling.Closed
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Myers.Compact
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.Sectional










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientKappaRoundness

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

private theorem round_slice_contractions
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g) (hround : IsRoundMetricSlice D) :
    ∃ r : ℝ, 0 < r ∧ (∀ x, D.scalarCurvature x = 6 * r) ∧
      ∀ x, ∀ v w : TangentSpace (𝓡 3) x, D.ricci x v w = 2 * r * g.inner x v w := by
  obtain ⟨r, hr, hcurv⟩ := hround
  have hsec (x : M) (v w : TangentSpace (𝓡 3) x)
      (hgram : g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 ≠ 0) :
      D.sectionalCurvature x v w = r := by
    unfold LeviCivitaData.sectionalCurvature
    rw [hcurv]
    exact mul_div_cancel_right₀ r hgram
  refine ⟨r, hr, fun x => ?_, fun x v w => ?_⟩
  · convert D.scalarCurvature_of_constant_sectional x r (hsec x) using 1 <;> norm_num
  · convert D.ricci_of_constant_sectional x r (hsec x) v w using 1 <;> norm_num



theorem ricciComplement_mem_of_isRoundMetricSlice
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (hround : IsRoundMetricSlice D)
    {c : ℝ} (hc : 1 ≤ c) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    D.ricciComplementTensor hD x ∈ tensorPinchingCone c := by
  obtain ⟨r, hr, hscalar, hric⟩ := round_slice_contractions D hround
  rw [ricciComplement_mem_tensorPinchingCone_iff]
  have heval (v : TangentSpace (𝓡 3) x) (hv : g.inner x v v = 1) :
      D.ricciComplementEvaluation x ![v, v] = r := by
    change (D.scalarCurvature x / 2) * g.inner x v v - D.ricci x v v = r
    rw [hscalar, hric, hv]
    ring
  constructor
  · intro v hv
    rw [heval v hv]
    exact hr.le
  · intro v w hv hw
    rw [heval v hv, heval w hw]
    nlinarith


theorem compactSpace_of_isRoundMetricSlice [T3Space M] [PreconnectedSpace M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (hround : IsRoundMetricSlice D) : CompactSpace M := by
  obtain ⟨r, hr, _, hric⟩ := round_slice_contractions D hround
  apply g.compactSpace_of_positive_ricci D hcomplete (show 0 < 2 * r by positivity)
  intro x v
  rw [hric]

private theorem isRoundMetricSlice_of_metric_eq
    {g h : RiemannianMetric 3 M} (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (heq : g = h) (hround : IsRoundMetricSlice D) : IsRoundMetricSlice D' := by
  subst h
  simpa only [IsRoundMetricSlice, D.horizon_curvatureTensor_eq D'] using hround

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]



theorem isRoundAncientKappaSolution_of_closedTimeShift
    {d : ℕ} (H : M22UniversalNoncollapsingPredecessors.{u} d)
    (K : AncientKappaSolution 3 M) (b : ℝ) (hb : b ≤ 0)
    (R : OrdinaryParabolicRescaling (I := closedAncientInterval) K.flow 1 zero_lt_one b)
    (hround : IsRoundAncientKappaSolution (K.closedTimeShift b hb R)) :
    IsRoundAncientKappaSolution K := by
  let : CompactSpace M := compactSpace_of_isRoundMetricSlice
    ((K.closedTimeShift b hb R).flow.connection 0)
    ((K.closedTimeShift b hb R).complete 0 le_rfl) (hround 0 le_rfl)
  apply isRoundAncientKappaSolution_of_early_pinching H K
  intro c hc t ht
  let a := min (t - 1) b
  have hab : a ≤ b := min_le_right _ _
  have hat : a < t := (min_le_left _ _).trans_lt (by linarith)
  have hshift : IsRoundMetricSlice ((K.closedTimeShift b hb R).flow.connection (a - b)) :=
    hround (a - b) (sub_nonpos.mpr hab)
  have horig : IsRoundMetricSlice (K.flow.connection a) := by
    have h := isRoundMetricSlice_of_metric_eq
      ((K.closedTimeShift b hb R).flow.connection (a - b))
      (K.flow.connection ((a - b) + b)) (K.closedTimeShift_metric b hb R (a - b)) hshift
    rw [show a - b + b = a by ring] at h
    exact h
  refine ⟨a, hat, fun x => ?_⟩
  exact ricciComplement_mem_of_isRoundMetricSlice (K.flow.connection a)
    (H.tensor_calculus 3 M _ _) horig hc.le x

end PoincareConjecture.AncientKappaRoundness
