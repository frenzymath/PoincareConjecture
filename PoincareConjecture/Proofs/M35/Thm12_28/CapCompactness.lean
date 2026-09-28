import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M09.RiemannianProper
import PoincareConjecture.Definitions.Ch11.BlowupLimits










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M35



theorem edist_le_intrinsicEDist
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (g : RiemannianMetric 3 M) (U : Set M) (x y : M) :
    g.edist x y ≤ intrinsicEDist g U x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply le_sInf
  rintro L ⟨gamma, hsmooth, hstart, hend, _, rfl⟩
  exact Manifold.riemannianEDist_le_pathELength hsmooth hstart hend zero_le_one

end PoincareConjecture.M35

namespace PoincareConjecture.CapCertificate

private theorem ratio_on_closure {X : Type*} [TopologicalSpace X]
    {f : X → ℝ} {U : Set X} {B : ℝ} (hf : Continuous f)
    (hratio : ∀ x ∈ U, ∀ y ∈ U, f y ≤ B * f x) :
    ∀ x ∈ closure U, ∀ y ∈ closure U, f y ≤ B * f x := by
  have hleft (y : X) (hy : y ∈ U) : closure U ⊆ {x | f y ≤ B * f x} :=
    closure_minimal (fun x hx => hratio x hx y hy)
      (isClosed_le continuous_const (continuous_const.mul hf))
  intro x hx
  exact closure_minimal (fun y hy => hleft y hy hx)
    (isClosed_le hf continuous_const)



theorem isCompact_closure
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g) (hcomplete : MetricComplete g) :
    IsCompact (closure N.carrier) := by
  obtain ⟨x, hx⟩ := N.core_nonempty
  have hxU : x ∈ N.carrier := by
    have hc := N.core_eq_interior_closed_core ▸ hx
    exact (N.closed_core_eq_complement_end ▸ interior_subset hc).1
  let r := N.cap_constant * scalarCurvatureSupOn g N.connection N.carrier ^ (-1 / 2 : ℝ)
  have hball : N.carrier ⊆ g.ball x r := by
    intro y hy
    have hdiam : intrinsicEDist g N.carrier x y ≤ intrinsicDiameter g N.carrier :=
      le_sSup ⟨(⟨x, hxU⟩, ⟨y, hy⟩), rfl⟩
    exact ((M35.edist_le_intrinsicEDist g N.carrier x y).trans hdiam).trans_lt
      N.intrinsic_diameter_bound
  exact (Proofs.M09.isCompact_closure_metric_ball g hcomplete x r).of_isClosed_subset
    isClosed_closure (closure_mono hball)




theorem scalar_ratio_on_closure
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g)
    (hR : Continuous N.connection.scalarCurvature) :
    ∃ B : ℝ, 0 < B ∧ B < N.cap_constant ∧
      ∀ x ∈ closure N.carrier, ∀ y ∈ closure N.carrier,
        N.connection.scalarCurvature y ≤ B * N.connection.scalarCurvature x := by
  obtain ⟨B, hBC, hratio⟩ := N.scalar_ratio
  obtain ⟨x, hx⟩ := N.core_nonempty
  have hxU : x ∈ N.carrier := by
    have hc := N.core_eq_interior_closed_core ▸ hx
    exact (N.closed_core_eq_complement_end ▸ interior_subset hc).1
  have hB : 0 < B := by
    have hpos := N.scalar_pos x hxU
    have hself := hratio x hxU x hxU
    nlinarith
  exact ⟨B, hB, hBC, ratio_on_closure hR hratio⟩



theorem exists_positive_scalar_bounds_on_closure
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    {g : RiemannianMetric 3 M} (N : CapCertificate g)
    (hR : Continuous N.connection.scalarCurvature) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ x ∈ closure N.carrier,
      a ≤ N.connection.scalarCurvature x ∧ N.connection.scalarCurvature x ≤ b := by
  obtain ⟨B, hB, _, hratio⟩ := N.scalar_ratio_on_closure hR
  obtain ⟨y, hy⟩ := N.core_nonempty
  have hyU : y ∈ N.carrier := by
    have hc := N.core_eq_interior_closed_core ▸ hy
    exact (N.closed_core_eq_complement_end ▸ interior_subset hc).1
  have hpos := N.scalar_pos y hyU
  refine ⟨N.connection.scalarCurvature y / B, B * N.connection.scalarCurvature y,
    div_pos hpos hB, mul_pos hB hpos, ?_⟩
  intro x hx
  refine ⟨(div_le_iff₀ hB).mpr ?_, hratio y (subset_closure hyU) x hx⟩
  simpa only [mul_comm] using hratio x hx y (subset_closure hyU)

end PoincareConjecture.CapCertificate
