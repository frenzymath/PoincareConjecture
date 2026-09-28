import PoincareConjecture.Proofs.M47.CanonicalNeckScalarComparison
import PoincareConjecture.Proofs.M47.CanonicalNeckClosedScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem scalar_bottom_bounds_of_cylinder_error {R Q epsilon : ℝ}
    (hQ : 0 < Q) (hsmall : epsilon ≤ 1 / 200)
    (herror : |R / Q - 1 / 2| ≤ (16 / 5 : ℝ) * epsilon) :
    (121 / 250 : ℝ) * Q ≤ R ∧ R ≤ (129 / 250 : ℝ) * Q := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp herror
  have hlower : (121 / 250 : ℝ) ≤ R / Q := by linarith only [hlo, hsmall]
  have hupper : R / Q ≤ (129 / 250 : ℝ) := by linarith only [hhi, hsmall]
  exact ⟨(le_div_iff₀ hQ).mp hlower, (div_le_iff₀ hQ).mp hupper⟩

theorem ordinary_closed_neck_scalar_difference_le (hC : RicciFlowCurvatureTheory.{u})
    {M : Type u} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {J : Set ℝ} (G : RicciFlow 3 M J) (T : ℝ) (N : EpsilonNeck (G.metric T))
    (hsmall : N.epsilon ≤ 1 / 200) {Q : ℝ} (hQ : 0 < Q)
    (hclock : ∀ s ∈ Icc (-1 : ℝ) 0, T + s / Q ∈ J)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun s z v w => Q * roundCylinderPullback
        (G.metric (T + s / Q)) N.coordinate_map z v w))
    (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) (x : M) (hx : x ∈ N.carrier) :
    |(G.connection (T + s / Q)).scalarCurvature x / Q - 1 / (1 - s)| ≤
      (16 / 5 : ℝ) * N.epsilon := by
  have hstrict (v : ℝ) (hv : v ∈ Ioc (-1 : ℝ) 0) :
      |(G.connection (T + v / Q)).scalarCurvature x / Q - 1 / (1 - v)| ≤
        (16 / 5 : ℝ) * N.epsilon :=
    neck_pullback_scalar_difference_le N hsmall (G.metric (T + v / Q))
      (G.connection (T + v / Q)) hQ hv.2 (hfamily.at_time hv) x hx
  have hmap : Continuous (fun v : ℝ => (T + v / Q, x)) := by fun_prop
  have hscalar : ContinuousOn
      (fun v : ℝ => (G.connection (T + v / Q)).scalarCurvature x / Q)
      (Icc (-1 : ℝ) 0) :=
    ((hC.scalar_regular 3 M J G).continuousOn.comp hmap.continuousOn
      (fun v hv => ⟨hclock v hv, mem_univ x⟩)).div_const Q
  have hmodel : ContinuousOn (fun v : ℝ => 1 / (1 - v)) (Icc (-1 : ℝ) 0) :=
    continuousOn_const.div (continuousOn_const.sub continuousOn_id)
      (fun v hv => by linarith only [hv.2])
  have hclosure : closure (Ioc (-1 : ℝ) 0) = Icc (-1 : ℝ) 0 :=
    closure_Ioc (by norm_num)
  exact le_on_closure hstrict (hclosure.symm ▸ (hscalar.sub hmodel).abs)
    continuousOn_const (hclosure.symm ▸ hs)

end PoincareConjecture.Proofs.M47
