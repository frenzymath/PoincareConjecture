import PoincareConjecture.Proofs.M47.TerminalSourceNormalCharts
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Covering
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Bounds.Ricci
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareConjecture.Proofs.M36.MetricComparison










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [SecondCountableTopology M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]



theorem terminalSourceNormal_exists_finite_chart_cover
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (p0 : M)
    {A R rho K : ℝ} (hA : 0 < A) (hrho : 0 < rho) (hrhoR : rho / 4 < R)
    (hK : 0 ≤ K) (hcompact : IsCompact (closure (g.ball p0 (5 * A))))
    (hcurv : ∀ x ∈ g.ball p0 (5 * A), D.curvatureTensorNorm x ≤ K)
    (hcharts : ∀ p ∈ g.ball p0 A,
      ∃ C : TerminalSourceChart g R, C.centre = p) :
    let d := min (A / 2) (rho / 4)
    ∃ S : Finset M, p0 ∈ S ∧ (↑S : Set M) ⊆ g.ball p0 A ∧
      S.card ≤ ⌈RiemannianMetric.modelVolume 3 K (3 * A) /
        RiemannianMetric.modelVolume 3 K (d / 2)⌉₊ + 1 ∧
      ∃ chart : S → TerminalSourceChart g R,
        (∀ p, (chart p).centre = p.val) ∧
        (∀ p, IsCompact ((chart p).chart '' Metric.closedBall (0 : E) (rho / 4))) ∧
        g.ball p0 A ⊆ ⋃ p : S, (chart p).chart '' Metric.closedBall (0 : E) (rho / 4) := by
  classical
  let d := min (A / 2) (rho / 4)
  have hd : 0 < d := lt_min (by positivity) (by positivity)
  have hdA : d ≤ A := (min_le_left _ _).trans (by linarith only [hA])
  have hdrho : d ≤ rho / 4 := min_le_right _ _
  have hRic : ∀ x ∈ g.ball p0 (5 * A), ∀ v : TangentSpace (𝓡 3) x,
      -(((3 : ℝ) - 1) * K) * g.inner x v v ≤ D.ricci x v v := by
    intro x hx v
    have hsectional (a b : TangentSpace (𝓡 3) x) :
        |D.sectionalCurvature x a b| ≤ K :=
      (D.abs_sectionalCurvature_le_curvatureTensorNorm x a b).trans (hcurv x hx)
    simpa only [Nat.cast_ofNat, neg_mul] using
      D.ricci_quadratic_lower_bound_of_abs_sectionalCurvature_le x K hsectional v
  obtain ⟨S0, hS0, hcard, _hseparated, hcover⟩ :=
    g.exists_finset_cover_of_precompact_ball p0 (by norm_num) hA hd hdA hK hcompact D hRic
  let S := insert p0 S0
  have hp0 : p0 ∈ g.ball p0 A := by
    change g.edist p0 p0 < ENNReal.ofReal A
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hA
  have hS : (↑S : Set M) ⊆ g.ball p0 A := by
    intro p hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact hp0
    · exact hS0 hp
  choose chart hcentre using fun p : S => hcharts p.val (hS p.property)
  refine ⟨S, Finset.mem_insert_self _ _, hS,
    (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hcard 1), chart, hcentre, ?_, ?_⟩
  · intro p
    apply (isCompact_closedBall (0 : E) (rho / 4)).image_of_continuousOn
    apply (chart p).chart.contMDiffOn.continuousOn.mono
    rw [(chart p).source]
    exact Metric.closedBall_subset_ball hrhoR
  · intro y hy
    obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp (hcover hy)
    let q : S := ⟨p, Finset.mem_insert_of_mem hp⟩
    have htarget : y ∈ (chart q).chart.target := by
      rw [(chart q).target, hcentre q]
      exact hyp.trans_le (ENNReal.ofReal_le_ofReal (hdrho.trans hrhoR.le))
    have hsource : (chart q).chart.symm y ∈ Metric.ball (0 : E) R :=
      (chart q).source ▸ (chart q).chart.map_target htarget
    have hinverse : (chart q).chart ((chart q).chart.symm y) = y :=
      (chart q).chart.right_inv htarget
    have hradial := (chart q).distance ((chart q).chart.symm y) hsource
    rw [hinverse, hcentre q] at hradial
    have hnorm : ‖(chart q).chart.symm y‖ < d := by
      apply (ENNReal.ofReal_lt_ofReal_iff hd).mp
      rw [← hradial]
      exact hyp
    refine mem_iUnion.mpr ⟨q, (chart q).chart.symm y, ?_, hinverse⟩
    simpa only [Metric.mem_closedBall, dist_zero_right] using hnorm.le.trans hdrho

end PoincareConjecture.M47
