import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.LocalVolumeCover
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.LocalNormalCharts
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.NormalCoverAssembly

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace PoincareConjecture.M28

theorem exists_uniform_normalCover_of_local_noncollapse
    (n : ℕ) {K δ v V : ℝ} (hn : 1 ≤ n) (hK : 0 ≤ K)
    (hδ : 0 < δ) (hv : 0 < v) (hV : 0 ≤ V) :
    ∃ R ρ : ℝ, ∃ N : ℕ, 0 < ρ ∧ 2 * ρ < R ∧ R < δ ∧
      ∀ (M : Type u) [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
        [T3Space M] [SecondCountableTopology M] [PreconnectedSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
        (g : RiemannianMetric n M) (D : LeviCivitaData g) (p : M)
        (r S : ℝ), 0 < r → r + 2 * δ ≤ S →
        IsCompact (closure (g.ball p S)) →
        (∀ x ∈ g.ball p S, D.curvatureTensorNorm x ≤ K) →
        (∀ q ∈ g.ball p r, ENNReal.ofReal v ≤ g.volumeMeasure (g.ball q δ)) →
        g.volumeMeasure (g.ball p S) ≤ ENNReal.ofReal V →
        Nonempty (NormalChartCover (fun _ => g) p (-1) 1 r R ρ (1 / 4) (9 / 4) N) := by
  let R := RiemannianMetric.localInjectivityRadius n K δ v
  have hR : 0 < R := RiemannianMetric.localInjectivityRadius_pos n K hδ v
  have hRδ : R < δ := RiemannianMetric.localInjectivityRadius_lt n K hδ v
  obtain ⟨ρ, hρ, hρR, hsmall⟩ :=
    RiemannianMetric.exists_uniform_radial_comparison_radius hR K
  let w := RiemannianMetric.smallerBallVolumeBound n K δ v ((ρ / 4) / 2)
  have hw : 0 < w :=
    RiemannianMetric.smallerBallVolumeBound_pos hn hK hδ hv (by positivity)
  refine ⟨R, ρ, ⌈V / w⌉₊ + 1, hρ, hρR, hRδ, ?_⟩
  intro M _ _ _ _ _ _ _ _ g D p r S hr hmargin hcompact hcurv hvol hupper
  have hsmallvol (q : M) (hq : q ∈ g.ball p r) :
      ENNReal.ofReal w ≤ g.volumeMeasure (g.ball q ((ρ / 4) / 2)) := by
    have hsub := riemannian_ball_subset_of_margin g hr.le
      (by positivity : 0 ≤ 2 * δ) hq hmargin
    exact (g.smallerBall_volume_lower_bound_of_curvatureTensorNorm_le D q
      hn hK hδ hv (hcompact.of_isClosed_subset isClosed_closure (closure_mono hsub))
      (fun x hx => hcurv x (hsub hx)) (hvol q hq) (by positivity)
      (by linarith : (ρ / 4) / 2 ≤ δ)).2
  have hcover := exists_finset_cover_of_local_volume_bounds g p hr
    (by positivity : 0 < ρ / 4) (by linarith : r + (ρ / 4) / 2 ≤ S)
    hw hV hupper hsmallvol
  exact exists_normalChartCover_of_normal_charts g p hr hρ hρR hcover
    (exists_normal_chart_of_local_noncollapse g D p hn hK hδ hv hr hmargin
      rfl hρR hsmall hcompact hcurv hvol)

end PoincareConjecture.M28
