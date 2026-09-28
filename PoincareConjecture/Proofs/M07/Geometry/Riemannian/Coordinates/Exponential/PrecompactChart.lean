import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.PrecompactExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.SmoothExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.EndpointAgreement

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

theorem exists_exponential_of_precompact_ball
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    let B := g.pullbackCoefficients c.symm
    let V := {v : E | Real.sqrt (B (c p) v v) < R}
    ∃ e : E → M,
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e V ∧ e 0 = p ∧
      HasFDerivAt (fun v => c (e v)) (ContinuousLinearMap.id ℝ E) 0 ∧
      ∀ v ∈ V, ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
        g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
        HasDerivAt (fun t => c (γ t)) v 0 ∧ γ 1 = e v ∧
        g.edist p (e v) ≤ ENNReal.ofReal (Real.sqrt (B (c p) v v)) := by
  classical
  dsimp only
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  let B := g.pullbackCoefficients c.symm
  let V := {v : E | Real.sqrt (B (c p) v v) < R}
  have hV : IsOpen V := by
    apply isOpen_lt _ continuous_const
    exact Real.continuous_sqrt.comp
      ((continuous_const.clm_apply continuous_id).clm_apply continuous_id)
  have hzero : (0 : E) ∈ V := by simpa [V] using hR
  have hex : ∀ v : E, ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M, v ∈ V →
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
      HasDerivAt (fun t => c (γ t)) v 0 ∧
      g.edist p (γ 1) ≤ ENNReal.ofReal (Real.sqrt (B (c p) v v)) := by
    intro v
    by_cases hv : v ∈ V
    · obtain ⟨ε, hε, γ, hγ⟩ :=
        g.exists_geodesic_through_one_of_precompact_ball p hR hcompact v hv
      exact ⟨ε, hε, γ, fun _ => hγ⟩
    · exact ⟨1, by norm_num, fun _ => p, fun h => (hv h).elim⟩
  choose ε hε Γ hΓ using hex
  have hgeo {v : E} (hv : v ∈ V) :
      ∀ᶠ z in 𝓝 v, g.IsGeodesicOn (Γ z) (Icc (0 : ℝ) 1) := by
    filter_upwards [hV.mem_nhds hv] with z hz
    intro t ht
    exact (hΓ z hz).1 t ⟨by linarith [hε z, ht.1], by linarith [hε z, ht.2]⟩
  have hinit {v : E} (hv : v ∈ V) : ∀ᶠ z in 𝓝 v, Γ z 0 = p := by
    filter_upwards [hV.mem_nhds hv] with z hz
    exact (hΓ z hz).2.1
  have hvel {v : E} (hv : v ∈ V) :
      ∀ᶠ z in 𝓝 v, HasDerivAt (fun t => c (Γ z t)) z 0 := by
    filter_upwards [hV.mem_nhds hv] with z hz
    exact (hΓ z hz).2.2.1
  obtain ⟨hend0, hderiv⟩ := g.geodesic_endpoint_zero_and_hasFDerivAt p Γ
    (hgeo hzero) (hinit hzero) (hvel hzero)
  refine ⟨fun v => Γ v 1, ?_, hend0, hderiv, ?_⟩
  · intro v hv
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_geodesic_endpoint (hgeo hv) (convex_Icc (0 : ℝ) 1)
      (a := 0) (by norm_num) (by norm_num)
    · exact contMDiffAt_const.congr_of_eventuallyEq (hinit hv)
    · rw [(hΓ v hv).2.1]
      apply contDiffAt_id.congr_of_eventuallyEq
      filter_upwards [hvel hv] with z hz
      exact hz.deriv
  · intro v hv
    exact ⟨ε v, hε v, Γ v, (hΓ v hv).1, (hΓ v hv).2.1,
      (hΓ v hv).2.2.1, rfl, (hΓ v hv).2.2.2⟩

end PoincareConjecture.RiemannianMetric
