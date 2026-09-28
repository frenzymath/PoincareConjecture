import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.SegmentSpeed
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.PrecompactChart













set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exponential_range_subset_ball_of_precompact
    (g : RiemannianMetric n M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    let B := g.pullbackCoefficients c.symm
    let V := {v : E | Real.sqrt (B (c p) v v) < R}
    ∃ e : E → M,
      ∀ v ∈ V, e v ∈ g.ball p R := by
  classical
  dsimp only
  obtain ⟨e, _, _, _, hbound⟩ := g.exists_exponential_of_precompact_ball p hR hcompact
  refine ⟨e, ?_⟩
  intro v hv
  change g.edist p (e v) < ENNReal.ofReal R
  obtain ⟨ε, hε, γ, hγ, hγp, hγv, hγe, hbd⟩ := hbound v hv
  exact lt_of_le_of_lt hbd ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hv)



theorem exponential_image_eq_ball_of_precompact
    (g : RiemannianMetric n M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    let B := g.pullbackCoefficients c.symm
    let V := {v : E | Real.sqrt (B (c p) v v) < R}
    ∃ e : E → M,
      (∀ v ∈ V, g.edist p (e v) ≤ ENNReal.ofReal
        (Real.sqrt (B (c p) v v))) ∧
      Set.range e = g.ball p R := by
  classical
  dsimp only
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  let B := g.pullbackCoefficients c.symm
  let V := {v : E | Real.sqrt (B (c p) v v) < R}
  obtain ⟨e, _, he0, _, hexp⟩ := g.exists_exponential_of_precompact_ball p hR hcompact
  have hzero : (0 : E) ∈ V := by simpa [V] using hR
  have hbound : ∀ v ∈ V,
      g.edist p (e v) ≤ ENNReal.ofReal (Real.sqrt (B (c p) v v)) := by
    intro v hv
    obtain ⟨ε, hε, γ, hγ, hγ0, hγv, hγ1, hdist⟩ := hexp v hv
    exact hdist
  have hmem : ∀ v ∈ V, e v ∈ g.ball p R := by
    intro v hv
    exact lt_of_le_of_lt (hbound v hv) ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hv)
  have hp : p ∈ g.ball p R := he0 ▸ hmem 0 hzero
  let e' : E → M := fun v => if v ∈ V then e v else p
  have heq : ∀ v ∈ V, e' v = e v := fun v hv => if_pos hv
  refine ⟨e', fun v hv => (heq v hv).symm ▸ hbound v hv, ?_⟩
  apply Set.Subset.antisymm
  · rintro q ⟨v, rfl⟩
    by_cases hv : v ∈ V
    · rw [heq v hv]
      exact hmem v hv
    · simpa only [e', if_neg hv] using hp
  · intro q hq
    obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
      g.exists_minimizing_geodesic_of_precompact_ball p q hR hcompact hq
    let v : E := deriv (fun t => c (γ t)) 0
    have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
    have hγv : HasDerivAt (fun t => c (γ t)) v 0 :=
      (hγ.hasDerivAt_chart_at h0 p
        (by simpa only [hγ0] using mem_extChartAt_source p)).1
    have hspeed : ENNReal.ofReal (g.tangentNorm p v) = g.edist p q :=
      hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hγv hmin
    have hnorm : Real.sqrt (B (c p) v v) = g.tangentNorm p v := by
      unfold tangentNorm
      rw [show B (c p) v v = g.inner p v v from g.chartCoefficients_self p v v]
    have hv : v ∈ V := by
      change Real.sqrt (B (c p) v v) < R
      rw [hnorm]
      apply (ENNReal.ofReal_lt_ofReal_iff hR).mp
      rw [hspeed]
      exact hq
    obtain ⟨δ, hδ, η, hη, hη0, hηv, hη1, _⟩ := hexp v hv
    have hγ' : g.IsGeodesicOn γ (Icc (0 : ℝ) 1) := by
      intro t ht
      exact hγ t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hη' : g.IsGeodesicOn η (Icc (0 : ℝ) 1) := by
      intro t ht
      exact hη t ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨v, ?_⟩
    rw [heq v hv, ← hη1,
      ← geodesic_endpoint_eq_of_initial_data hγ' hη' hγ0 hη0 hγv hηv, hγ1]

end PoincareConjecture.RiemannianMetric
