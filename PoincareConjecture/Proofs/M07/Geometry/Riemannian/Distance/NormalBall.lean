import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.PrecompactChart
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.NormalRadius
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.NormalRadial

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_exponential_endpoint_edist_le_tangentNorm
    (g : RiemannianMetric n M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    let B := g.pullbackCoefficients c.symm
    let V := {v : E | Real.sqrt (B (c p) v v) < R}
    ∃ e : E → M,
      (∀ v ∈ V, g.edist p (e v) ≤ ENNReal.ofReal (g.tangentNorm p v)) := by
  classical
  dsimp only
  let E := EuclideanSpace ℝ (Fin n)
  let c := extChartAt (𝓡 n) p
  let B := g.pullbackCoefficients c.symm
  let V := {v : E | Real.sqrt (B (c p) v v) < R}
  obtain ⟨e, _, _, _, hbound⟩ := g.exists_exponential_of_precompact_ball p hR hcompact
  refine ⟨e, ?_⟩
  intro v hv
  obtain ⟨ε, hε, γ, hγ, hγp, hγv, hγe, hdist⟩ := hbound v hv
  have hnorm : g.tangentNorm p v = Real.sqrt (B (c p) v v) := by
    change Real.sqrt (g.inner p v v) = Real.sqrt (B (c p) v v)
    congr 1
    simpa [c, B] using (chartCoefficients_self g p v v).symm
  rw [hnorm]
  exact hdist

theorem radial_geodesic_subarc_edist_le_tangentNorm
    (g : RiemannianMetric n M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (v : EuclideanSpace ℝ (Fin n))
    (hv : Real.sqrt (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) v v) < R) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 ∧
      ∀ t ∈ Ioo (-ε) (1 + ε),
        g.edist p (γ t) ≤ ENNReal.ofReal (g.tangentNorm p v) * ENNReal.ofReal |t| := by
  obtain ⟨ε, hε, γ, hγ, hγp, hγv, _⟩ :=
    g.exists_geodesic_through_one_of_precompact_ball p hR hcompact v hv
  refine ⟨ε, hε, γ, hγ, hγp, hγv, ?_⟩
  intro t ht
  have h := hγ.edist_le_initial_speed ⟨by linarith, by linarith⟩ hγp hγv ht
  have hnorm : g.tangentNorm p v = Real.sqrt (g.pullbackCoefficients
      (extChartAt (𝓡 n) p).symm (extChartAt (𝓡 n) p p) v v) := by
    change Real.sqrt (g.inner p v v) = _
    congr 1
    exact (chartCoefficients_self g p v v).symm
  rw [hnorm]
  exact h

theorem exists_exponential_chart_gauss_radial_lower_bound
    (g : RiemannianMetric n M) (p : M) :
    let E := EuclideanSpace ℝ (Fin n)
    ∃ e : OpenPartialHomeomorph E M,
      (0 : E) ∈ e.source ∧ e 0 = p ∧
      ∀ v ∈ e.source, ∀ w : E,
        g.inner p v w ^ 2 ≤
          g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
            (mfderiv (𝓡 n) (𝓡 n) e v v) *
          g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v w)
            (mfderiv (𝓡 n) (𝓡 n) e v w) := by
  classical
  dsimp only
  obtain ⟨e, h0, he0, _, _, hgauss, _, _⟩ :=
    exists_exponential_chart_gauss g p
  refine ⟨e, h0, he0, ?_⟩
  intro v hv w
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hCS :
      (g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
        (mfderiv (𝓡 n) (𝓡 n) e v w)) ^ 2 ≤
        g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
          (mfderiv (𝓡 n) (𝓡 n) e v v) *
        g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v w)
          (mfderiv (𝓡 n) (𝓡 n) e v w) := by
    change (inner ℝ (mfderiv (𝓡 n) (𝓡 n) e v v)
      (mfderiv (𝓡 n) (𝓡 n) e v w)) ^ 2 ≤
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) e v v)
        (mfderiv (𝓡 n) (𝓡 n) e v v) *
      inner ℝ (mfderiv (𝓡 n) (𝓡 n) e v w)
        (mfderiv (𝓡 n) (𝓡 n) e v w)
    simpa [pow_two, real_inner_self_eq_norm_sq] using
      (real_inner_mul_inner_self_le
        (mfderiv (𝓡 n) (𝓡 n) e v v)
        (mfderiv (𝓡 n) (𝓡 n) e v w))
  rw [← hgauss v hv w]
  exact hCS

theorem exists_tangentBall_edist_eq_of_gauss
    (g : RiemannianMetric n M) (p : M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ e.source) (he0 : e 0 = p)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (he' : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    (hgauss : ∀ v ∈ e.source, ∀ w : EuclideanSpace ℝ (Fin n),
      g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
        (mfderiv (𝓡 n) (𝓡 n) e v w) = g.inner p v w) :
    ∃ r : ℝ, 0 < r ∧ {v | g.tangentNorm p v < r} ⊆ e.source ∧
      ∀ v, g.tangentNorm p v < r →
        g.edist p (e v) = ENNReal.ofReal (g.tangentNorm p v) := by
  obtain ⟨a, ha, hasource⟩ := g.exists_tangentBall_subset_nhds p
    (e.open_source.mem_nhds h0)
  obtain ⟨b, hb, _, hblow⟩ := g.exists_ball_tangentNorm_inverse_le_edist p e h0 he0 he he' hgauss
  refine ⟨min a (b : ℝ), lt_min ha (by exact_mod_cast hb), ?_, ?_⟩
  · intro v hv
    apply hasource
    change g.tangentNorm p v < a
    exact hv.trans_le (min_le_left _ _)
  · intro v hv
    have hsource : v ∈ e.source := hasource (hv.trans_le (min_le_left _ _))
    have hradial : ∀ t ∈ Icc (0 : ℝ) 1, t • v ∈ e.source := by
      intro t ht
      apply hasource
      change g.tangentNorm p (t • v) < a
      have hnorm : g.tangentNorm p (t • v) = t * g.tangentNorm p v := by
        simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
        rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.1]
      rw [hnorm]
      calc
        t * g.tangentNorm p v ≤ 1 * g.tangentNorm p v :=
          mul_le_mul_of_nonneg_right ht.2 (Real.sqrt_nonneg _)
        _ < a := by simpa using hv.trans_le (min_le_left _ _)
    have hupper := g.edist_radial_le_of_gauss p e he0 he hgauss v hradial
    apply le_antisymm hupper
    have hsmall : g.edist p (e v) < b := by
      apply hupper.trans_lt
      rw [← ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.ofReal_lt_ofReal_iff (by exact_mod_cast hb)).mpr
        (hv.trans_le (min_le_right _ _))
    have hlower := hblow (e v) hsmall
    rwa [e.left_inv hsource] at hlower

end PoincareConjecture.RiemannianMetric
