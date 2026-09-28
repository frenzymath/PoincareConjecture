import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_NeckContainment
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_NeckScalar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_SphereNeckObstruction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal ContinuousMap

namespace PoincareConjecture.M44

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_uniform_neck_exclusion_cutoff {K D k : ℝ}
    (hK : 0 < K) (hD : 0 < D) (hk : 0 < k) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ (g0 : StandardInitialMetric) (R h : ℝ), 0 < R → 0 < h →
      ∀ (sphere : C(UnitTwoSphere, g0.metric.ball 0 R))
        (transport : C(g0.metric.ball 0 R, M)),
      (∀ x, N.connection.scalarCurvature (transport x) ≤ K / h ^ 2) →
      (∀ x y, g.edist (transport x) (transport y) < ENNReal.ofReal (h * D)) →
      ContMDiff (𝓡 2) (𝓡 3) ∞ (transport.comp sphere) →
      (∀ z, Function.Injective (mfderiv (𝓡 2) (𝓡 3) (transport.comp sphere) z)) →
      (∀ z, ∀ u v : TangentSpace (𝓡 2) z,
        let f := transport.comp sphere
        let Df := mfderiv (𝓡 2) (𝓡 3) f z
        0 < g.inner (f z) (Df u) (Df u) * g.inner (f z) (Df v) (Df v) -
          (g.inner (f z) (Df u) (Df v)) ^ 2 →
          k / h ^ 2 < N.connection.sectionalCurvature (f z) (Df u) (Df v)) →
      Disjoint (range transport) N.central_sphere := by
  have h2K : 0 < 2 * K := by positivity
  obtain ⟨ds, hds, hscalar⟩ := exists_neck_scalar_ratio_cutoff
  obtain ⟨db, hdb, hbuffer⟩ := exists_neck_containment_cutoff h2K hD
  obtain ⟨dn, hdn, hneck⟩ := exists_sphere_neck_obstruction_cutoff (div_pos hk h2K)
  refine ⟨min ds (min db dn), lt_min hds (lt_min hdb hdn), ?_⟩
  intro M _ _ _ _ g N hsmall g0 R h hR hh sphere transport hRbound hdiam hf himm hplane
  apply disjoint_left.mpr
  rintro y ⟨x, rfl⟩ hx
  have hc := hscalar N (hsmall.trans (min_le_left _ _)) (transport x)
    (N.central_sphere_subset hx)
  have hcenter : N.connection.scalarCurvature N.center ≤ (2 * K) / h ^ 2 := by
    have hdouble := mul_le_mul_of_nonneg_left (hRbound x) (by norm_num : (0 : ℝ) ≤ 2)
    rw [← mul_div_assoc] at hdouble
    exact hc.le.trans hdouble
  have hcenter' : N.connection.scalarCurvature N.center * h ^ 2 ≤ 2 * K :=
    (le_div_iff₀ (sq_pos_of_pos hh)).mp hcenter
  have hmem (y) : transport y ∈ N.carrier :=
    hbuffer N (hsmall.trans ((min_le_right _ _).trans (min_le_left _ _)))
      h hh hcenter' (transport x) hx (hdiam x y)
  apply hneck N (hsmall.trans ((min_le_right _ _).trans (min_le_right _ _)))
    g0 R hR sphere transport hmem hf himm
  intro z u v
  dsimp only
  intro hgram
  have hphysical := hplane z u v ((normalizedNeck_gram_pos_iff N _ _ _).mp hgram)
  have hnormalized := normalizedNeck_sectional_lower N
    (div_nonneg hk.le (sq_nonneg h)) hcenter hphysical
  have hquot : (k / h ^ 2) / ((2 * K) / h ^ 2) = k / (2 * K) := by
    field_simp
  rwa [hquot] at hnormalized

end PoincareConjecture.M44
