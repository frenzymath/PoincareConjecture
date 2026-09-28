import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_AngularProjection
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_10_SphereNullhomotopy












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ContinuousMap

namespace PoincareConjecture.M44

open M36

local notation "E" => EuclideanSpace ℝ (Fin 3)




def neckTransportAngularMap
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {X : Type*} [TopologicalSpace X] (f : C(X, M))
    (hmem : ∀ x, f x ∈ N.carrier) : C(X, UnitTwoSphere) :=
  ⟨fun x => (N.coordinate_inverse (f x)).1, continuous_iff_continuousAt.mpr
    (fun x => (neck_inverse_contMDiffAt N (hmem x)).continuousAt.fst.comp
      f.continuous.continuousAt)⟩





theorem exists_sphere_neck_obstruction_cutoff {k : ℝ} (hk : 0 < k) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      ∀ (g0 : StandardInitialMetric) (R : ℝ), 0 < R →
      ∀ (sphere : C(UnitTwoSphere, g0.metric.ball 0 R))
        (transport : C(g0.metric.ball 0 R, M)),
      (∀ x, transport x ∈ N.carrier) →
      ContMDiff (𝓡 2) (𝓡 3) ∞ (transport.comp sphere) →
      (∀ z, Function.Injective (mfderiv (𝓡 2) (𝓡 3) (transport.comp sphere) z)) →
      (∀ z, ∀ u v : TangentSpace (𝓡 2) z,
        let f := transport.comp sphere
        let Df := mfderiv (𝓡 2) (𝓡 3) f z
        let h := normalizedNeckMetric N
        0 < h.inner (f z) (Df u) (Df u) * h.inner (f z) (Df v) (Df v) -
          (h.inner (f z) (Df u) (Df v)) ^ 2 →
          k < (normalizedNeckConnection N).sectionalCurvature (f z) (Df u) (Df v)) →
      False := by
  obtain ⟨epsilon0, hepsilon0, hcut⟩ := exists_neck_sphere_angular_cutoff hk
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro M _ _ _ _ g N hsmall g0 R hR sphere transport hmem hf himm hlower
  have hlocal := hcut N hsmall (transport.comp sphere) hf
    (fun z => hmem (sphere z)) himm hlower
  apply sphere_factor_through_standard_ball_not_localHomeomorph g0 hR sphere
    (neckTransportAngularMap N transport hmem)
  simpa only [neckTransportAngularMap, neckSphereAngularMap,
    ContinuousMap.coe_mk, ContinuousMap.coe_comp, Function.comp_def] using hlocal




theorem normalizedNeck_gram_pos_iff
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g) (x : M)
    (u v : TangentSpace (𝓡 3) x) :
    (0 < (normalizedNeckMetric N).inner x u u * (normalizedNeckMetric N).inner x v v -
      ((normalizedNeckMetric N).inner x u v) ^ 2) ↔
    0 < g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 := by
  simp only [normalizedNeckMetric, m01RescaledMetric_inner]
  rw [show (N.connection.scalarCurvature N.center * g.inner x u u) *
      (N.connection.scalarCurvature N.center * g.inner x v v) -
      (N.connection.scalarCurvature N.center * g.inner x u v) ^ 2 =
      (N.connection.scalarCurvature N.center) ^ 2 *
        (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) by ring]
  exact mul_pos_iff_of_pos_left (sq_pos_of_pos N.scalar_center_pos)




theorem normalizedNeck_sectional_lower
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (N : EpsilonNeck g)
    {k Q : ℝ} (hk : 0 ≤ k) (hQ : N.connection.scalarCurvature N.center ≤ Q)
    {x : M} {u v : TangentSpace (𝓡 3) x}
    (hlower : k < N.connection.sectionalCurvature x u v) :
    k / Q < (normalizedNeckConnection N).sectionalCurvature x u v := by
  rw [normalizedNeck_sectional]
  exact (div_le_div_of_nonneg_left hk N.scalar_center_pos hQ).trans_lt
    ((div_lt_div_iff_of_pos_right N.scalar_center_pos).mpr hlower)




theorem exists_physical_sphere_neck_obstruction_cutoff {k Q : ℝ}
    (hk : 0 < k) (hQ : 0 < Q) :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧
      ∀ {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
        [IsManifold (𝓡 3) ∞ M] [T2Space M]
        {g : RiemannianMetric 3 M} (N : EpsilonNeck g), N.epsilon ≤ epsilon0 →
      N.connection.scalarCurvature N.center ≤ Q →
      ∀ (g0 : StandardInitialMetric) (R : ℝ), 0 < R →
      ∀ (sphere : C(UnitTwoSphere, g0.metric.ball 0 R))
        (transport : C(g0.metric.ball 0 R, M)),
      (∀ x, transport x ∈ N.carrier) →
      ContMDiff (𝓡 2) (𝓡 3) ∞ (transport.comp sphere) →
      (∀ z, Function.Injective (mfderiv (𝓡 2) (𝓡 3) (transport.comp sphere) z)) →
      (∀ z, ∀ u v : TangentSpace (𝓡 2) z,
        let f := transport.comp sphere
        let Df := mfderiv (𝓡 2) (𝓡 3) f z
        0 < g.inner (f z) (Df u) (Df u) * g.inner (f z) (Df v) (Df v) -
          (g.inner (f z) (Df u) (Df v)) ^ 2 →
          k < N.connection.sectionalCurvature (f z) (Df u) (Df v)) →
      False := by
  obtain ⟨epsilon0, hepsilon0, hcut⟩ := exists_sphere_neck_obstruction_cutoff (div_pos hk hQ)
  refine ⟨epsilon0, hepsilon0, ?_⟩
  intro M _ _ _ _ g N hsmall hcenter g0 R hR sphere transport hmem hf himm hlower
  apply hcut N hsmall g0 R hR sphere transport hmem hf himm
  intro z u v
  dsimp only
  intro hgram
  exact normalizedNeck_sectional_lower N hk.le hcenter
    (hlower z u v ((normalizedNeck_gram_pos_iff N _ _ _).mp hgram))

end PoincareConjecture.M44
