import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusClass
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.PullbackGeodesics

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Topology Manifold ContDiff ENNReal NNReal Bundle

namespace PoincareConjecture

variable {n m : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64_observation_edist_bound [CompactSpace M]
    (g : RiemannianMetric n M) (e : M → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) :
    ∃ C : ℝ≥0, ∀ x y, edist (e x) (e y) ≤ C * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨B, hB, hbound⟩ := M60.exists_uniform_mfderiv_bound g e he
  let C : ℝ≥0 := ⟨B + 1, by positivity⟩
  refine ⟨C, fun x y => ?_⟩
  have hnorm (q : M) (v : TangentSpace (𝓡 n) q) :
      (RiemannianMetric.euclideanMetric m).tangentNorm (e q)
        (mfderiv (𝓡 n) (𝓡 m) e q v) ≤ (B + 1) * g.tangentNorm q v := by
    rw [RiemannianMetric.euclideanMetric_tangentNorm,
      ← norm_tangentSpace_vectorSpace (x := e q)]
    change ‖mfderiv (𝓡 n) (𝓡 m) e q v‖ ≤ (B + 1) * ‖v‖
    exact ((mfderiv (𝓡 n) (𝓡 m) e q).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right ((hbound q).trans (by linarith)) (norm_nonneg v))
  have hd := RiemannianMetric.edist_le_mul_of_tangentNorm_mfderiv_le
    g (RiemannianMetric.euclideanMetric m) he (by positivity : 0 < B + 1) hnorm x y
  rw [ENNReal.coe_nnreal_eq]
  change edist (e x) (e y) ≤ ENNReal.ofReal (B + 1) * g.edist x y
  simpa only [RiemannianMetric.euclideanMetric_edist] using hd

theorem m64Annulus_observed_lipschitzOn [CompactSpace M]
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (e : M → EuclideanSpace ℝ (Fin m)) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) :
    ∃ K : ℝ≥0, LipschitzOnWith K (e ∘ A.map) m64AnnulusDomain := by
  obtain ⟨C, hC⟩ := m64_observation_edist_bound g e he
  let L : ℝ≥0 := ⟨A.lipschitz_constant, A.lipschitz_nonnegative⟩
  refine ⟨C * L, fun x hx y hy => ?_⟩
  calc
    edist (e (A.map x)) (e (A.map y)) ≤ C * g.edist (A.map x) (A.map y) := hC _ _
    _ ≤ C * (ENNReal.ofReal A.lipschitz_constant * ENNReal.ofReal ‖x - y‖) := by
      gcongr
      exact A.lipschitz_on_domain ⟨x, hx⟩ ⟨y, hy⟩
    _ = (C * L : ℝ≥0) * edist x y := by
      rw [ENNReal.coe_mul, ENNReal.coe_nnreal_eq L, edist_dist, dist_eq_norm]
      exact (mul_assoc _ _ _).symm

end PoincareConjecture
