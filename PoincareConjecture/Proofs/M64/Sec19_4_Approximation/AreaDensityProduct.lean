import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy
import PoincareConjecture.Proofs.M58.Mathlib.TwoVectorArea
import PoincareConjecture.Definitions.M64Annulus

set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem m60AreaDensity_le_tangentNorm_product
    (g : RiemannianMetric n M) (f : LoopPlane → M) (z : LoopPlane) :
    m60AreaDensity g f z ≤
      g.tangentNorm (f z)
          (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) *
        g.tangentNorm (f z)
          (mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold m60AreaDensity
  rw [Matrix.det_fin_two, m60AreaGram_symm g f z 1 0]
  let u := mfderiv (𝓡 2) (𝓡 n) f z
    (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  let v := mfderiv (𝓡 2) (𝓡 n) f z
    (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  dsimp only [m60AreaGram, RiemannianMetric.tangentNorm]
  change Real.sqrt (max 0
      (g.inner (f z) u u * g.inner (f z) v v -
        g.inner (f z) u v * g.inner (f z) u v)) ≤
    Real.sqrt (g.inner (f z) u u) * Real.sqrt (g.inner (f z) v v)
  have huu : 0 ≤ g.inner (f z) u u :=
    (g.toRiemannianMetric.toCore (f z)).re_inner_nonneg _
  have hvv : 0 ≤ g.inner (f z) v v :=
    (g.toRiemannianMetric.toCore (f z)).re_inner_nonneg _
  have hdet : g.inner (f z) u u * g.inner (f z) v v -
      g.inner (f z) u v * g.inner (f z) u v ≤
      g.inner (f z) u u * g.inner (f z) v v := by
    exact sub_le_self _ (mul_self_nonneg _)
  apply Real.sqrt_le_iff.mpr
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
  rw [max_le_iff]
  refine ⟨sq_nonneg _, ?_⟩
  rw [mul_pow, Real.sq_sqrt huu, Real.sq_sqrt hvv]
  exact hdet

theorem m64AnnulusIntegral_le_of_ae_density_bound
    {g : RiemannianMetric n M} {f : LoopPlane → M}
    {K : ℝ}
    (hfinite : volume m64AnnulusDomain ≠ (⊤ : ENNReal))
    (hInt : IntegrableOn (m60AreaDensity g f) m64AnnulusDomain volume)
    (hbound : ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      m60AreaDensity g f z ≤ K) :
    (∫ z in m64AnnulusDomain, m60AreaDensity g f z) ≤
      K * volume.real m64AnnulusDomain := by
  have hconst : IntegrableOn (fun _ : LoopPlane => K)
      m64AnnulusDomain volume := integrableOn_const hfinite
  calc
    (∫ z in m64AnnulusDomain, m60AreaDensity g f z) ≤
        ∫ _ : LoopPlane in m64AnnulusDomain, K :=
      integral_mono_ae hInt hconst hbound
    _ = K * volume.real m64AnnulusDomain := by
      simp [mul_comm]

end PoincareConjecture
