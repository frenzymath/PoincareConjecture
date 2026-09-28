import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.AnnulusReflectionGeometry
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64AreaDensity_comp_annulusFlip (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) :
    m60AreaDensity g (fun w => f (m64AnnulusFlip w)) z =
      m60AreaDensity g f (m64AnnulusFlip z) := by
  have hd := mfderiv_comp_m64AnnulusFlip (n := n) f z
  have h0 : mfderiv (𝓡 2) (𝓡 n) (fun w => f (m64AnnulusFlip w)) z
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      mfderiv (𝓡 2) (𝓡 n) f (m64AnnulusFlip z)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
    erw [hd]
    change mfderiv (𝓡 2) (𝓡 n) f (m64AnnulusFlip z)
      (m60PlaneReflection (EuclideanSpace.basisFun (Fin 2) ℝ 0)) = _
    rw [m60PlaneReflection_basis_zero]
  have h1 : mfderiv (𝓡 2) (𝓡 n) (fun w => f (m64AnnulusFlip w)) z
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      -mfderiv (𝓡 2) (𝓡 n) f (m64AnnulusFlip z)
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by
    erw [hd]
    change mfderiv (𝓡 2) (𝓡 n) f (m64AnnulusFlip z)
      (m60PlaneReflection (EuclideanSpace.basisFun (Fin 2) ℝ 1)) = _
    rw [m60PlaneReflection_basis_one, map_neg]
  simp only [m60AreaDensity, Matrix.det_fin_two, m60AreaGram, h0, h1, map_neg,
    neg_apply, neg_neg, neg_mul_neg]

theorem m64AreaDensity_integrableOn_comp_annulusFlip (g : RiemannianMetric n M)
    (f : LoopPlane → M) (hf : IntegrableOn (m60AreaDensity g f) m64AnnulusDomain volume) :
    IntegrableOn (m60AreaDensity g (fun w => f (m64AnnulusFlip w)))
      m64AnnulusDomain volume := by
  have hi := (m64AnnulusFlip_measurePreserving.integrableOn_comp_preimage
    m64AnnulusFlip.toMeasurableEquiv.measurableEmbedding).mpr hf
  rw [m64AnnulusFlip_preimage_domain] at hi
  change IntegrableOn (fun z => m60AreaDensity g (fun w => f (m64AnnulusFlip w)) z)
    m64AnnulusDomain volume
  simp_rw [m64AreaDensity_comp_annulusFlip]
  exact hi

theorem m64AnnulusArea_comp_annulusFlip (g : RiemannianMetric n M)
    (f : LoopPlane → M) :
    m64AnnulusArea g (fun w => f (m64AnnulusFlip w)) = m64AnnulusArea g f := by
  unfold m64AnnulusArea
  simp_rw [m64AreaDensity_comp_annulusFlip]
  have h := m64AnnulusFlip_measurePreserving.setIntegral_preimage_emb
    m64AnnulusFlip.toMeasurableEquiv.measurableEmbedding (m60AreaDensity g f) m64AnnulusDomain
  rwa [m64AnnulusFlip_preimage_domain] at h

noncomputable def m64Annulus_reverse {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) : M64Annulus g c1 c0 where
  map := fun z => A.map (m64AnnulusFlip z)
  continuous_on_domain := A.continuous_on_domain.comp m64AnnulusFlip.continuous.continuousOn
    (fun z hz => (m64AnnulusFlip_mem_domain z).mpr hz)
  periodic := by
    intro x s
    simp only [m64AnnulusFlip_annulusPoint]
    exact A.periodic x (1 - s)
  lower_boundary := by
    intro x
    simp only [m64AnnulusFlip_annulusPoint, sub_zero]
    exact A.upper_boundary x
  upper_boundary := by
    intro x
    simp only [m64AnnulusFlip_annulusPoint, sub_self]
    exact A.lower_boundary x
  lipschitz_constant := A.lipschitz_constant
  lipschitz_nonnegative := A.lipschitz_nonnegative
  lipschitz_on_domain := by
    intro x y
    have h := A.lipschitz_on_domain
      ⟨m64AnnulusFlip x, (m64AnnulusFlip_mem_domain x).mpr x.property⟩
      ⟨m64AnnulusFlip y, (m64AnnulusFlip_mem_domain y).mpr y.property⟩
    have hn : ‖m64AnnulusFlip x - m64AnnulusFlip y‖ = ‖(x : LoopPlane) - y‖ := by
      simpa only [dist_eq_norm] using m64AnnulusFlip_isometry.dist_eq x y
    simpa only [hn] using h
  ae_manifold_differentiable := by
    filter_upwards [m64AnnulusFlip_measurePreserving.quasiMeasurePreserving.ae
      A.ae_manifold_differentiable] with z hz
    intro hzdom
    exact (hz ((m64AnnulusFlip_mem_domain z).mpr hzdom)).comp z
      (m64AnnulusFlip_hasFDerivAt z).hasMFDerivAt.mdifferentiableAt
  area_integrable := m64AreaDensity_integrableOn_comp_annulusFlip g A.map A.area_integrable

theorem m64Annulus_reverse_area {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A : M64Annulus g c0 c1) : (m64Annulus_reverse A).area = A.area :=
  m64AnnulusArea_comp_annulusFlip g A.map

end PoincareConjecture
