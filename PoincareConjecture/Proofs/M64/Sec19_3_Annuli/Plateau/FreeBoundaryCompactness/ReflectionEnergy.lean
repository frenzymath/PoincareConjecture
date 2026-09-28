import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.AnnulusReflection
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusReduction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem areaGram_diagonal_comp_annulusFlip (g : RiemannianMetric n M)
    (f : LoopPlane → M) (p : LoopPlane) (i : Fin 2) :
    m60AreaGram g (fun w => f (m64AnnulusFlip w)) p i i =
      m60AreaGram g f (m64AnnulusFlip p) i i := by
  have hd := mfderiv_comp_m64AnnulusFlip (n := n) f p
  have h0 : mfderiv (𝓡 2) (𝓡 n) (fun w => f (m64AnnulusFlip w)) p
      (EuclideanSpace.basisFun (Fin 2) ℝ 0) =
      mfderiv (𝓡 2) (𝓡 n) f (m64AnnulusFlip p)
        (EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
    erw [hd]
    change mfderiv (𝓡 2) (𝓡 n) f (m64AnnulusFlip p)
      (m60PlaneReflection (EuclideanSpace.basisFun (Fin 2) ℝ 0)) = _
    rw [m60PlaneReflection_basis_zero]
  have h1 : mfderiv (𝓡 2) (𝓡 n) (fun w => f (m64AnnulusFlip w)) p
      (EuclideanSpace.basisFun (Fin 2) ℝ 1) =
      -mfderiv (𝓡 2) (𝓡 n) f (m64AnnulusFlip p)
        (EuclideanSpace.basisFun (Fin 2) ℝ 1) := by
    erw [hd]
    change mfderiv (𝓡 2) (𝓡 n) f (m64AnnulusFlip p)
      (m60PlaneReflection (EuclideanSpace.basisFun (Fin 2) ℝ 1)) = _
    rw [m60PlaneReflection_basis_one, map_neg]
  fin_cases i
  · exact congrArg (fun v => g.inner (f (m64AnnulusFlip p)) v v) h0
  · change m60AreaGram g (fun w => f (m64AnnulusFlip w)) p 1 1 =
      m60AreaGram g f (m64AnnulusFlip p) 1 1
    have h := congrArg (fun v => g.inner (f (m64AnnulusFlip p)) v v) h1
    simp only [map_neg, neg_apply, neg_neg] at h
    exact h

theorem annulus_reverse_weightedGram_integrable
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1) (r : ℝ)
    (hE : IntegrableOn (fun p => (r * m60AreaGram g A.map p 0 0 +
      r⁻¹ * m60AreaGram g A.map p 1 1) / 2) m64AnnulusDomain) :
    IntegrableOn (fun p => (r * m60AreaGram g (m64Annulus_reverse A).map p 0 0 +
      r⁻¹ * m60AreaGram g (m64Annulus_reverse A).map p 1 1) / 2) m64AnnulusDomain := by
  have hi := (m64AnnulusFlip_measurePreserving.integrableOn_comp_preimage
    m64AnnulusFlip.toMeasurableEquiv.measurableEmbedding).mpr hE
  rw [m64AnnulusFlip_preimage_domain] at hi
  change IntegrableOn (fun p =>
    (r * m60AreaGram g (fun w => A.map (m64AnnulusFlip w)) p 0 0 +
      r⁻¹ * m60AreaGram g (fun w => A.map (m64AnnulusFlip w)) p 1 1) / 2)
    m64AnnulusDomain
  simp_rw [areaGram_diagonal_comp_annulusFlip]
  exact hi

theorem annulus_reverse_weightedGramEnergy
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1) (r : ℝ) :
    m64ClassicalWeightedGramEnergy g (m64Annulus_reverse A) r =
      m64ClassicalWeightedGramEnergy g A r := by
  unfold m64ClassicalWeightedGramEnergy
  simp_rw [show (m64Annulus_reverse A).map = fun p => A.map (m64AnnulusFlip p) from rfl,
    areaGram_diagonal_comp_annulusFlip]
  have h := m64AnnulusFlip_measurePreserving.setIntegral_preimage_emb
    m64AnnulusFlip.toMeasurableEquiv.measurableEmbedding
    (fun p => (r * m60AreaGram g A.map p 0 0 + r⁻¹ * m60AreaGram g A.map p 1 1) / 2)
    m64AnnulusDomain
  rwa [m64AnnulusFlip_preimage_domain] at h

theorem annulus_reverse_contMDiffOn_strip
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M} (A : M64Annulus g c0 c1)
    (hA : ContMDiffOn (𝓡 2) (𝓡 n) 1 A.map {p | p 1 ∈ Ioo (0 : ℝ) 1}) :
    ContMDiffOn (𝓡 2) (𝓡 n) 1 (m64Annulus_reverse A).map
      {p | p 1 ∈ Ioo (0 : ℝ) 1} := by
  have hflip : ContDiff ℝ 1 m64AnnulusFlip :=
    m60PlaneReflection.toContinuousLinearEquiv.contDiff.add contDiff_const
  exact hA.comp (contMDiff_iff_contDiff.mpr hflip).contMDiffOn (fun p hp => by
    change 0 < m64AnnulusFlip p 1 ∧ m64AnnulusFlip p 1 < 1
    rw [m64AnnulusFlip_coord_one]
    constructor <;> linarith [hp.1, hp.2])

end PoincareConjecture.M64
