import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Exhaustion.TensorNormContinuity
import PoincareConjecture.Proofs.M35.Uniqueness.Heat.Bernstein.Energies









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}
local notation "V" => EuclideanSpace ℝ (Fin n)
local notation "e" => EuclideanSpace.basisFun (Fin n) ℝ

theorem raw_field_connection_continuousOn {J I : Set ℝ} (F : RicciFlow n V J)
    (hIJ : I ⊆ J) {E : Set V} (X : ℝ → V → V)
    (hXs : ∀ t, ContDiff ℝ ∞ (X t))
    (hX : ContinuousOn (Function.uncurry X) (I ×ˢ E))
    (hDX : ContinuousOn (fun p : ℝ × V => fderiv ℝ (X p.1) p.2) (I ×ˢ E)) (u : V) :
    ContinuousOn (fun p : ℝ × V => (F.connection p.1).connection (X p.1) p.2 u)
      (I ×ˢ E) := by
  have hΓ := (rawConnectionCoefficient_family_contDiffOn F).continuousOn.mono
    (prod_mono hIJ (subset_univ E))
  have hc := (hDX.clm_apply (continuousOn_const (c := u))).add
    ((hΓ.clm_apply (continuousOn_const (c := u))).clm_apply hX)
  apply hc.congr
  intro p _hp
  exact raw_connection_expansion (F.connection p.1) ((hXs p.1).differentiable (by simp) p.2) u

theorem raw_covector_gradient_normSq_continuousOn {J I : Set ℝ} (F : RicciFlow n V J)
    (hIJ : I ⊆ J) {E : Set V} (X : ℝ → V → V)
    (hXs : ∀ t, ContDiff ℝ ∞ (X t))
    (hX : ContinuousOn (Function.uncurry X) (I ×ˢ E))
    (hDX : ContinuousOn (fun p : ℝ × V => fderiv ℝ (X p.1) p.2) (I ×ˢ E)) :
    ContinuousOn (fun p : ℝ × V => ((F.metric p.1).tensorNorm
      ((F.connection p.1).covariantTensorDerivative
        (killingCovector (F.metric p.1) (X p.1))) p.2) ^ 2) (I ×ˢ E) := by
  apply raw_tensorNorm_sq_continuousOn F hIJ
    (fun t => (F.connection t).covariantTensorDerivative (killingCovector (F.metric t) (X t)))
    (fun t => M04.isSmoothCovariantTensor_covariantTensorDerivative _
      (isSmoothCovariantTensor_killingCovector _ _ (hXs t)))
  intro a
  simp only [killingCovector_derivative _ _ (hXs _)]
  have hg := (rawMetricBilin_family_contDiffOn F).continuousOn.mono
    (prod_mono hIJ (subset_univ E))
  exact (hg.clm_apply (raw_field_connection_continuousOn F hIJ X hXs hX hDX (e (a 0))
    )).clm_apply (continuousOn_const (c := e (a 1)))

theorem raw_killing_defect_normSq_continuousOn {J I : Set ℝ} (F : RicciFlow n V J)
    (hIJ : I ⊆ J) {E : Set V} (X : ℝ → V → V)
    (hXs : ∀ t, ContDiff ℝ ∞ (X t))
    (hX : ContinuousOn (Function.uncurry X) (I ×ˢ E))
    (hDX : ContinuousOn (fun p : ℝ × V => fderiv ℝ (X p.1) p.2) (I ×ˢ E)) :
    ContinuousOn (fun p : ℝ × V => ((F.metric p.1).tensorNorm
      (killingDefectTensor (F.connection p.1) (X p.1)) p.2) ^ 2) (I ×ˢ E) := by
  apply raw_tensorNorm_sq_continuousOn F hIJ
    (fun t => killingDefectTensor (F.connection t) (X t))
    (fun t => isSmoothCovariantTensor_killingDefectTensor _ _ (hXs t))
  intro a
  simp only [killingDefectTensor, DeTurckNative.metricLieDerivative_apply]
  have hg := (rawMetricBilin_family_contDiffOn F).continuousOn.mono
    (prod_mono hIJ (subset_univ E))
  have hc (i : Fin 2) := raw_field_connection_continuousOn F hIJ X hXs hX hDX (e (a i))
  exact ((hg.clm_apply (hc 0)).clm_apply (continuousOn_const (c := e (a 1)))).add
    ((hg.clm_apply (continuousOn_const (c := e (a 0)))).clm_apply (hc 1))

theorem raw_vectorHeatJetEnergy_zero_continuousOn {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {I : Set ℝ} (hI : I ⊆ Ico 0 G.lifetime)
    {E : Set StandardCapSpace} (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hX : ContinuousOn (Function.uncurry X) (I ×ˢ E)) :
    ContinuousOn (Function.uncurry (vectorHeatJetEnergy G X 0)) (I ×ˢ E) := by
  have hg := (rawMetricBilin_family_contDiffOn G.flow).continuousOn.mono
    (prod_mono hI (subset_univ E))
  apply ((hg.clm_apply hX).clm_apply hX).congr
  intro p _hp
  exact vectorHeatJetEnergy_zero G X p.1 p.2

theorem raw_vectorHeatJetEnergy_one_continuousOn {g₀ : StandardInitialMetric}
    (G : PartialStandardCapFlow g₀) {I : Set ℝ} (hI : I ⊆ Ico 0 G.lifetime)
    {E : Set StandardCapSpace} (X : ℝ → StandardCapSpace → StandardCapSpace)
    (hXs : ∀ t, ContDiff ℝ ∞ (X t))
    (hX : ContinuousOn (Function.uncurry X) (I ×ˢ E))
    (hDX : ContinuousOn (fun p : ℝ × StandardCapSpace => fderiv ℝ (X p.1) p.2) (I ×ˢ E)) :
    ContinuousOn (Function.uncurry (vectorHeatJetEnergy G X 1)) (I ×ˢ E) :=
  raw_covector_gradient_normSq_continuousOn G.flow hI X hXs hX hDX

end PoincareConjecture.M35.Uniqueness.Heat
