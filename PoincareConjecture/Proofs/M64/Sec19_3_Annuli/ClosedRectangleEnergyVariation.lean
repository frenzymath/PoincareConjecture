import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingMapVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.MovingAnnulusCurrent
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.DomainBoundary
import PoincareConjecture.Proofs.M64.Sec19_4_Approximation.MetricLipschitzBridge
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

private theorem annulusInterior_subset : m64AnnulusInterior ⊆ m64AnnulusDomain := by
  intro p hp
  simp only [m64AnnulusInterior, mem_preimage, Set.mem_pi, mem_univ, mem_Ioo] at hp
  have h0 := hp 0 trivial
  have h1 := hp 1 trivial
  exact ⟨h0.1.le, h0.2.le, h1.1.le, h1.2.le⟩

theorem m64AnnulusDomain_uniqueDiffOn : UniqueDiffOn ℝ m64AnnulusDomain := by
  apply uniqueDiffOn_convex m64AnnulusDomain_convex
  refine ⟨annulusPoint (curvePeriod / 2) (1 / 2), ?_⟩
  apply (interior_maximal annulusInterior_subset isOpen_m64AnnulusInterior)
  simp only [m64AnnulusInterior, mem_preimage, Set.mem_pi, mem_univ, mem_Ioo]
  intro i _
  fin_cases i <;> norm_num [annulusPoint, curvePeriod, Real.pi_pos]

theorem m64AnnulusIntegral_differentiableAt_of_contDiffOn
    {E : ℝ × LoopPlane → ℝ} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hE : ContDiffOn ℝ ∞ E (Ioo (-epsilon) epsilon ×ˢ m64AnnulusDomain)) :
    DifferentiableAt ℝ (fun s => ∫ p in m64AnnulusDomain, E (s, p)) 0 := by
  let Q := Ioo (-epsilon) epsilon ×ˢ m64AnnulusDomain
  have hQ : UniqueDiffOn ℝ Q :=
    isOpen_Ioo.uniqueDiffOn.prod m64AnnulusDomain_uniqueDiffOn
  apply (m64AnnulusIntegral_hasDerivAt_of_local_continuous_derivative
    (F := fun s p => E (s, p))
    (F' := fun s p => fderivWithin ℝ E Q (s, p) (1, 0)) hepsilon ?_ ?_ ?_).2.differentiableAt
  · intro s hs
    exact hE.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun p hp => ⟨hs, hp⟩)
  · exact ((hE.fderivWithin hQ (m := ∞) (by simp)).clm_apply
      (contDiffOn_const (c := (1, (0 : LoopPlane))))).continuousOn
  · intro s hs p hp
    exact ((hE.differentiableOn (by simp)) (s, p) ⟨hs, hp⟩).hasFDerivWithinAt
      |>.comp_hasDerivAt (l := E) (f := fun s : ℝ => (s, p)) s
        ((hasDerivAt_id s).prodMk (hasDerivAt_const s p))
        (by filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht; exact ⟨ht, hp⟩)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

private theorem within_energy_contDiffOn
    (g : RiemannianMetric n M) (w : Fin 2 → ℝ)
    {v : ℝ × LoopPlane → M} {Q : Set (ℝ × LoopPlane)}
    (hQ : UniqueDiffOn ℝ Q)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v Q) :
    ContDiffOn ℝ ∞ (fun q => (1 / 2 : ℝ) * ∑ i : Fin 2,
      w i * g.inner (v q)
        (mfderivWithin 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v Q q
          (0, EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderivWithin 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v Q q
          (0, EuclideanSpace.basisFun (Fin 2) ℝ i))) Q := by
  intro q hq
  let u (i : Fin 2) (w : ℝ × LoopPlane) :=
    mfderivWithin 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v Q w
      (0, EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hpush (i : Fin 2) :
      ContMDiffWithinAt 𝓘(ℝ, ℝ × LoopPlane) ((𝓡 n).prod (𝓡 n)) ∞
        (fun w => (⟨v w, u i w⟩ : TangentBundle (𝓡 n) M)) Q q := by
    have hd : ContMDiffWithinAt 𝓘(ℝ, ℝ × LoopPlane)
        ((𝓘(ℝ, ℝ × LoopPlane)).prod 𝓘(ℝ, ℝ × LoopPlane)) ∞
        (fun w : ℝ × LoopPlane =>
          (⟨w, (0, EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ :
            TangentBundle 𝓘(ℝ, ℝ × LoopPlane) (ℝ × LoopPlane))) Q q := by
      rw [contMDiffWithinAt_totalSpace]
      refine ⟨contMDiffWithinAt_id, ?_⟩
      simpa using contMDiffWithinAt_const
        (c := ((0 : ℝ), EuclideanSpace.basisFun (Fin 2) ℝ i))
    have hderiv := (hv q hq).mfderivWithin_const (m := ∞) (by simp) hq hQ.uniqueMDiffOn
    exact hderiv.clm_apply_of_inCoordinates hd (hv q hq)
  have hmetric := g.contMDiff.contMDiffAt.comp_contMDiffWithinAt q (hv q hq)
  have hscalar (i : Fin 2) : ContDiffWithinAt ℝ ∞
      (fun w => g.inner (v w) (u i w) (u i w)) Q q := by
    have h := hmetric.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
      (hpush i) (hpush i)
    exact contMDiffWithinAt_iff_contDiffWithinAt.mp
      (Bundle.contMDiffWithinAt_totalSpace.mp h).2
  exact contDiffWithinAt_const.mul
    (ContDiffWithinAt.sum fun i _ => contDiffWithinAt_const.mul (hscalar i))

theorem m64AnnulusGramEnergy_differentiableAt_of_closed_smooth_variation
    (g : RiemannianMetric n M) (w : Fin 2 → ℝ) {v : ℝ × LoopPlane → M}
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ m64AnnulusDomain)) :
    DifferentiableAt ℝ (fun s => ∫ p in m64AnnulusDomain,
      (1 / 2 : ℝ) * ∑ i : Fin 2, w i * m60AreaGram g (fun z => v (s, z)) p i i) 0 := by
  let Q := Ioo (-epsilon) epsilon ×ˢ m64AnnulusDomain
  let E := fun q : ℝ × LoopPlane => (1 / 2 : ℝ) * ∑ i : Fin 2,
    w i * g.inner (v q)
      (mfderivWithin 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v Q q
        (0, EuclideanSpace.basisFun (Fin 2) ℝ i))
      (mfderivWithin 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) v Q q
        (0, EuclideanSpace.basisFun (Fin 2) ℝ i))
  have hQ : UniqueDiffOn ℝ Q :=
    isOpen_Ioo.uniqueDiffOn.prod m64AnnulusDomain_uniqueDiffOn
  have hE : ContDiffOn ℝ ∞ E Q := within_energy_contDiffOn g w hQ hv
  have hdiff := m64AnnulusIntegral_differentiableAt_of_contDiffOn hepsilon hE
  apply hdiff.congr_of_eventuallyEq
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
  apply integral_congr_ae
  have hnull : ∀ᵐ p ∂volume, p ∉ m64AnnulusDomain \ interior m64AnnulusDomain :=
    ae_iff.mpr (by simpa only [not_not, Set.ofPred_mem_eq] using m64AnnulusDomain_boundary_null)
  filter_upwards [ae_restrict_mem m64AnnulusDomain_measurableSet,
    ae_restrict_of_ae hnull] with p hp hint
  have hpint : p ∈ interior m64AnnulusDomain := by
    by_contra h
    exact hint ⟨hp, h⟩
  have hnhds : Q ∈ 𝓝 (s, p) :=
    prod_mem_nhds (isOpen_Ioo.mem_nhds hs) (mem_interior_iff_mem_nhds.mp hpint)
  have hmd := (hv.contMDiffAt hnhds).mdifferentiableAt (by simp)
  simp only [E, mfderivWithin_of_mem_nhds hnhds,
    m60AreaGram, m64MovingAnnulus_spatial_differential hmd]

theorem m64AnnulusEnergy_differentiableAt_of_closed_smooth_variation
    (g : RiemannianMetric n M) {v : ℝ × LoopPlane → M}
    {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ m64AnnulusDomain)) :
    DifferentiableAt ℝ (fun s => ∫ p in m64AnnulusDomain,
      m60EnergyDensity g (fun z => v (s, z)) p) 0 := by
  simpa only [m60EnergyDensity, Matrix.trace, Matrix.diag, one_mul] using
    m64AnnulusGramEnergy_differentiableAt_of_closed_smooth_variation g
      (fun _ => 1) hepsilon hv

end PoincareConjecture
