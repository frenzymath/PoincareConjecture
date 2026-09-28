import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FluxRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m65PlaneFluxVector_divergence (g : RiemannianMetric n M)
    (u : ℝ → LoopPlane → M) {t : ℝ} {z : LoopPlane}
    (hu : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ (Function.uncurry u) (t, z)) :
    (∑ i : Fin 2, deriv (fun r : ℝ => m65PlaneVariationFlux g u t i
      (z + r • EuclideanSpace.basisFun (Fin 2) ℝ i)) 0) =
      ∑ i : Fin 2, inner ℝ
        (fderiv ℝ (m65PlaneFluxVector g u t) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i) := by
  let X := m65PlaneFluxVector g u t
  have hX : DifferentiableAt ℝ X z :=
    (m65PlaneFluxVector_contDiffAt g u hu).differentiableAt (by simp)
  apply Finset.sum_congr rfl
  intro i _
  let v := EuclideanSpace.basisFun (Fin 2) ℝ i
  have hline : HasDerivAt (fun r : ℝ => z + r • v) v 0 := by
    simpa +instances only [zero_add, one_smul] using!
      (hasDerivAt_const (0 : ℝ) z).add ((hasDerivAt_id (0 : ℝ)).smul_const v)
  have hX' : HasDerivAt (fun r : ℝ => X (z + r • v)) (fderiv ℝ X z v) 0 := by
    have hd : HasFDerivAt X (fderiv ℝ X z) (z + (0 : ℝ) • v) := by
      simpa only [zero_smul, add_zero] using hX.hasFDerivAt
    simpa +instances only [Function.comp_def] using! hd.comp_hasDerivAt 0 hline
  have hd := (hX'.inner ℝ (hasDerivAt_const (0 : ℝ) v)).deriv
  have hcoord (w : LoopPlane) : inner ℝ (X w) v = m65PlaneVariationFlux g u t i w := by
    rw [EuclideanSpace.inner_basisFun_real]
    fin_cases i <;> rfl
  simpa only [hcoord, inner_zero_right, zero_add, X, v] using hd

theorem m65Integral_motionDensity_eq_boundary
    {a b : ℝ} (F : RicciFlow n M (Icc a b)) (u : ℝ → LoopPlane → M)
    {U : Set (ℝ × LoopPlane)} (hU : IsOpen U)
    (hu : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ (Function.uncurry u) U)
    {t : ℝ} (hdisk : ∀ z ∈ loopDiskSet, (t, z) ∈ U)
    (hconf : ∀ᵐ z ∂volume.restrict loopDiskSet,
      ∃ c : ℝ, m60AreaGram (F.metric t) (u t) z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (htension : ∀ᵐ z ∂volume.restrict loopDiskSet,
      m65PlaneTension (F.connection t) (u t) z = 0) :
    IntegrableOn (m65PlaneMotionDensity F u t) loopDiskSet volume ∧
      (∫ z in loopDiskSet, m65PlaneMotionDensity F u t z) =
        ∫ θ in (-Real.pi)..Real.pi,
          (F.metric t).inner (u t (Proofs.M58.angularPoint θ))
            (curveVelocity (fun s => u s (Proofs.M58.angularPoint θ)) t)
            (mfderiv (𝓡 2) (𝓡 n) (u t) (Proofs.M58.angularPoint θ)
              (Proofs.M58.angularPoint θ)) := by
  let X := m65PlaneFluxVector (F.metric t) u t
  let v : Fin 2 → LoopPlane := EuclideanSpace.basisFun (Fin 2) ℝ
  let D : LoopPlane → ℝ := fun z => ∑ i : Fin 2, inner ℝ ((fderiv ℝ X z) (v i)) (v i)
  have hjoint (z : LoopPlane) (hz : z ∈ loopDiskSet) :
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ (Function.uncurry u) (t, z) :=
    (hu (t, z) (hdisk z hz)).contMDiffAt (hU.mem_nhds (hdisk z hz))
  have hX (z : LoopPlane) (hz : z ∈ loopDiskSet) : ContDiffAt ℝ 1 X z :=
    m65PlaneFluxVector_contDiffAt (F.metric t) u (hjoint z hz)
  have hD : ContinuousOn D loopDiskSet := by
    intro z hz
    have h (i : Fin 2) : ContinuousAt
        (fun w => inner ℝ ((fderiv ℝ X w) (v i)) (v i)) z :=
      (((hX z hz).continuousAt_fderiv (by simp)).clm_apply continuousAt_const).inner
        continuousAt_const
    have h' : ContinuousAt D z := by
      simpa +instances only [D, Fin.sum_univ_two, Pi.add_apply] using! (h 0).add (h 1)
    exact h'.continuousWithinAt
  have hI : IntegrableOn D loopDiskSet volume := hD.integrableOn_compact
    (isCompact_closedBall (0 : LoopPlane) 1)
  have heq : m65PlaneMotionDensity F u t =ᵐ[volume.restrict loopDiskSet] D := by
    filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet, hconf,
      htension] with z hz hc hτ
    obtain ⟨c, hc⟩ := hc
    rw [m65PlaneMotionDensity_eq_divergence_sub_tension F u hU hu (hdisk z hz) c hc,
      hτ, map_zero, sub_zero, m65PlaneFluxVector_divergence (F.metric t) u (hjoint z hz)]
  refine ⟨hI.congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, m65Integral_divergence_loopDisk X hX]
  apply intervalIntegral.integral_congr
  intro θ _
  exact m65PlaneFluxVector_inner (F.metric t) u t _ _

end PoincareConjecture
