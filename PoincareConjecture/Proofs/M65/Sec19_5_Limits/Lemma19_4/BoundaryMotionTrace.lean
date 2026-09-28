import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BoundaryFluxTrace
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.DiskTraceDivergence
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.DiskTraceIntegral

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle BigOperators Topology intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m65Integral_motionDensity_eq_boundary_of_trace
    {a b : ℝ} (F : RicciFlow n M (Icc a b)) (u : ℝ → LoopPlane → M)
    {U : Set (ℝ × LoopPlane)} (hU : IsOpen U)
    (hu : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ (Function.uncurry u) U)
    {t : ℝ} (hdisk : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, (t, z) ∈ U)
    (V : (z : LoopPlane) → TangentSpace (𝓡 n) (u t z))
    (E A : (z : LoopPlane) → Fin 2 → TangentSpace (𝓡 n) (u t z))
    (hV : ContinuousOn (fun z => (⟨u t z, V z⟩ : TangentBundle (𝓡 n) M)) loopDiskSet)
    (hE : ∀ i, ContinuousOn (fun z => (⟨u t z, E z i⟩ : TangentBundle (𝓡 n) M))
      loopDiskSet)
    (hA : ∀ i, ContinuousOn (fun z => (⟨u t z, A z i⟩ : TangentBundle (𝓡 n) M))
      loopDiskSet)
    (hVe : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
      V z = curveVelocity (fun s => u s z) t)
    (hEe : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, ∀ i,
      E z i = mfderiv (𝓡 2) (𝓡 n) (u t) z (EuclideanSpace.basisFun (Fin 2) ℝ i))
    (hAe : ∀ z ∈ Metric.ball (0 : LoopPlane) 1, ∀ i,
      A z i = rampHorizontalCovariantDerivative (F.connection t) (fun s => u s z)
        (fun s => mfderiv (𝓡 2) (𝓡 n) (u s) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) t)
    (hconf : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
      ∃ c : ℝ, m60AreaGram (F.metric t) (u t) z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (htension : ∀ z ∈ Metric.ball (0 : LoopPlane) 1,
      m65PlaneTension (F.connection t) (u t) z = 0) :
    IntegrableOn (m65PlaneMotionDensity F u t) loopDiskSet volume ∧
      (∫ z in loopDiskSet, m65PlaneMotionDensity F u t z) =
        ∫ θ in (-Real.pi)..Real.pi,
          (F.metric t).inner (u t (Proofs.M58.angularPoint θ))
            (V (Proofs.M58.angularPoint θ))
            (∑ i : Fin 2, (Proofs.M58.angularPoint θ) i • E (Proofs.M58.angularPoint θ) i) := by
  let X := m65PlaneTraceFlux (F.metric t) (u t) V E
  let d : LoopPlane → ℝ := fun z => ∑ i : Fin 2, (F.metric t).inner (u t z) (A z i) (E z i)
  have hjoint (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) 1) :
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ (Function.uncurry u) (t, z) :=
    (hu (t, z) (hdisk z hz)).contMDiffAt (hU.mem_nhds (hdisk z hz))
  have hXeq (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) 1) :
      X z = m65PlaneFluxVector (F.metric t) u t z := by
    ext i
    fin_cases i <;>
      simp only [X, m65PlaneTraceFlux, PiLp.toLp_apply, m65PlaneFluxVector,
        m65PlaneVariationFlux, hVe z hz, hEe z hz] <;> rfl
  have hXloc (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) 1) :
      X =ᶠ[𝓝 z] m65PlaneFluxVector (F.metric t) u t := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hz] with w hw
    exact hXeq w hw
  have hXi (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) 1) :
      ContDiffAt ℝ 1 X z :=
    (m65PlaneFluxVector_contDiffAt (F.metric t) u (hjoint z hz)).congr_of_eventuallyEq
      (hXloc z hz)
  have hMd (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) 1) :
      m65PlaneMotionDensity F u t z = d z := by
    obtain ⟨c, hc⟩ := hconf z hz
    rw [m65PlaneMotionDensity_eq_sum_of_conformal F u t z c hc]
    exact Finset.sum_congr rfl (fun i _ => by rw [← hAe z hz i, ← hEe z hz i])
  have hd : ContinuousOn d loopDiskSet := by
    simpa +instances only [d, Fin.sum_univ_two, Pi.add_apply] using!
      (m65Metric_pairing_continuousOn (F.metric t) (u t) (fun z => A z 0)
        (fun z => E z 0) (hA 0) (hE 0)).add
        (m65Metric_pairing_continuousOn (F.metric t) (u t) (fun z => A z 1)
          (fun z => E z 1) (hA 1) (hE 1))
  have hdiv (z : LoopPlane) (hz : z ∈ Metric.ball (0 : LoopPlane) 1) :
      (∑ i : Fin 2, inner ℝ ((fderiv ℝ X z) (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) = d z := by
    rw [(hXloc z hz).fderiv_eq,
      ← m65PlaneFluxVector_divergence (F.metric t) u (hjoint z hz)]
    obtain ⟨c, hc⟩ := hconf z hz
    have h := m65PlaneMotionDensity_eq_divergence_sub_tension F u hU hu (hdisk z hz) c hc
    rw [htension z hz, map_zero, sub_zero] at h
    exact h.symm.trans (hMd z hz)
  have heq : m65PlaneMotionDensity F u t =ᵐ[volume.restrict loopDiskSet] d := by
    filter_upwards [m65Ae_mem_openLoopDisk] with z hz
    exact hMd z hz
  refine ⟨(hd.integrableOn_compact (isCompact_closedBall (0 : LoopPlane) 1)).congr
    heq.symm, ?_⟩
  rw [integral_congr_ae heq,
    m65Integral_divergence_loopDisk_of_trace X d
      (m65PlaneTraceFlux_continuousOn (F.metric t) (u t) V E hV hE) hXi hd hdiv]
  apply intervalIntegral.integral_congr
  intro θ _
  exact m65PlaneTraceFlux_inner (F.metric t) (u t) V E _ _

end PoincareConjecture
