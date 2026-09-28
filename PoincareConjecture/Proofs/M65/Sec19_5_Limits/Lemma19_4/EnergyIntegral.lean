import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.CompactDiskDerivative
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ConformalRicci
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FluxIntegral











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle BigOperators Topology intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} (F : RicciFlow n M (Icc a b))




theorem m65MovingEnergyDensity_hasDerivAt_of_conformal
    (u : ℝ → LoopPlane → M) {t : ℝ} {z : LoopPlane} (ht : t ∈ Ioo a b)
    (hu : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) 2 (Function.uncurry u) (t, z))
    (c : ℝ)
    (hconf : m60AreaGram (F.metric t) (u t) z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) :
    HasDerivAt (fun s => m60EnergyDensity (F.metric s) (u s) z)
      (-m65PlaneRicciTraceDensity (F.connection t) (u t) z +
        m65PlaneMotionDensity F u t z) t := by
  rw [m65PlaneRicciTraceDensity_eq_sum_of_conformal (F.connection t) (u t) z c hconf,
    m65PlaneMotionDensity_eq_sum_of_conformal F u t z c hconf]
  exact m65MovingEnergyDensity_hasDerivAt F u ht hu




theorem m65Disk_energy_firstVariation
    (u : ℝ → LoopPlane → M) {U : Set (ℝ × LoopPlane)} (hU : IsOpen U)
    (hu : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) ∞ (Function.uncurry u) U)
    {t : ℝ} (ht : t ∈ Ioo a b) (hdisk : ∀ z ∈ loopDiskSet, (t, z) ∈ U)
    (hconf : ∀ᵐ z ∂volume.restrict loopDiskSet,
      ∃ c : ℝ, m60AreaGram (F.metric t) (u t) z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (htension : ∀ᵐ z ∂volume.restrict loopDiskSet,
      m65PlaneTension (F.connection t) (u t) z = 0) :
    IntegrableOn (m65PlaneRicciTraceDensity (F.connection t) (u t)) loopDiskSet volume ∧
      HasDerivAt (fun s => ∫ z in loopDiskSet, m60EnergyDensity (F.metric s) (u s) z)
        (-(∫ z in loopDiskSet, m65PlaneRicciTraceDensity (F.connection t) (u t) z) +
          ∫ θ in (-Real.pi)..Real.pi,
            (F.metric t).inner (u t (Proofs.M58.angularPoint θ))
              (curveVelocity (fun s => u s (Proofs.M58.angularPoint θ)) t)
              (mfderiv (𝓡 2) (𝓡 n) (u t) (Proofs.M58.angularPoint θ)
                (Proofs.M58.angularPoint θ))) t := by
  let E : ℝ × LoopPlane → ℝ := fun p => m60EnergyDensity (F.metric p.1) (u p.1) p.2
  let R := m65PlaneRicciTraceDensity (F.connection t) (u t)
  let A := m65PlaneMotionDensity F u t
  have hjoint (z : LoopPlane) (hz : z ∈ loopDiskSet) :
      ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) (𝓡 n) 2 (Function.uncurry u) (t, z) :=
    ((hu (t, z) (hdisk z hz)).contMDiffAt (hU.mem_nhds (hdisk z hz))).of_le (by decide)
  have hE (z : LoopPlane) (hz : z ∈ loopDiskSet) : ContDiffAt ℝ 1 E (t, z) :=
    m65MovingEnergyDensity_contDiffAt F u ht (hjoint z hz)
  obtain ⟨hI, hderiv⟩ := m65HasDerivAt_integral_loopDisk E hE
  have hjet : (fun z => fderiv ℝ E (t, z) (1, 0)) =ᵐ[volume.restrict loopDiskSet]
      fun z => -R z + A z := by
    filter_upwards [ae_restrict_mem Metric.isClosed_closedBall.measurableSet, hconf]
      with z hz hc
    obtain ⟨c, hc⟩ := hc
    have hpartial : HasDerivAt (fun s => E (s, z)) (fderiv ℝ E (t, z) (1, 0)) t := by
      have h := ((hE z hz).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).prodMk (hasDerivAt_const t z))
      simpa +instances only [Function.comp_def, id_eq] using! h
    exact hpartial.unique
      (m65MovingEnergyDensity_hasDerivAt_of_conformal F u ht (hjoint z hz) c hc)
  obtain ⟨hAI, hAboundary⟩ := m65Integral_motionDensity_eq_boundary F u hU hu
    hdisk hconf htension
  have hRI : IntegrableOn R loopDiskSet volume := by
    apply (hAI.sub hI).congr
    filter_upwards [hjet] with z hz
    change A z - fderiv ℝ E (t, z) (1, 0) = R z
    rw [hz]
    ring
  refine ⟨hRI, hderiv.congr_deriv ?_⟩
  calc
    _ = ∫ z in loopDiskSet, -R z + A z := integral_congr_ae hjet
    _ = (∫ z in loopDiskSet, -R z) + ∫ z in loopDiskSet, A z := integral_add hRI.neg hAI
    _ = _ := by
      rw [integral_neg]
      exact congrArg (fun y => -(∫ z in loopDiskSet, R z) + y) hAboundary

end PoincareConjecture
