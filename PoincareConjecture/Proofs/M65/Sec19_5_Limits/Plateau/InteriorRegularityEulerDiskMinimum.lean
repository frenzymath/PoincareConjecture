import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.InteriorRegularityEulerDiskLocal
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityWeakReplacement











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology ContDiff Manifold SchwartzMap

universe u

namespace PoincareConjecture.M65WeakDisk

set_option maxHeartbeats 1600000 in





theorem localMap_minimizes {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {N : ℕ} (g : RiemannianMetric 3 M) (e : M → EuclideanSpace ℝ (Fin N))
    (he : ContMDiff (𝓡 3) (𝓡 N) ∞ e)
    (hinj : ∀ p, Function.Injective (mfderiv (𝓡 3) (𝓡 N) e p))
    (hemb : Topology.IsEmbedding e) (compact : IsCompact (univ : Set M))
    {γ : LoopCircle → M} (hγ : Continuous γ) (F : M65WeakDisk e γ)
    (a b c : LoopCircle) (hmin : F.MinimizesNormalizedEnergy g a b c) :
    M65LocallyMinimizesEnergy g F.localMap := by
  classical
  intro x R hR hRU G hmatch
  let Z := closedBall x R
  have hZ : IsCompact Z := isCompact_closedBall x R
  have hZD : Z ⊆ loopDiskSet := hRU.trans ball_subset_closedBall
  have hgreen (test : 𝓢(LoopPlane, ℝ)) (i : Fin 2) (j : Fin N) :
      (∫ z in Z, (G.derivative i z j - F.derivative i z j) * test z +
        (e (G.value z) j - e (F.value z) j) *
          fderiv ℝ test z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0 :=
    M65Euler.compact_disk_green_difference isOpen_ball F.localMap G x hR.le hRU hmatch test i j
  obtain ⟨H, hparameter, hinside, houtside, hfields⟩ :=
    F.exists_boundary_replacement he.continuous hγ hZ hZD G.value G.derivative
      (G.value_memLp Z hZ hRU) (fun i => G.derivative_memLp i Z hZ hRU)
      F.parameter F.weakly_monotone (fun test i j => by
        rw [hgreen test i j]
        simp only [sub_self, zero_mul, integral_zero])
  have hHnormalized : H.Normalized a b c := by
    simpa only [Normalized, hparameter] using hmin.1
  have hcomparison := hmin.2 H hHnormalized
  let original := m65EmbeddedEnergyDensity g e F.value (fun i z => F.derivative i z)
  let replacement := m65EmbeddedEnergyDensity g e G.value G.derivative
  let global := m65EmbeddedEnergyDensity g e H.value (fun i z => H.derivative i z)
  have hFint : IntegrableOn original loopDiskSet := F.energy_integrable g he hinj hemb compact
  have hGint : IntegrableOn replacement Z := G.energy_integrable g he hinj hemb compact Z hZ hRU
  have hpiece : global =ᵐ[volume.restrict loopDiskSet] Z.piecewise replacement original := by
    filter_upwards [ae_all_iff.mpr hfields] with z hz
    by_cases hm : z ∈ Z
    · have hD (i : Fin 2) : H.derivative i z = G.derivative i z := by
        simpa only [piecewise_eq_of_mem Z _ _ hm] using hz i
      simp only [global, replacement, m65EmbeddedEnergyDensity, hinside z hm, hD,
        piecewise_eq_of_mem Z _ _ hm]
    · have hD (i : Fin 2) : H.derivative i z = F.derivative i z := by
        simpa only [piecewise_eq_of_notMem Z _ _ hm] using hz i
      simp only [global, original, m65EmbeddedEnergyDensity, houtside z hm, hD,
        piecewise_eq_of_notMem Z _ _ hm]
  have hsplit : (∫ z in loopDiskSet, global z) =
      (∫ z in Z, replacement z) + (∫ z in loopDiskSet, original z) - ∫ z in Z, original z := by
    rw [integral_congr_ae hpiece]
    have hh := integral_piecewise (μ := volume.restrict loopDiskSet) hZ.measurableSet
      (hGint.restrict (t := loopDiskSet)) (hFint.integrableOn (s := Zᶜ))
    rw [Measure.restrict_restrict_of_subset hZD, Measure.restrict_restrict hZ.measurableSet.compl,
      inter_comm Zᶜ loopDiskSet, ← Set.sdiff_eq loopDiskSet Z,
      setIntegral_sdiff hZ.measurableSet hFint hZD] at hh
    rw [hh]
    ring
  change (∫ z in loopDiskSet, original z) ≤ ∫ z in loopDiskSet, global z at hcomparison
  rw [hsplit] at hcomparison
  change (∫ z in Z, original z) ≤ ∫ z in Z, replacement z
  linarith only [hcomparison]

end PoincareConjecture.M65WeakDisk
