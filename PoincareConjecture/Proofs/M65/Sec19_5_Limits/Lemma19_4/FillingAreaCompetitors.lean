import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.FillingAreaEnergy
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.EnergyComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M65Filling

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

theorem energy_integrable_of_withinC1 (g : RiemannianMetric 3 M)
    {f : LoopPlane → M} (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet) :
    IntegrableOn (m60EnergyDensity g f) loopDiskSet volume := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let A := fun z i => mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet z
    (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hc (i : Fin 2) : ContinuousOn (fun z => g.inner (f z) (A z i) (A z i))
      loopDiskSet :=
    (m65Attainment_continuousWithin_column hf _).inner_bundle
      (m65Attainment_continuousWithin_column hf _)
  have hE : ContinuousOn (fun z => (1 / 2 : ℝ) * ∑ i : Fin 2,
      g.inner (f z) (A z i) (A z i)) loopDiskSet := by
    apply ((continuousOn_const (c := (1 / 2 : ℝ))).mul ((hc 0).add (hc 1))).congr
    intro z _
    simp only [Fin.sum_univ_two]
    rfl
  apply (hE.integrableOn_compact (isCompact_closedBall (0 : LoopPlane) 1)).congr
  filter_upwards [m65Ae_mem_openLoopDisk] with z hz
  have hn : loopDiskSet ∈ 𝓝 z :=
    mem_of_superset (Metric.isOpen_ball.mem_nhds hz) Metric.ball_subset_closedBall
  simp only [m60EnergyDensity, Matrix.trace, Matrix.diag_apply, m60AreaGram, A,
    mfderivWithin_of_mem_nhds hn]

def moved_spanningDisk {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
    {gamma : C1FreeLoopSpace (M := M)} (S : M65MinimalDisk g D gamma)
    (g' : RiemannianMetric 3 M) (gamma' : C1FreeLoopSpace (M := M))
    (Phi : M → M) (hPhi : ContMDiff (𝓡 3) (𝓡 3) 1 Phi)
    (hboundary : ∀ x : ℝ, Phi (periodicFreeLoop gamma x) = periodicFreeLoop gamma' x) :
    LipschitzSpanningDisk g' gamma' := by
  let beta : LoopCircle ≃ₜ LoopCircle := {
    toFun := S.disk.reparameterization.map
    invFun := S.disk.reparameterization.inverse
    left_inv := S.disk.reparameterization.left_inverse
    right_inv := S.disk.reparameterization.right_inverse
    continuous_toFun := S.disk.reparameterization.continuous_map
    continuous_invFun := S.disk.reparameterization.continuous_inverse }
  refine m65Attainment_spanningDisk g' gamma' (Phi ∘ S.disk.map)
    (hPhi.comp_contMDiffOn S.boundary_regular) beta ?_
  intro z
  change Phi (S.disk.map z) = gamma' (beta z)
  rw [S.disk.boundary_eq]
  change Phi (gamma (beta z)) = gamma' (beta z)
  obtain ⟨x, hx⟩ := m65LoopAngular_continuous_surjective.2 (beta z)
  have h0 : gamma (beta z) = periodicFreeLoop gamma x := by
    rw [← hx]
    exact (gamma.boundary (m65LoopAngular x)).symm
  have h1 : gamma' (beta z) = periodicFreeLoop gamma' x := by
    rw [← hx]
    exact (gamma'.boundary (m65LoopAngular x)).symm
  rw [h0, h1]
  exact hboundary x

theorem filling_le_moved_energy {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
    {gamma : C1FreeLoopSpace (M := M)} (S : M65MinimalDisk g D gamma)
    (g' : RiemannianMetric 3 M) (gamma' : C1FreeLoopSpace (M := M))
    (Phi : M → M) (hPhi : ContMDiff (𝓡 3) (𝓡 3) 1 Phi)
    (hboundary : ∀ x : ℝ, Phi (periodicFreeLoop gamma x) = periodicFreeLoop gamma' x) :
    fillingArea g' gamma' ≤ ∫ z in loopDiskSet,
      m60EnergyDensity g' (Phi ∘ S.disk.map) z := by
  let Q := moved_spanningDisk S g' gamma' Phi hPhi hboundary
  have hbelow : BddBelow (range (fun Q' : LipschitzSpanningDisk g' gamma' => Q'.area)) := by
    refine ⟨0, ?_⟩
    rintro x ⟨Q', rfl⟩
    exact Q'.area_nonnegative
  have hle : fillingArea g' gamma' ≤ Q.area := csInf_le hbelow (mem_range_self Q)
  exact hle.trans (m65ParametrizedArea_le_energy g' (Phi ∘ S.disk.map)
    Q.area_integrable (energy_integrable_of_withinC1 g'
      (hPhi.comp_contMDiffOn S.boundary_regular)))

theorem minimal_energy_eq_filling {g : RiemannianMetric 3 M} {D : LeviCivitaData g}
    {gamma : C1FreeLoopSpace (M := M)} (S : M65MinimalDisk g D gamma) :
    (∫ z in loopDiskSet, m60EnergyDensity g S.disk.map z) = fillingArea g gamma := by
  have he : S.disk.area = ∫ z in loopDiskSet, m60EnergyDensity g S.disk.map z := by
    apply m65ParametrizedArea_eq_energy_of_conformal
    filter_upwards [m65Ae_mem_openLoopDisk] with z hz
    exact S.weakly_conformal z hz
  exact he.symm.trans S.area_eq

end PoincareConjecture.M65Filling
