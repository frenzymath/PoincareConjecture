import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetRadiusStokes
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetLaplacian
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussBonnetInteriorLog
import Mathlib.Analysis.Calculus.Gradient.Basic

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric MeasureTheory InnerProductSpace Complex
open scoped Topology ContDiff Manifold Laplacian

namespace PoincareConjecture.M65Gauss

theorem integral_laplacian_disk_off_countable {u : LoopPlane → ℝ}
    {U S : Set LoopPlane} (hU : IsOpen U) (hS : S.Countable)
    (hu : ContDiffOn ℝ 1 u U)
    (hui : ∀ z ∈ U \ S, ContDiffAt ℝ 2 u z)
    (x : LoopPlane) {R : ℝ} (hR : 0 < R) (hRU : closedBall x R ⊆ U)
    (hL : IntegrableOn (Δ u) (closedBall x R)) :
    (∫ z in closedBall x R, Δ u z) =
      R * ∫ θ in (-Real.pi)..Real.pi,
        fderiv ℝ u (x + R • Proofs.M58.angularPoint θ) (Proofs.M58.angularPoint θ) := by
  let T := (toDual ℝ LoopPlane).symm.toContinuousLinearEquiv
  let X : LoopPlane → LoopPlane := fun z => T (fderiv ℝ u z)
  have hXC : ContinuousOn X U := T.continuous.comp_continuousOn
    ((hu.fderiv_of_isOpen hU (m := 0) (by norm_num)).continuousOn)
  have hXi (z : LoopPlane) (hz : z ∈ ball x R \ S) : ContDiffAt ℝ 1 X z :=
    T.contDiff.contDiffAt.comp z
      ((hui z ⟨hRU (ball_subset_closedBall hz.1), hz.2⟩).fderiv_right
        (m := 1) (by norm_num))
  have hdiv (z : LoopPlane) (hz : z ∈ ball x R \ S) :
      (∑ i : Fin 2, inner ℝ (fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) = Δ u z := by
    have hd := ((hui z ⟨hRU (ball_subset_closedBall hz.1), hz.2⟩).fderiv_right
      (m := 1) (by norm_num)).differentiableAt (by simp)
    have h := T.hasFDerivAt.comp z hd.hasFDerivAt
    change HasFDerivAt X _ z at h
    rw [h.fderiv, laplacian_eq_iteratedFDeriv_orthonormalBasis u
      (EuclideanSpace.basisFun (Fin 2) ℝ)]
    simp only [ContinuousLinearMap.comp_apply, T, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, toDual_symm_apply, iteratedFDeriv_two_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have h := integral_divergence_disk_off_countable X (Δ u) S hS x hR
    (hXC.mono hRU) hXi hL hdiv
  simpa only [X, T, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    toDual_symm_apply] using h

end PoincareConjecture.M65Gauss

namespace PoincareConjecture.M65MinimalDisk

open M65Gauss

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {gamma : C1FreeLoopSpace (M := M)}

theorem exists_interior_curvature_flux (S : M65MinimalDisk g connection gamma) :
    let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
    let G := fun z : LoopPlane => -(∑ i : Fin 2, fderiv ℝ (fun y =>
      fderiv ℝ (fun w => Real.log (S.conformalFactor w)) y
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2
    ∃ (B : Finset ℂ) (m : ℂ → ℕ) (v : LoopPlane → ℝ),
      (∀ z, z ∈ B ↔ z ∈ ball (0 : ℂ) 1 ∧ S.conformalFactor (e z) = 0) ∧
      ContDiffOn ℝ 1 v (ball (0 : LoopPlane) 1) ∧
      (∀ z ∈ ball (0 : LoopPlane) 1, e.symm z ∉ B →
        v z = Real.log (S.conformalFactor z) / 2 -
          ∑ a ∈ B, (m a : ℝ) * Real.log ‖z - e a‖) ∧
      ∀ R : ℝ, 0 < R → R < 1 →
        IntegrableOn G (closedBall (0 : LoopPlane) R) ∧
        (∫ z in closedBall (0 : LoopPlane) R, G z) =
          -R * ∫ θ in (-Real.pi)..Real.pi,
            fderiv ℝ v (R • Proofs.M58.angularPoint θ) (Proofs.M58.angularPoint θ) := by
  classical
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let U := ball (0 : LoopPlane) 1
  let G := fun z : LoopPlane => -(∑ i : Fin 2, fderiv ℝ (fun y =>
    fderiv ℝ (fun w => Real.log (S.conformalFactor w)) y
      (EuclideanSpace.basisFun (Fin 2) ℝ i)) z (EuclideanSpace.basisFun (Fin 2) ℝ i)) / 2
  obtain ⟨B, m, u, hB, hu, hui, heq, _hfactors⟩ := S.exists_interior_logarithmic_potential
  let E : Set LoopPlane := e.symm ⁻¹' (B : Set ℂ)
  let v : LoopPlane → ℝ := u ∘ e.symm
  have hE : E.Finite := B.finite_toSet.preimage e.symm.injective.injOn
  have hEC : IsClosed E := B.finite_toSet.isClosed.preimage e.symm.continuous
  have hmap (z : LoopPlane) (hz : z ∈ U) : e.symm z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    change ‖orthonormalBasisOneI.repr.symm z‖ < 1
    rw [orthonormalBasisOneI.repr.symm.norm_map]
    exact mem_ball_zero_iff.mp hz
  have hv : ContDiffOn ℝ 1 v U := hu.comp e.symm.contDiff.contDiffOn hmap
  have hvi : ContDiffOn ℝ ∞ v (U \ E) := hui.comp e.symm.contDiff.contDiffOn
    (fun z hz => ⟨hmap z hz.1, hz.2⟩)
  have hVE : IsOpen (U \ E) := isOpen_ball.sdiff hEC
  have hformula (z : LoopPlane) (hz : z ∈ U) (hne : e.symm z ∉ B) :
      v z = Real.log (S.conformalFactor z) / 2 -
        ∑ a ∈ B, (m a : ℝ) * Real.log ‖z - e a‖ := by
    have hh := heq (e.symm z) (hmap z hz) hne
    change u (e.symm z) = Real.log (S.conformalFactor (e (e.symm z))) / 2 -
      ∑ a ∈ B, (m a : ℝ) * Real.log ‖e.symm z - a‖ at hh
    rw [e.apply_symm_apply] at hh
    have hn (a : ℂ) : ‖e.symm z - a‖ = ‖z - e a‖ := by
      have h := orthonormalBasisOneI.repr.norm_map (e.symm z - a)
      change ‖e (e.symm z - a)‖ = ‖e.symm z - a‖ at h
      simpa only [map_sub, e.apply_symm_apply] using h.symm
    change u (e.symm z) = _
    simpa only [hn] using hh
  have hsmooth (z : LoopPlane) (hz : z ∈ U) : ContDiffAt ℝ ∞ S.conformalFactor z := by
    apply e.contDiffAt_comp_iff.mp
    exact S.conformalFactor_complex_contDiffOn.contDiffAt (isOpen_ball.mem_nhds (hmap z hz))
  have hDelta (z : LoopPlane) (hz : z ∈ U \ E) : Δ v z = -G z := by
    have hp : 0 < S.conformalFactor z := by
      apply lt_of_le_of_ne (S.conformalFactor_nonneg z)
      intro hzero
      apply hz.2
      exact (hB (e.symm z)).mpr ⟨hmap z hz.1, by
        change S.conformalFactor (e (e.symm z)) = 0
        simpa only [e.apply_symm_apply] using hzero.symm⟩
    have hlog : ContDiffAt ℝ 2 (fun w => Real.log (S.conformalFactor w)) z :=
      ((hsmooth z hz.1).log hp.ne').of_le (WithTop.coe_le_coe.mpr le_top)
    have hne (a : ℂ) (ha : a ∈ B) : z ≠ e a := by
      intro heza
      apply hz.2
      change e.symm z ∈ B
      simpa only [heza, e.symm_apply_apply] using ha
    have hlocal : v =ᶠ[𝓝 z] fun w => (1 / 2 : ℝ) * Real.log (S.conformalFactor w) -
        ∑ a ∈ B, (m a : ℝ) * Real.log ‖w - e a‖ := by
      filter_upwards [hVE.mem_nhds hz] with w hw
      rw [hformula w hw.1 hw.2]
      ring
    rw [logarithmic_residual_laplacian B e (fun a => (m a : ℝ)) hlog hne hlocal,
      laplacian_eq_plane_trace hlog]
    dsimp only [G]
    ring
  have hGloc : LocallyIntegrableOn G U := by
    intro z hz
    obtain ⟨r, hr, _hsub, hL⟩ := S.interior_logarithmicDensity_integrable hz
    exact ⟨ball z r, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z hr), hL⟩
  refine ⟨B, m, v, hB, hv, hformula, ?_⟩
  intro R hR hR1
  have hRU : closedBall (0 : LoopPlane) R ⊆ U := closedBall_subset_ball hR1
  have hGR : IntegrableOn G (closedBall (0 : LoopPlane) R) :=
    hGloc.integrableOn_compact_subset hRU (isCompact_closedBall 0 R)
  have hAE : (Δ v) =ᵐ[volume.restrict (closedBall (0 : LoopPlane) R)] fun z => -G z := by
    filter_upwards [ae_restrict_mem measurableSet_closedBall,
      ae_restrict_of_ae (hE.countable.ae_notMem volume)] with z hz hn
    exact hDelta z ⟨hRU hz, hn⟩
  have hVL : IntegrableOn (Δ v) (closedBall (0 : LoopPlane) R) := hGR.neg.congr hAE.symm
  have hStokes := integral_laplacian_disk_off_countable isOpen_ball hE.countable hv
    (fun z hz => ((hvi.contDiffAt (hVE.mem_nhds hz)).of_le
      (WithTop.coe_le_coe.mpr le_top))) 0 hR hRU hVL
  rw [integral_congr_ae hAE, integral_neg] at hStokes
  simp only [zero_add] at hStokes
  refine ⟨hGR, ?_⟩
  linarith

end PoincareConjecture.M65MinimalDisk
