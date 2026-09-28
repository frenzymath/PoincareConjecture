import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.BranchHarmonicEquation
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.MinimalDiskHarmonicChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Complex
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.M65MinimalDisk

open M65Branch

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {connection : LeviCivitaData g}
  {γ : C1FreeLoopSpace (M := M)}

theorem interior_branch_power_factor (S : M65MinimalDisk g connection γ)
    {x : LoopPlane} (hx : x ∈ Metric.ball (0 : LoopPlane) 1) :
    let e := orthonormalBasisOneI.repr
    let H := (chartAt LoopAmbient (S.disk.map x)) ∘ S.disk.map ∘ e
    let z0 := e.symm x
    ∃ (m : ℕ) (K : ℂ → Fin 3 → ℂ), ContDiffAt ℝ 1 K z0 ∧ K z0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 z0, complexGradient H z = (z - z0) ^ m • K z := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let q := chartAt LoopAmbient (S.disk.map x)
  let G := q ∘ S.disk.map
  let H := G ∘ e
  let z0 := e.symm x
  obtain ⟨gE, DE, W, hW, hxW, hWdisk, hsource, hG, _, heq⟩ :=
    S.exists_harmonic_chart_neighborhood hx
  let V := e ⁻¹' W
  have hV : IsOpen V := hW.preimage e.continuous
  have hz0 : z0 ∈ V := by
    change e (e.symm x) ∈ W
    simpa only [e.apply_symm_apply] using hxW
  have hH : ContDiffOn ℝ ∞ H V := hG.comp e.contDiff.contDiffOn (fun _ hz => hz)
  have hmatrix (z : ℂ) (hz : z ∈ V) :
      dbar (complexGradient H) z = harmonicMatrix DE H z (complexGradient H z) :=
    plane_harmonic_to_complex DE (hG.contDiffAt (hW.mem_nhds hz)) (heq (e z) hz)
  have hnot : ¬∀ᶠ z in 𝓝 z0, complexGradient H z = 0 := by
    intro hzero
    have hfinite := S.finite_branches.preimage e.injective.injOn
    apply (infinite_of_mem_nhds z0 ?_) hfinite
    filter_upwards [hzero, hV.mem_nhds hz0] with z hz hzw
    have hzint := hWdisk hzw
    refine ⟨Metric.ball_subset_closedBall hzint, ?_⟩
    have hnhds : loopDiskSet ∈ 𝓝 (e z) :=
      mem_of_superset (Metric.isOpen_ball.mem_nhds hzint) Metric.ball_subset_closedBall
    rw [mfderivWithin_of_mem_nhds hnhds]
    have hDH : fderiv ℝ H z = 0 := (complexGradient_eq_zero_iff H z).mp hz
    have hDG := ((hG.contDiffAt (hW.mem_nhds hzw)).differentiableAt (by simp)).hasFDerivAt
    have hd := hDG.comp z e.hasFDerivAt
    have hcoord (v : LoopPlane) : fderiv ℝ G (e z) v = 0 := by
      have hv := congrArg (fun L : ℂ →L[ℝ] LoopAmbient => L (e.symm v)) hd.fderiv
      change fderiv ℝ H z (e.symm v) = fderiv ℝ G (e z) (e (e.symm v)) at hv
      simpa only [hDH, zero_apply, e.apply_symm_apply] using hv.symm
    have hf := ((S.interior_smooth.contMDiffAt
      (Metric.isOpen_ball.mem_nhds hzint)).mdifferentiableAt (by simp))
    apply ContinuousLinearMap.ext
    intro v
    have hv := m65PlaneDerivative_chart (S.disk.map x) hf (hsource hzw) v
    change Proofs.M09.chartVectorField (S.disk.map x) (fderiv ℝ G (e z) v)
      (S.disk.map (e z)) = _ at hv
    rw [hcoord v] at hv
    simpa only [Proofs.M09.chartVectorField, VectorField.mpullback, map_zero,
      zero_apply] using hv.symm
  exact exists_power_factor_of_local_matrix_equation hV hz0
    (contDiffOn_harmonicMatrix DE hV hH) (contDiffOn_complexGradient hV hH) hmatrix hnot

end PoincareConjecture.M65MinimalDisk
