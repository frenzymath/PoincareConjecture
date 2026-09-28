import PoincareConjecture.Proofs.M35.Uniqueness.CenteredQuadratic
import PoincareConjecture.Proofs.M09.RiemannianProper
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.PrecompactChart
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.M35.Uniqueness

theorem exists_distance_square_base_support
    (g : RiemannianMetric 3 StandardCapSpace) (D : LeviCivitaData g)
    (hcomplete : MetricComplete g) (p : StandardCapSpace) :
    ∃ u : StandardCapSpace → ℝ,
      ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ u p ∧ u p = 0 ∧
      (∀ᶠ y in 𝓝 p, (g.edist p y).toReal ^ 2 ≤ u y) ∧ D.laplacian u p = 6 := by
  let c := extChartAt (𝓡 3) p
  let B := g.pullbackCoefficients c.symm
  let V := {v : StandardCapSpace | Real.sqrt (B (c p) v v) < 1}
  have hV : IsOpen V := by
    apply isOpen_lt _ continuous_const
    exact Real.continuous_sqrt.comp
      ((continuous_const.clm_apply continuous_id).clm_apply continuous_id)
  have h0V : (0 : StandardCapSpace) ∈ V := by simp [V]
  have hcompact := Proofs.M09.isCompact_closure_metric_ball g hcomplete p 1
  obtain ⟨e, he, he0, hederiv, hpaths⟩ :=
    g.exists_exponential_of_precompact_ball p (R := 1) (by norm_num) hcompact
  change ContMDiffOn (𝓡 3) (𝓡 3) ∞ e V at he
  change HasFDerivAt e (ContinuousLinearMap.id ℝ StandardCapSpace) 0 at hederiv
  have hecont : ContDiffAt ℝ ∞ e 0 :=
    contMDiffAt_iff_contDiffAt.mp (he.contMDiffAt (hV.mem_nhds h0V))
  let H := hecont.toOpenPartialHomeomorph e
    (f' := ContinuousLinearEquiv.refl ℝ StandardCapSpace) hederiv (by simp)
  have h0H : (0 : StandardCapSpace) ∈ H.source :=
    hecont.mem_toOpenPartialHomeomorph_source
      (f' := ContinuousLinearEquiv.refl ℝ StandardCapSpace) hederiv (by simp)
  have hpH : p ∈ H.target := by
    rw [← he0]
    exact H.map_source h0H
  have hzero : H.symm p = 0 := by
    rw [← he0]
    exact H.left_inv h0H
  have hEH : HasFDerivAt H
      (ContinuousLinearEquiv.refl ℝ StandardCapSpace).toContinuousLinearMap
      (H.symm p) := by
    change HasFDerivAt e (ContinuousLinearMap.id ℝ StandardCapSpace) (H.symm p)
    rw [hzero]
    exact hederiv
  have hInv : HasFDerivAt H.symm (ContinuousLinearMap.id ℝ StandardCapSpace) p := by
    exact H.hasFDerivAt_symm (f' := ContinuousLinearEquiv.refl ℝ StandardCapSpace) hpH hEH
  have hInvSmooth : ContDiffAt ℝ ∞ H.symm p := by
    apply H.contDiffAt_symm (f₀' := ContinuousLinearEquiv.refl ℝ StandardCapSpace) hpH hEH
    change ContDiffAt ℝ ∞ e (H.symm p)
    rw [hzero]
    exact hecont
  let u : StandardCapSpace → ℝ := fun y => g.euclideanCoefficients p (H.symm y) (H.symm y)
  have hu : ContDiffAt ℝ ∞ u p :=
    (contDiffAt_const.clm_apply hInvSmooth).clm_apply hInvSmooth
  refine ⟨u, contMDiffAt_iff_contDiffAt.mpr hu, ?_, ?_, ?_⟩
  · simp [u, hzero]
  · have hinV : ∀ᶠ y in 𝓝 p, H.symm y ∈ V :=
      hInv.continuousAt.preimage_mem_nhds (by simpa only [hzero] using hV.mem_nhds h0V)
    filter_upwards [hinV, H.open_target.mem_nhds hpH] with y hy hyH
    obtain ⟨_, _, _, _, _, _, _, hdist⟩ := hpaths (H.symm y) hy
    have hright : e (H.symm y) = y := H.right_inv hyH
    rw [hright] at hdist
    have hB : B (c p) (H.symm y) (H.symm y) = g.inner p (H.symm y) (H.symm y) := by
      exact RiemannianMetric.chartCoefficients_self g p _ _
    change g.edist p y ≤ ENNReal.ofReal (Real.sqrt (B (c p) (H.symm y) (H.symm y))) at hdist
    rw [hB] at hdist
    have hnonneg : 0 ≤ g.inner p (H.symm y) (H.symm y) := by
      by_cases hz : H.symm y = 0
      · simp [hz]
      · exact (g.pos p _ hz).le
    have hh := ENNReal.toReal_le_of_le_ofReal (Real.sqrt_nonneg _) hdist
    have hs := (sq_le_sq₀ ENNReal.toReal_nonneg (Real.sqrt_nonneg _)).mpr hh
    rw [Real.sq_sqrt hnonneg] at hs
    exact hs
  · exact laplacian_centered_metric_quadratic D hInvSmooth hzero hInv

end PoincareConjecture.M35.Uniqueness
