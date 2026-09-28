import PoincareConjecture.Proofs.M47.TerminalGermsOpenCharts

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

def terminalSourceCountableDomain (rho : ℝ) : Opens E :=
  ⟨Metric.ball 0 (rho / 2), Metric.isOpen_ball⟩

def terminalSourceCountableZero {rho : ℝ} (hrho : 0 < rho) :
    terminalSourceCountableDomain rho :=
  ⟨0, Metric.mem_ball_self (half_pos hrho)⟩

noncomputable def terminalSourceCountableScaleFactor (rho0 rho : ℝ) : ℝ :=
  min 1 (rho0 / (2 * rho))

theorem terminalSourceCountableScaleFactor_bounds {rho0 rho : ℝ}
    (h0 : 0 < rho0) (hrho : 0 < rho) :
    0 < terminalSourceCountableScaleFactor rho0 rho ∧
      terminalSourceCountableScaleFactor rho0 rho ≤ 1 ∧
      terminalSourceCountableScaleFactor rho0 rho * (rho / 2) ≤ rho0 / 4 := by
  have hpos : 0 < terminalSourceCountableScaleFactor rho0 rho :=
    lt_min (by norm_num) (div_pos h0 (mul_pos (by norm_num) hrho))
  have hmul := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hrho)).mp
    (min_le_right (1 : ℝ) (rho0 / (2 * rho)))
  exact ⟨hpos, min_le_left _ _, by
    change min 1 (rho0 / (2 * rho)) * (rho / 2) ≤ rho0 / 4
    nlinarith only [hmul]⟩

private theorem scaled_norm_lt {rho0 rho : ℝ} (h0 : 0 < rho0) (hrho : 0 < rho)
    (x : terminalSourceCountableDomain rho) :
    ‖terminalSourceCountableScaleFactor rho0 rho • (x : E)‖ < rho0 / 4 := by
  obtain ⟨hlambda, _, hbound⟩ := terminalSourceCountableScaleFactor_bounds h0 hrho
  have hxBall : (x : E) ∈ Metric.ball 0 (rho / 2) := x.property
  have hx : ‖(x : E)‖ < rho / 2 := by
    simpa only [Metric.mem_ball, dist_zero_right] using hxBall
  rw [norm_smul, Real.norm_of_nonneg hlambda.le]
  exact (mul_lt_mul_of_pos_left hx hlambda).trans_le hbound

noncomputable def terminalSourceCountableScaleMap {rho0 rho : ℝ}
    (h0 : 0 < rho0) (hrho : 0 < rho) :
    terminalSourceCountableDomain rho → terminalSourceCountableDomain rho0 :=
  fun x => ⟨terminalSourceCountableScaleFactor rho0 rho • (x : E), by
    change ‖terminalSourceCountableScaleFactor rho0 rho • (x : E) - 0‖ < rho0 / 2
    rw [sub_zero]
    exact (scaled_norm_lt h0 hrho x).trans (by linarith only [h0])⟩

theorem terminalSourceCountableScaleMap_zero {rho0 rho : ℝ}
    (h0 : 0 < rho0) (hrho : 0 < rho) :
    terminalSourceCountableScaleMap h0 hrho (terminalSourceCountableZero hrho) =
      terminalSourceCountableZero h0 := by
  apply Subtype.ext
  exact smul_zero _

theorem terminalSourceCountableScaleMap_norm_lt {rho0 rho : ℝ}
    (h0 : 0 < rho0) (hrho : 0 < rho) (x : terminalSourceCountableDomain rho) :
    ‖(terminalSourceCountableScaleMap h0 hrho x : E)‖ < rho0 / 4 :=
  scaled_norm_lt h0 hrho x

theorem terminalSourceCountableScaleMap_dist {rho0 rho : ℝ}
    (h0 : 0 < rho0) (hrho : 0 < rho) (x y : terminalSourceCountableDomain rho) :
    dist (terminalSourceCountableScaleMap h0 hrho x)
        (terminalSourceCountableScaleMap h0 hrho y) =
      terminalSourceCountableScaleFactor rho0 rho * dist x y := by
  change dist (terminalSourceCountableScaleFactor rho0 rho • (x : E))
    (terminalSourceCountableScaleFactor rho0 rho • (y : E)) = _
  rw [dist_smul₀, Real.norm_of_nonneg (terminalSourceCountableScaleFactor_bounds h0 hrho).1.le]
  rfl

theorem terminalSourceCountableScaleMap_geometry {rho0 rho : ℝ}
    (h0 : 0 < rho0) (hrho : 0 < rho) :
    Topology.IsOpenEmbedding (terminalSourceCountableScaleMap h0 hrho) ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (terminalSourceCountableScaleMap h0 hrho) := by
  let L := (LinearEquiv.smulOfNeZero ℝ E
    (terminalSourceCountableScaleFactor rho0 rho)
    (terminalSourceCountableScaleFactor_bounds h0 hrho).1.ne').toContinuousLinearEquiv
  have hsmooth : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞
      (Subtype.val ∘ terminalSourceCountableScaleMap h0 hrho) := by
    intro x
    exact (Poincare.isLocalDiffeomorph_opensSubtypeVal (𝓡 3)
      (terminalSourceCountableDomain rho) x).comp (𝓡 3) E
        (L.toDiffeomorph.isLocalDiffeomorph (x : E))
  refine ⟨?_, terminalGerms_open_codomain_localDiffeomorph
    (terminalSourceCountableDomain rho0) hsmooth⟩
  apply Topology.IsOpenEmbedding.of_comp _
    (terminalSourceCountableDomain rho0).isOpen.isOpenEmbedding_subtypeVal
  exact L.toHomeomorph.isOpenEmbedding.comp
    (terminalSourceCountableDomain rho).isOpen.isOpenEmbedding_subtypeVal

end PoincareConjecture.M47
