import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ModelChart
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.Orientation
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

open SaddleLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem standard_lower_height_level_not_preconnected
    {t : Real} (ht : 0 < t) (htu : t < 1 / 4) :
    ¬ IsPreconnected {q : S2 | Saddle.height q = -1 - t} := by
  let X := Real.sqrt (1 / 2 + t)
  let Y := Real.sqrt (1 / 4 - t)
  have hX : X ^ 2 = 1 / 2 + t := Real.sq_sqrt (by linarith)
  have hY : Y ^ 2 = 1 / 4 - t := Real.sq_sqrt (by linarith)
  have hnorm (σ : Real) (hσ : σ ^ 2 = 1) :
      ‖Saddle.vector (σ * X) Y (-1 / 2)‖ = 1 := by
    have hn := EuclideanSpace.norm_sq_eq (Saddle.vector (σ * X) Y (-1 / 2))
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, Saddle.vector_zero,
      Saddle.vector_one, Saddle.vector_two, mul_pow, hσ, one_mul, hX, hY] at hn
    nlinarith [norm_nonneg (Saddle.vector (σ * X) Y (-1 / 2))]
  let q (σ : Real) (hσ : σ ^ 2 = 1) : S2 :=
    ⟨Saddle.vector (σ * X) Y (-1 / 2), mem_sphere_zero_iff_norm.mpr (hnorm σ hσ)⟩
  have hlevel (σ : Real) (hσ : σ ^ 2 = 1) : Saddle.height (q σ hσ) = -1 - t := by
    rw [Saddle.height_apply]
    simp only [q, Saddle.vector_two, Saddle.vector_zero, mul_pow, hσ, one_mul, hX]
    ring
  intro hpre
  have hcont : Continuous (fun q : S2 => (q : E3) 0) := by fun_prop
  have hbetween : (0 : Real) ∈ Icc
      ((q (-1) (by norm_num) : E3) 0) ((q 1 (by norm_num) : E3) 0) := by
    simp only [q, Saddle.vector_zero, neg_one_mul, one_mul, mem_Icc]
    exact ⟨neg_nonpos.mpr (Real.sqrt_nonneg _), Real.sqrt_nonneg _⟩
  obtain ⟨u, hu, huz⟩ := hpre.intermediate_value
    (hlevel (-1) (by norm_num)) (hlevel 1 (by norm_num)) hcont.continuousOn hbetween
  have hn := EuclideanSpace.norm_sq_eq (u : E3)
  have hun : ‖(u : E3)‖ = 1 := norm_eq_of_mem_sphere u
  rw [hun] at hn
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
  change (u : E3) 0 = 0 at huz
  change Saddle.height u = -1 - t at hu
  rw [Saddle.height_apply, huz, zero_pow (by norm_num : 2 ≠ 0), sub_zero] at hu
  rw [huz] at hn
  nlinarith [sq_nonneg ((u : E3) 1), sq_nonneg t]

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_standard_lower_source_level
    (d : TerminalSaddleGeometry M P p e) (hmodel : d.model = Saddle.shear)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) (t : Real) :
    {q : S2 | inner Real (M.v : E3) (d.filledModel q) =
      inner Real (M.v : E3) (g p) - d.scale * t} =
      {q : S2 | Saddle.height q = -1 - t} := by
  have hcenter := terminal_standard_model_chart_center d hmodel hform
  have hheight : d.model (d.modelChart 0) 2 = -1 := by
    rw [hmodel, hcenter]
    exact Saddle.height_saddlePoint
  ext q
  change inner Real (M.v : E3) (d.transport (d.model q)) = _ ↔ _
  rw [d.transport_height, hheight, hmodel]
  change inner Real (M.v : E3) (g p) + d.scale * (Saddle.height q - -1) =
    inner Real (M.v : E3) (g p) - d.scale * t ↔ Saddle.height q = -1 - t
  constructor
  · intro h
    apply (mul_left_inj' (ne_of_gt d.scale_pos)).mp
    nlinarith
  · intro h
    rw [h]
    ring

theorem terminal_standard_lower_slice_not_preconnected
    (d : TerminalSaddleGeometry M P p e) (hmodel : d.model = Saddle.shear)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    {t : Real} (ht : 0 < t) (htu : t < 1 / 4) :
    ¬ IsPreconnected (d.B (inner Real (M.v : E3) (g p) - d.scale * t)) := by
  intro h
  have hs := (model_slice_preconnected_iff d _).mp h
  rw [terminal_standard_lower_source_level d hmodel hform t] at hs
  exact standard_lower_height_level_not_preconnected ht htu hs

theorem exists_unmatched_standard_slice_of_connected_lower_levels
    (hg : g ∈ M.tree.leaves) (d : TerminalSaddleGeometry M P p e)
    (hmodel : d.model = Saddle.shear)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    {ε : Real} (hε : 0 < ε)
    (hactual : ∀ s ∈ Ioo (0 : Real) ε,
      IsPreconnected {q : S2 | inner Real (M.v : E3) (g q) =
        inner Real (M.v : E3) (g p) - s}) :
    ∃ z ∈ d.I, ¬ ∃ Q : Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      Q '' d.A z = d.B z := by
  let s := min d.eta (min ε (d.scale / 4)) / 2
  have hs : 0 < s := div_pos (lt_min d.eta_pos
    (lt_min hε (div_pos d.scale_pos (by norm_num)))) (by norm_num)
  have hsη : s < d.eta := by
    have := min_le_left d.eta (min ε (d.scale / 4))
    dsimp [s] at hs ⊢
    linarith
  have hsε : s < ε := by
    have := (min_le_right d.eta (min ε (d.scale / 4))).trans (min_le_left ε (d.scale / 4))
    dsimp [s] at hs ⊢
    linarith
  have hsu : s < d.scale / 4 := by
    have := (min_le_right d.eta (min ε (d.scale / 4))).trans (min_le_right ε (d.scale / 4))
    dsimp [s] at hs ⊢
    linarith
  refine ⟨inner Real (M.v : E3) (g p) - s, ?_, ?_⟩
  · change d.ends.lowerCut ≤ _ ∧ _ ≤ d.ends.upperCut
    rw [d.lowerCut_eq, d.upperCut_eq]
    constructor <;> linarith [d.eta_pos]
  · rintro ⟨Q, hQ⟩
    have hA := (actual_slice_preconnected_iff hg d _).mpr (hactual s ⟨hs, hsε⟩)
    have hB := hA.image Q Q.continuous.continuousOn
    rw [hQ] at hB
    have ht : 0 < s / d.scale := div_pos hs d.scale_pos
    have htu : s / d.scale < 1 / 4 := (div_lt_iff₀ d.scale_pos).mpr (by linarith)
    have hn := terminal_standard_lower_slice_not_preconnected d hmodel hform ht htu
    have he : d.scale * (s / d.scale) = s := by field_simp [ne_of_gt d.scale_pos]
    rw [he] at hn
    exact hn hB

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
