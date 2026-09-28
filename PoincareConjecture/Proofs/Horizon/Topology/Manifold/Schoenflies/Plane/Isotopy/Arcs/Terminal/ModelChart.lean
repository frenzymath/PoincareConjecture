import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.TerminalData
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Critical
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.SignedSquares



noncomputable section
set_option autoImplicit false
open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_model_chart_height
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2)
    {x : E2} (hx : x ∈ closedBall 0 d.matchingRadius) :
    d.model (d.modelChart x) 2 = d.model (d.modelChart 0) 2 - x 0 ^ 2 + x 1 ^ 2 := by
  have hm := congrArg (fun y : E3 => inner Real (M.v : E3) y) (d.matching x hx)
  rw [d.transport_height, hform _ (d.matching_actual_source x hx)] at hm
  simp only [PiLp.smul_apply, smul_eq_mul, mul_pow,
    Real.sq_sqrt d.scale_pos.le] at hm
  nlinarith [d.scale_pos]

theorem terminal_model_chart_critical
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun q : S2 => d.model q 2) (d.modelChart 0) = 0 := by
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ (fun q : S2 => d.model q 2) := by
    exact (EuclideanSpace.proj (𝕜 := Real) (2 : Fin 3)).contMDiff.comp
      (d.model.contMDiff.comp (contMDiff_coe_sphere (n := 2)))
  let c := d.model (d.modelChart 0) 2
  let σ : Fin 2 → Real := ![-1, 1]
  have hlocal : (fun q : S2 => d.model q 2) ∘ d.modelChart =ᶠ[𝓝 (0 : E2)]
      (fun x => c + ∑ i : Fin 2, σ i * x i ^ 2) := by
    filter_upwards [closedBall_mem_nhds (0 : E2) d.matchingRadius_pos] with x hx
    simpa [c, σ, Fin.sum_univ_two, sub_eq_add_neg, add_assoc] using
      terminal_model_chart_height d hform hx
  rw [mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eventuallyEq hh d.modelChart
    d.modelChart_smooth d.modelChart_symm_smooth d.modelChart_zero hlocal]
  exact (Poincare.Analysis.Calculus.Morse.fderiv_diagonal_quadratic_eq_zero_iff c σ
    (by intro i; fin_cases i <;> norm_num [σ]) 0).mpr rfl

theorem terminal_model_chart_has_lower_and_upper_points
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    (∃ q : S2, d.model q 2 < d.model (d.modelChart 0) 2) ∧
      ∃ q : S2, d.model (d.modelChart 0) 2 < d.model q 2 := by
  let u := d.matchingRadius / 2
  have hu : 0 < u := div_pos d.matchingRadius_pos (by norm_num)
  have hmem (i : Fin 2) : EuclideanSpace.single i u ∈ closedBall (0 : E2) d.matchingRadius := by
    rw [mem_closedBall_zero_iff]
    simp only [PiLp.norm_single, Real.norm_eq_abs, abs_of_pos hu]
    dsimp [u]
    linarith [d.matchingRadius_pos]
  have hl := terminal_model_chart_height d hform (hmem 0)
  have hr := terminal_model_chart_height d hform (hmem 1)
  simp at hl hr
  constructor
  · exact ⟨d.modelChart (EuclideanSpace.single 0 u), by nlinarith [sq_pos_of_pos hu]⟩
  · exact ⟨d.modelChart (EuclideanSpace.single 1 u), by nlinarith [sq_pos_of_pos hu]⟩

theorem terminal_model_chart_not_isLocalMin
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ¬ IsLocalMin (fun q : S2 => d.model q 2) (d.modelChart 0) := by
  intro hmin
  have he := (d.modelChart_smooth.continuousOn.continuousAt
    (d.modelChart.open_source.mem_nhds d.modelChart_zero)).tendsto
  have hev := he.eventually hmin
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  let u := min ε d.matchingRadius / 2
  have hu : 0 < u := div_pos (lt_min hε d.matchingRadius_pos) (by norm_num)
  have hue : u < ε := by have := min_le_left ε d.matchingRadius; dsimp [u] at hu ⊢; linarith
  have hur : u < d.matchingRadius := by
    have := min_le_right ε d.matchingRadius
    dsimp [u] at hu ⊢
    linarith
  have hx : EuclideanSpace.single (0 : Fin 2) u ∈ closedBall (0 : E2) d.matchingRadius := by
    rw [mem_closedBall_zero_iff]
    simpa [abs_of_pos hu] using hur.le
  have hxb : EuclideanSpace.single (0 : Fin 2) u ∈ ball (0 : E2) ε := by
    rw [mem_ball_zero_iff]
    simpa [abs_of_pos hu] using hue
  have hm := hball hxb
  have hh := terminal_model_chart_height d hform hx
  simp at hh
  change d.model (d.modelChart 0) 2 ≤ d.model (d.modelChart (EuclideanSpace.single 0 u)) 2 at hm
  nlinarith [sq_pos_of_pos hu]

theorem terminal_model_chart_not_isLocalMax
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ¬ IsLocalMax (fun q : S2 => d.model q 2) (d.modelChart 0) := by
  intro hmax
  have he := (d.modelChart_smooth.continuousOn.continuousAt
    (d.modelChart.open_source.mem_nhds d.modelChart_zero)).tendsto
  have hev := he.eventually hmax
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hev
  let u := min ε d.matchingRadius / 2
  have hu : 0 < u := div_pos (lt_min hε d.matchingRadius_pos) (by norm_num)
  have hue : u < ε := by have := min_le_left ε d.matchingRadius; dsimp [u] at hu ⊢; linarith
  have hur : u < d.matchingRadius := by
    have := min_le_right ε d.matchingRadius
    dsimp [u] at hu ⊢
    linarith
  have hx : EuclideanSpace.single (1 : Fin 2) u ∈ closedBall (0 : E2) d.matchingRadius := by
    rw [mem_closedBall_zero_iff]
    simpa [abs_of_pos hu] using hur.le
  have hxb : EuclideanSpace.single (1 : Fin 2) u ∈ ball (0 : E2) ε := by
    rw [mem_ball_zero_iff]
    simpa [abs_of_pos hu] using hue
  have hm := hball hxb
  have hh := terminal_model_chart_height d hform hx
  simp at hh
  change d.model (d.modelChart (EuclideanSpace.single 1 u)) 2 ≤ d.model (d.modelChart 0) 2 at hm
  nlinarith [sq_pos_of_pos hu]



theorem terminal_standard_model_chart_center
    (d : TerminalSaddleGeometry M P p e) (hmodel : d.model = Saddle.shear)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    d.modelChart 0 = Saddle.saddlePoint := by
  have hc := terminal_model_chart_critical d hform
  rw [hmodel] at hc
  change mfderiv (𝓡 2) 𝓘(Real, Real) Saddle.height (d.modelChart 0) = 0 at hc
  obtain ⟨⟨qlo, hlo⟩, ⟨qhi, hhi⟩⟩ := terminal_model_chart_has_lower_and_upper_points d hform
  rw [hmodel] at hlo hhi
  change Saddle.height qlo < Saddle.height (d.modelChart 0) at hlo
  change Saddle.height (d.modelChart 0) < Saddle.height qhi at hhi
  have hbound (q : S2) : -(5 / 4 : Real) ≤ Saddle.height q ∧ Saddle.height q ≤ 1 := by
    have hn := EuclideanSpace.norm_sq_eq (q : E3)
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs] at hn
    have hnorm : ‖(q : E3)‖ = 1 := by simp
    rw [hnorm] at hn
    rw [Saddle.height_apply]
    constructor
    · nlinarith [sq_nonneg ((q : E3) 1), sq_nonneg ((q : E3) 2 + 1 / 2)]
    · nlinarith [sq_nonneg ((q : E3) 0), sq_nonneg ((q : E3) 1),
        sq_nonneg ((q : E3) 2 - 1)]
  have heq : Saddle.height (d.modelChart 0) = -1 := by
    rcases Saddle.critical_height_values hc with h | h | h
    · linarith [(hbound qlo).1]
    · exact h
    · linarith [(hbound qhi).2]
  exact (Saddle.critical_in_band_iff (d.modelChart 0) (by rw [heq]; norm_num)).mp hc

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
