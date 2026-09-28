import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.PhysicalModelChart



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
open SaddleLevel
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem terminal_raw_model_critical_of_physical
    (d : TerminalSaddleGeometry M P p e) (q : S2)
    (hq : mfderiv (𝓡 2) 𝓘(Real, Real)
      (fun y : S2 => inner Real (M.v : E3) (d.filledModel y)) q = 0) :
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun y : S2 => d.model y 2) q = 0 := by
  let h : S2 → Real := fun y => inner Real (M.v : E3) (d.filledModel y)
  let J : Real → Real := fun z =>
    (z - inner Real (M.v : E3) (g p)) / d.scale + d.model (d.modelChart 0) 2
  have hJ : ContDiff Real ∞ J := by dsimp [J]; fun_prop
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h :=
    (innerSL Real (M.v : E3)).contMDiff.comp
      (d.filledModel.contMDiff.comp (contMDiff_coe_sphere (n := 2)))
  have hcomp : (fun y : S2 => d.model y 2) = J ∘ h := by
    funext y
    change d.model y 2 =
      (inner Real (M.v : E3) (d.transport (d.model y)) -
        inner Real (M.v : E3) (g p)) / d.scale + d.model (d.modelChart 0) 2
    rw [d.transport_height]
    field_simp [d.scale_pos.ne']
    ring
  rw [hcomp, mfderiv_comp q ((hJ.contMDiff _).mdifferentiableAt (by simp))
    ((hh q).mdifferentiableAt (by simp)), hq]
  ext x
  simp



theorem exists_terminal_model_regular_window
    (d : TerminalSaddleGeometry M P p e)
    (hform : ∀ x ∈ e.source, inner Real (M.v : E3) (g (e x)) =
      inner Real (M.v : E3) (g p) - x 0 ^ 2 + x 1 ^ 2) :
    ∃ ε : Real, 0 < ε ∧ ∀ t ∈ Icc (-ε) ε, t ≠ 0 → ∀ q : S2,
      inner Real (M.v : E3) (d.filledModel q) = inner Real (M.v : E3) (g p) + t →
      mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun y : S2 => inner Real (M.v : E3) (d.filledModel y)) q ≠ 0 := by
  rcases d.model_kind with hmodel | hmodel
  · have hcenter := terminal_standard_model_chart_center d hmodel hform
    refine ⟨d.scale / 8, div_pos d.scale_pos (by norm_num), ?_⟩
    intro t ht hne q hq hcrit
    have hc := terminal_raw_model_critical_of_physical d q hcrit
    rw [hmodel] at hc
    have hh := d.transport_height (d.model q)
    change inner Real (M.v : E3) (d.filledModel q) = _ at hh
    rw [hq, hmodel, hcenter] at hh
    change _ = _ + d.scale * (Saddle.height q - Saddle.height Saddle.saddlePoint) at hh
    rw [Saddle.height_saddlePoint] at hh
    rcases Saddle.critical_height_values hc with h | h | h
    · rw [h] at hh
      linarith [ht.1, d.scale_pos]
    · rw [h] at hh
      exact hne (by linarith)
    · rw [h] at hh
      linarith [ht.2, d.scale_pos]
  · have hc := terminal_model_chart_critical d hform
    rw [hmodel] at hc
    have hz := terminal_nested_model_chart_latitude d hmodel hform
    obtain ⟨q₀, hqz, hqh, hqc, _⟩ := Saddle.Nested.exists_unique_critical_point_in_height_band
    have hqp : q₀ = d.modelChart 0 := Saddle.Nested.critical_latitude_unique_in_saddle_interval
      hqc hc (Ioo_subset_Icc_self hqz) (Ioo_subset_Icc_self hz)
    rw [hqp] at hqh
    let a := Saddle.Nested.height (d.modelChart 0)
    let η := min (a - 1) (13 / 10 - a) / 2
    have hη : 0 < η := half_pos (lt_min (by dsimp [a]; linarith [hqh.1])
      (by dsimp [a]; linarith [hqh.2]))
    have hηl : η < a - 1 := by
      have := min_le_left (a - 1) (13 / 10 - a)
      dsimp [η] at hη ⊢
      linarith
    have hηu : η < 13 / 10 - a := by
      have := min_le_right (a - 1) (13 / 10 - a)
      dsimp [η] at hη ⊢
      linarith
    refine ⟨d.scale * η, mul_pos d.scale_pos hη, ?_⟩
    intro t ht hne q hq hcrit
    have hraw := terminal_raw_model_critical_of_physical d q hcrit
    rw [hmodel] at hraw
    have hh := d.transport_height (d.model q)
    change inner Real (M.v : E3) (d.filledModel q) = _ at hh
    rw [hq, hmodel] at hh
    change _ = _ + d.scale * (Saddle.Nested.height q - a) at hh
    have hband : Saddle.Nested.height q ∈ Icc (1 : Real) (13 / 10) := by
      constructor <;> nlinarith [ht.1, ht.2, d.scale_pos]
    have heq := (Saddle.Nested.critical_in_height_band_iff_eq_saddle hc hz q hband).mp hraw
    rw [heq] at hh
    change _ = _ + d.scale * (a - a) at hh
    exact hne (by linarith)

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
