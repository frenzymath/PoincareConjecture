import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Plane.VectorFieldHomotopy
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.BoundedExistence
import PoincareConjecture.Proofs.Horizon.Analysis.ODE.Plane.Nontrapping
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Plane.FlowEndpoints
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Plane.SectionMap
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Plane.TailCorrection











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Manifold ContDiff

namespace Poincare.Manifold.SphereIsotopy

open Poincare.Manifold.PlaneDiffeomorph

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "v₀" => (!₂[(1 : ℝ), 0] : E₂)



theorem exists_compactly_supported_plane_isotopy
    (g : Diffeomorph (𝓡 2) (𝓡 2)
      (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) ∞)
    {K : Set (EuclideanSpace ℝ (Fin 2))} (hK : IsCompact K)
    (hfix : ∀ x, x ∉ K → g x = x) :
    ∃ F : ℝ → Diffeomorph (𝓡 2) (𝓡 2)
        (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)) ∞,
      ContDiff ℝ ∞
        (fun z : ℝ × EuclideanSpace ℝ (Fin 2) => F z.1 z.2) ∧
      (∀ x, F 0 x = x) ∧ (∀ x, F 1 x = g x) ∧
      ∃ S : Set (EuclideanSpace ℝ (Fin 2)), IsCompact S ∧
        ∀ t x, x ∉ S → F t x = x := by
  classical
  have hv : v₀ ≠ 0 := by
    intro h
    have := congrArg (fun x : E₂ => x 0) h
    norm_num at this
  obtain ⟨H, hH, hHne, hH0, hH1, R, hR, hKR, hHfix⟩ :=
    exists_pushforward_homotopy g hK hfix hv
  let A := R + 1
  have hA : 0 < A := by dsimp [A]; linarith
  have houter (p : ℝ) (x : E₂)
      (hx : x 0 ≤ -A ∨ A ≤ x 0 ∨ x 1 ≤ -A ∨ A ≤ x 1) : H (p, x) = v₀ := by
    apply hHfix p x
    have h0 : |x 0| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    have h1 : |x 1| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 1
    dsimp only [A] at hx
    rcases hx with hx | hx | hx | hx <;>
      linarith [(abs_le.mp h0).1, (abs_le.mp h0).2, (abs_le.mp h1).1, (abs_le.mp h1).2]
  obtain ⟨Φ, hΦ, hiΦ, hdΦ, hcΦ, _⟩ :=
    Poincare.ODE.Flow.exists_smooth_parametric_flow hH
      (isCompact_closedBall (0 : E₂) R) (fun p x hx => hHfix p x
        (by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hx))
  obtain ⟨D, hD, hDi, hDformula⟩ :=
    exists_horizontal_flow_coordinates hH hHne houter hΦ hiΦ hdΦ hcΦ
  have hD0 (x : E₂) : D 0 x = x := by
    rw [hDformula]
    have hid := flow_coordinates_eq_diffeomorph (Diffeomorph.refl (𝓡 2) E₂ ∞)
      (L := -A) (fun _ => rfl) (hiΦ 0)
      (fun y t => by simpa [hH0] using hdΦ 0 y t) x
    exact hid
  have hgsection (y : ℝ) : g (!₂[-A, y]) = !₂[-A, y] := by
    apply hfix
    intro hyK
    have hnorm : ‖(!₂[-A, y] : E₂)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hKR hyK
    have hcoord := PiLp.norm_apply_le (!₂[-A, y] : E₂) (0 : Fin 2)
    simp only [Matrix.cons_val_zero, norm_neg, Real.norm_eq_abs, abs_of_pos hA] at hcoord
    dsimp only [A] at hcoord
    linarith
  have hD1 (x : E₂) : D 1 x = g x := by
    rw [hDformula]
    exact flow_coordinates_eq_diffeomorph g hgsection (hiΦ 1)
      (fun y t => by simpa only [hH1] using hdΦ 1 y t) x
  have hDoutside (p : ℝ) (x : E₂)
      (hx : x 0 ≤ -A ∨ x 1 ≤ -A ∨ A ≤ x 1) : D p x = x := by
    rw [hDformula]
    apply flow_coordinates_eq_self_of_exterior
      (hH.comp (contDiff_const.prodMk contDiff_id))
      (fun y hy => houter p y (by rcases hy with hy | hy; exact Or.inl hy; exact Or.inr (Or.inr hy)))
      (hiΦ p) (hdΦ p) hx
  obtain ⟨σ, ρ, κ, hsσ, hsρ, hsκ, hcross, hσpos, hρbij, hκρ, hρκ, hρpos, hout⟩ :=
    exists_smooth_horizontal_section_map hH hHne (by linarith : -A < A)
      houter hΦ hiΦ hdΦ hcΦ
  let shift : ℝ × ℝ → ℝ := fun z => 2 * A - σ z
  have hsshift : ContDiff ℝ ∞ shift := contDiff_const.sub hsσ
  have hshiftout (p y : ℝ) (hy : y ≤ -A ∨ A ≤ y) : shift (p, y) = 0 ∧ ρ (p, y) = y := by
    obtain ⟨hρ, hσ⟩ := hout p y hy
    constructor
    · dsimp only [shift]
      rw [hσ]
      ring
    · exact hρ
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc (a := -A) (b := A))).exists_bound_of_continuousOn
    (hsσ.continuous.continuousOn (s := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-A) A))
  let Q := max C (2 * A)
  have hσbound (p : ℝ) (hp : p ∈ Set.Icc 0 1) (y : ℝ) : σ (p, y) ≤ Q := by
    by_cases hy : y ∈ Set.Icc (-A) A
    · exact (le_abs_self _).trans ((hC (p, y) ⟨hp, hy⟩).trans (le_max_left _ _))
    · have hyout : y ≤ -A ∨ A ≤ y := by
        simp only [Set.mem_Icc, not_and_or, not_le] at hy
        exact hy.imp le_of_lt le_of_lt
      rw [(hout p y hyout).2]
      dsimp only [Q]
      linarith [le_max_right C (2 * A)]
  have htail (p : ℝ) (hp : p ∈ Set.Icc 0 1) (x : E₂) (hx : Q ≤ x 0) :
      D p x = !₂[x 0 + shift (p, x 1), ρ (p, x 1)] := by
    have hray := Poincare.ODE.Plane.eq_horizontal_forward_ray
      (hH.comp (contDiff_const.prodMk contDiff_id)) (hdΦ p (!₂[-A, x 1]))
      (fun y hy => houter p y (Or.inr (Or.inl hy)))
      (a := σ (p, x 1)) (by rw [hcross]; simp)
      (x 0 + A - σ (p, x 1)) (by linarith [hσbound p hp (x 1)])
    rw [hcross] at hray
    rw [hDformula]
    convert hray using 1
    · congr 1
      ring
    · ext i
      fin_cases i <;> simp [shift]
      ring
  have hgRight (y : ℝ) : g (!₂[A, y]) = !₂[A, y] := by
    apply hfix
    intro hyK
    have hnorm : ‖(!₂[A, y] : E₂)‖ ≤ R := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hKR hyK
    have hcoord := PiLp.norm_apply_le (!₂[A, y] : E₂) (0 : Fin 2)
    simp only [Matrix.cons_val_zero, Real.norm_eq_abs, abs_of_pos hA] at hcoord
    dsimp only [A] at hcoord
    linarith
  have hend (p : ℝ) (hp : ∀ y, D p (!₂[A, y]) = !₂[A, y]) (y : ℝ) :
      shift (p, y) = 0 ∧ ρ (p, y) = y := by
    have hright : Φ p (A - -A) (!₂[-A, y]) = !₂[A, y] := by
      simpa only [hDformula, Matrix.cons_val_zero, Matrix.cons_val_one] using hp y
    obtain ⟨t, _, hu⟩ := Poincare.ODE.Plane.existsUnique_horizontal_right_section_hit
      (hH.comp (contDiff_const.prodMk contDiff_id)) (hHne p) (houter p)
      (hdΦ p (!₂[-A, y]))
    have hσ : σ (p, y) = A - -A :=
      (hu _ (congrArg (fun x : E₂ => x 0) (hcross p y))).trans
        (hu _ (congrArg (fun x : E₂ => x 0) hright)).symm
    have hρ : ρ (p, y) = y := by
      have hc := hcross p y
      rw [hσ, hright] at hc
      exact (congrArg (fun x : E₂ => x 1) hc).symm
    refine ⟨?_, hρ⟩
    dsimp only [shift]
    rw [hσ]
    ring
  have hend0 := hend 0 (fun y => hD0 (!₂[A, y]))
  have hend1 := hend 1 (fun y => (hD1 (!₂[A, y])).trans (hgRight y))
  obtain ⟨F, hF, hF0, hF1, S, hS, hSfix⟩ :=
    exists_compactly_supported_family_of_triangular_tail D hD
      (fun p _ x hx => hDoutside p x hx) shift ρ κ hsshift hsκ
      (fun p _ y => hκρ p y)
      (fun p _ y => deriv_section_inverse_pos hsρ hsκ hρκ hρpos p y)
      (fun p _ y hy => (hshiftout p y hy).1)
      (fun p _ y hy => (hshiftout p y hy).2)
      (fun y => (hend0 y).1) (fun y => (hend1 y).1)
      (fun y => (hend0 y).2) (fun y => (hend1 y).2) htail
  exact ⟨F, hF, fun x => (hF0 x).trans (hD0 x), fun x => (hF1 x).trans (hD1 x),
    S, hS, hSfix⟩

end Poincare.Manifold.SphereIsotopy
