import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.FourierCoordinates

/-!
# Uniform C1 control of actual H1 coordinates

The normalized energy bounds the coordinate norm by the two uniform
norms and gives continuous dependence on actual C1 data. MT2007
Claim 19.1, p. 437; `2026-09-21-parametric-h1-composition.md`, statements 1-2.
-/

set_option autoImplicit false

open AddCircle MeasureTheory Filter
open scoped Topology

namespace PoincareMT.M63

variable {L : ℝ} [Fact (0 < L)]

/-- Actual H1 coordinates are bounded by the function and first derivative
uniform norms. MT2007 Claim 19.1, p. 437; parametric H1 composition
derivation, statement 1. Haar measure has mass one. -/
theorem norm_periodicH1Coordinates_le (f g : C(AddCircle L, ℂ))
    (h : ∀ x : ℝ, HasDerivAt (fun y : ℝ => f (y : AddCircle L)) (g (x : AddCircle L)) x) :
    ‖periodicH1Coordinates f g h‖ ≤ ‖f‖ + ‖g‖ := by
  have hb (a : C(AddCircle L, ℂ)) :
      (∫ x : AddCircle L, ‖a x‖ ^ 2 ∂haarAddCircle) ≤ ‖a‖ ^ 2 := by
    have hi : Integrable (fun x => ‖a x‖ ^ 2) haarAddCircle :=
      (a.continuous.norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
    calc
      _ ≤ ∫ _x : AddCircle L, ‖a‖ ^ 2 ∂haarAddCircle :=
        integral_mono hi (integrable_const _) (fun x =>
          pow_le_pow_left₀ (norm_nonneg _) (a.norm_coe_le_norm x) 2)
      _ = _ := by simp
  have he := periodicH1Coordinates_norm_sq f g h
  have hs : ‖periodicH1Coordinates f g h‖ ^ 2 ≤ (‖f‖ + ‖g‖) ^ 2 := by
    nlinarith [hb f, hb g, mul_nonneg (norm_nonneg f) (norm_nonneg g)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp hs

/-- Continuous actual C1 data give continuous H1 coordinates, for any
topological parameter space. MT2007 Claim 19.1, p. 437; parametric H1
composition derivation, statement 2. -/
theorem continuous_periodicH1Coordinates {P : Type*} [TopologicalSpace P]
    (f g : P → C(AddCircle L, ℂ)) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ p (x : ℝ), HasDerivAt (fun y : ℝ => f p (y : AddCircle L))
      (g p (x : AddCircle L)) x) :
    Continuous (fun p => periodicH1Coordinates (f p) (g p) (h p)) := by
  apply continuous_iff_continuousAt.mpr
  intro p₀
  have hb (p : P) :
      ‖periodicH1Coordinates (f p) (g p) (h p) -
        periodicH1Coordinates (f p₀) (g p₀) (h p₀)‖ ≤
      ‖f p - f p₀‖ + ‖g p - g p₀‖ := by
    have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => (f p - f p₀) (y : AddCircle L))
        ((g p - g p₀) (x : AddCircle L)) x := fun x => (h p x).fun_sub (h p₀ x)
    have heq : periodicH1Coordinates (f p) (g p) (h p) -
        periodicH1Coordinates (f p₀) (g p₀) (h p₀) =
        periodicH1Coordinates (f p - f p₀) (g p - g p₀) hd := by
      apply periodicH1Decoder_injective (L := L)
      rw [map_sub, periodicH1Coordinates_reconstruct, periodicH1Coordinates_reconstruct,
        periodicH1Coordinates_reconstruct]
    rw [heq]
    exact norm_periodicH1Coordinates_le _ _ hd
  change Tendsto _ (𝓝 p₀) (𝓝 _)
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  apply squeeze_zero (fun _ => norm_nonneg _) hb
  have hc : Continuous (fun p => ‖f p - f p₀‖ + ‖g p - g p₀‖) := by fun_prop
  simpa only [sub_self, norm_zero, add_zero] using hc.tendsto p₀

end PoincareMT.M63
