import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Pullback.PullbackReparametrization
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Variation.Euler.EulerResidual

/-!
# Square-time transport of the actual Euler expression

Morgan-Tian equation (6.2), Definition 6.7 and Lemma 6.8,
pp. 106, 108-109. Reparameterizing an actual horizontal extension
gives the regularized equation on the strict square interval for
every Euler path, without minimality or endpoint smoothness.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)

/-- The actual velocity extension transported by `t = s²`, retaining
the original common spatial domain, Lemma 6.8, pp. 108-109. -/
noncomputable def squarePullbackExtension
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity) :
    M14PullbackExtension G (fun s => p.curve (s ^ 2))
      (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
      (fun s => (2 * s) • p.horizontal_velocity (s ^ 2)) :=
  pullbackExtensionSmulComp E (fun s => s ^ 2) (fun s => 2 * s)
    (contDiff_id.pow 2) (contDiff_const.mul contDiff_id)
    (fun _ hs => ⟨Real.lt_sq_of_sqrt_lt hs.1,
      (Real.lt_sqrt ((Real.sqrt_nonneg τ₁).trans_lt hs.1).le).mp hs.2⟩)

/-- The actual square-time covariant derivative is `2 X + 4s² D X`,
the transport calculation of Lemma 6.8, pp. 108-109. -/
theorem horizontalCovariantDerivative_square
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    M14HorizontalCovariantDerivative G (fun r => p.curve (r ^ 2))
        (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
        (fun r => (2 * r) • p.horizontal_velocity (r ^ 2)) (squarePullbackExtension p E) s =
      (2 : ℝ) • p.horizontal_velocity (s ^ 2) + (4 * s ^ 2) •
        M14HorizontalCovariantDerivative G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity E
          (s ^ 2) := by
  have hmap : MapsTo (fun r : ℝ => r ^ 2) (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
      (Ioo τ₁ τ₂) := fun r hr => ⟨Real.lt_sq_of_sqrt_lt hr.1,
        (Real.lt_sqrt ((Real.sqrt_nonneg τ₁).trans_lt hr.1).le).mp hr.2⟩
  have hγ := ((p.curve_regular _ (hmap hs)).contMDiffAt
    (isOpen_Ioo.mem_nhds (hmap hs))).mdifferentiableAt (by simp)
  have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hscale : HasDerivAt (fun r : ℝ => 2 * r) 2 s := by
    simpa using (hasDerivAt_id s).const_mul 2
  have h := horizontalCovariantDerivative_smul_comp E (fun r => r ^ 2) (fun r => 2 * r)
    (contDiff_id.pow 2) (contDiff_const.mul contDiff_id) hmap hs
    (isOpen_Ioo.mem_nhds hs) (isOpen_Ioo.mem_nhds (hmap hs)) hγ
  simpa only [squarePullbackExtension, Function.comp_def, hsq.deriv, hscale.deriv,
    show 2 * s * (2 * s) = 4 * s ^ 2 by ring] using h

/-- M12's actual Ricci tensor scales in its velocity slot, as required
in the square-time Euler calculation, Lemma 6.8, pp. 108-109. -/
theorem horizontalRicci_smul_left (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : G.Point) (v w : G.Horizontal q) (c : ℝ) :
    horizontalRicci G.leafwise q (c • v) w = c * horizontalRicci G.leafwise q v w := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  rw [H.ricci_symmetric q (c • v) w, horizontalRicci_smul_right hM12,
    H.ricci_symmetric q w v]

/-- The actual regularized expression is `4s²` times the original
paired Euler residual on the strict positive interval, Lemma 6.8,
pp. 108-109. No endpoint value of the original velocity is used. -/
theorem squarePullback_eulerResidual (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    {s : ℝ} (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
    (W : G.Horizontal (p.curve (s ^ 2))) :
    G.spacetime.horizontalMetric.inner (p.curve (s ^ 2))
        (M14HorizontalCovariantDerivative G (fun r => p.curve (r ^ 2))
          (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
          (fun r => (2 * r) • p.horizontal_velocity (r ^ 2)) (squarePullbackExtension p E) s) W -
      2 * s ^ 2 * M14HorizontalScalarDifferential G (p.curve (s ^ 2)) W.val +
      4 * s * horizontalRicci G.leafwise (p.curve (s ^ 2))
        ((2 * s) • p.horizontal_velocity (s ^ 2)) W =
      (4 * s ^ 2) * M14EulerResidual G p E (s ^ 2) W := by
  have hs0 : s ≠ 0 := ((Real.sqrt_nonneg τ₁).trans_lt hs.1).ne'
  rw [horizontalCovariantDerivative_square p E hs, horizontalRicci_smul_left hM12]
  simp only [M14EulerResidual, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  field_simp [hs0]
  ring

end PoincareMT.M14
