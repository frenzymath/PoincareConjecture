import PoincareConjecture.Proofs.M14.Sec6_2_PullbackReparametrization
import PoincareConjecture.Proofs.M14.Sec6_2_EulerResidual

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)

noncomputable def squarePullbackExtension
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity) :
    M14PullbackExtension G (fun s => p.curve (s ^ 2))
      (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂))
      (fun s => (2 * s) • p.horizontal_velocity (s ^ 2)) :=
  pullbackExtensionSmulComp E (fun s => s ^ 2) (fun s => 2 * s)
    (contDiff_id.pow 2) (contDiff_const.mul contDiff_id)
    (fun _ hs => ⟨Real.lt_sq_of_sqrt_lt hs.1,
      (Real.lt_sqrt ((Real.sqrt_nonneg τ₁).trans_lt hs.1).le).mp hs.2⟩)

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

theorem horizontalRicci_smul_left (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : G.Point) (v w : G.Horizontal q) (c : ℝ) :
    horizontalRicci G.leafwise q (c • v) w = c * horizontalRicci G.leafwise q v w := by
  have H := (hM12.leafwise_calculus X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover).2 G.leafwise
  rw [H.ricci_symmetric q (c • v) w, horizontalRicci_smul_right hM12,
    H.ricci_symmetric q w v]

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

end PoincareConjecture.M14
