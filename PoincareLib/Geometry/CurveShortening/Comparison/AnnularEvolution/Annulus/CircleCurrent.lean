import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Annulus.SliceDifferential
import PoincareLib.Geometry.CurveShortening.Ramp.Approximation.Horizontal.Lift

/-!
# The actual circle current of an annular map

Pairing the two genuine source columns with the product's parallel circle
unit field gives a globally defined smooth scalar one-form. Its directional
derivatives are the corresponding covariant pairings, without choosing a
circle lift or assuming the map is unbranched.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

/-- Actual pairing with the parallel circle field differentiates by the covariant derivative
of the given tangent field alone. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary
19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64CircleProduct_pairing_circleUnit_hasDerivAt
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {gamma : ℝ → P.charts.Point} {x : ℝ}
    {Y : (s : ℝ) → TangentSpace (𝓡 (n + 1)) (gamma s)}
    (hgamma : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 (n + 1)) gamma x)
    (hY : MDifferentiableAt 𝓘(ℝ, ℝ) ((𝓡 (n + 1)).prod (𝓡 (n + 1)))
      (fun s => (⟨gamma s, Y s⟩ : TangentBundle (𝓡 (n + 1)) P.charts.Point)) x) :
    HasDerivAt (fun s => (P.flow.metric t).inner (gamma s) (Y s)
        (P.charts.circleUnit (gamma s)))
      ((P.flow.metric t).inner (gamma x)
        (rampHorizontalCovariantDerivative (P.flow.connection t) gamma Y x)
        (P.charts.circleUnit (gamma x))) x := by
  have hZ := ((M62.circleProduct_identities P).circle_unit_smooth.mdifferentiableAt
    (by simp)).comp x hgamma
  have h := M62.hasDerivAt_metric_pairing (P.flow.connection t) hgamma hY hZ
  simpa only [M63.circleUnit_pullback_zero P t hgamma, map_zero, add_zero] using h

/-- The genuine angular-circle pairing of a source column. Source: Morgan--Tian (2007),
Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
noncomputable def m64AnnulusCircleCurrent
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (f : LoopPlane → P.charts.Point) (i : Fin 2) (p : LoopPlane) : ℝ :=
  (P.flow.metric t).inner (f p)
    (mfderiv (𝓡 2) (𝓡 (n + 1)) f p (EuclideanSpace.single i 1))
    (P.charts.circleUnit (f p))

/-- Smoothness of the actual current follows from the genuine bundle metric, the
pushed-forward source vector, and the parallel circle field. Source: Morgan--Tian (2007),
Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusCircleCurrent_contDiffAt
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {f : LoopPlane → P.charts.Point} {p : LoopPlane}
    (hf : ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ f p) (i : Fin 2) :
    ContDiffAt ℝ ∞ (m64AnnulusCircleCurrent P t f i) p := by
  have hpush := m64Annulus_pushforward_contMDiffAt hf (EuclideanSpace.single i 1)
  have hcircle := (M62.circleProduct_identities P).circle_unit_smooth.contMDiffAt.comp p hf
  have h := (((P.flow.metric t).contMDiff (f p)).comp p hf).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := Bundle.Trivial P.charts.Point ℝ) hpush hcircle
  exact contMDiffAt_iff_contDiffAt.mp (Bundle.contMDiffAt_totalSpace.mp h).2

/-- The actual horizontal derivative of each current is a covariant pairing. No local lift
or harmonicity is assumed. Source: Morgan--Tian (2007), Lemma 19.15 and Corollary 19.16, pp.
447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusCircleCurrent_horizontal_derivative
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {f : LoopPlane → P.charts.Point} {x s : ℝ}
    (hf : ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ f (annulusPoint x s)) (i : Fin 2) :
    fderiv ℝ (m64AnnulusCircleCurrent P t f i) (annulusPoint x s)
        (EuclideanSpace.single (0 : Fin 2) 1) =
      (P.flow.metric t).inner (f (annulusPoint x s))
        (rampHorizontalCovariantDerivative (P.flow.connection t)
          (fun y => f (annulusPoint y s))
          (fun y => mfderiv (𝓡 2) (𝓡 (n + 1)) f (annulusPoint y s)
            (EuclideanSpace.single i 1)) x)
        (P.charts.circleUnit (f (annulusPoint x s))) := by
  have hline : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ (fun y => annulusPoint y s) x := by
    apply contMDiffAt_iff_contDiffAt.mpr
    apply (contDiffAt_piLp 2).mpr
    intro j
    fin_cases j
    · simpa [annulusPoint] using! (contDiffAt_id : ContDiffAt ℝ ∞ (id : ℝ → ℝ) x)
    · simpa [annulusPoint] using (contDiffAt_const (c := s) : ContDiffAt ℝ ∞ (fun _ : ℝ => s) x)
  have hpush := (m64Annulus_pushforward_contMDiffAt hf (EuclideanSpace.single i 1)).comp x hline
  have hpair := m64CircleProduct_pairing_circleUnit_hasDerivAt P t
    ((hf.comp x hline).mdifferentiableAt (by simp)) (hpush.mdifferentiableAt (by simp))
  have hscalar := ((m64AnnulusCircleCurrent_contDiffAt P t hf i).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt x (m64AnnulusPoint_horizontal_hasDerivAt s x)
  exact hscalar.unique hpair

/-- The analogous genuine vertical derivative of the scalar current. Source: Morgan--Tian
(2007), Lemma 19.15 and Corollary 19.16, pp. 447-449; project derivation
`proof-work/tasks/M64/reports/2026-09-27-annulus-energy-and-finite-variation-derivation.md`. -/
theorem m64AnnulusCircleCurrent_vertical_derivative
    (P : M62.CircleProductData F circumference) (t : ℝ)
    {f : LoopPlane → P.charts.Point} {x s : ℝ}
    (hf : ContMDiffAt (𝓡 2) (𝓡 (n + 1)) ∞ f (annulusPoint x s)) (i : Fin 2) :
    fderiv ℝ (m64AnnulusCircleCurrent P t f i) (annulusPoint x s)
        (EuclideanSpace.single (1 : Fin 2) 1) =
      (P.flow.metric t).inner (f (annulusPoint x s))
        (rampHorizontalCovariantDerivative (P.flow.connection t)
          (fun r => f (annulusPoint x r))
          (fun r => mfderiv (𝓡 2) (𝓡 (n + 1)) f (annulusPoint x r)
            (EuclideanSpace.single i 1)) s)
        (P.charts.circleUnit (f (annulusPoint x s))) := by
  have hline : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ (annulusPoint x) s := by
    apply contMDiffAt_iff_contDiffAt.mpr
    apply (contDiffAt_piLp 2).mpr
    intro j
    fin_cases j
    · simpa [annulusPoint] using (contDiffAt_const (c := x) : ContDiffAt ℝ ∞ (fun _ : ℝ => x) s)
    · simpa [annulusPoint] using! (contDiffAt_id : ContDiffAt ℝ ∞ (id : ℝ → ℝ) s)
  have hpush := (m64Annulus_pushforward_contMDiffAt hf (EuclideanSpace.single i 1)).comp s hline
  have hpair := m64CircleProduct_pairing_circleUnit_hasDerivAt P t
    ((hf.comp s hline).mdifferentiableAt (by simp)) (hpush.mdifferentiableAt (by simp))
  have hscalar := ((m64AnnulusCircleCurrent_contDiffAt P t hf i).differentiableAt
    (by simp)).hasFDerivAt.comp_hasDerivAt s (m64AnnulusPoint_vertical_hasDerivAt x s)
  exact hscalar.unique hpair

end PoincareMT
