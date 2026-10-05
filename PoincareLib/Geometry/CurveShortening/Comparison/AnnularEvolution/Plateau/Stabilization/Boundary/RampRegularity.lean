import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Stabilization.Curve.Lift
import PoincareLib.Geometry.CurveShortening.Ramp.Slope.Ramp.InitialBounds
import PoincareLib.Geometry.CurveShortening.Ramp.CurveEstimates.Relabeling.Geometry

/-!
# Regular boundary curves for the actual stabilized ramps

The constant auxiliary-circle section retains nonzero ramp velocity.
Translation in the original boundary parameter preserves this property
and the given C2 regularity. This supplies the hypotheses of the C1
straightening chart without any boundary regularity of the annulus.
Source: MT Definition 19.12, p. 446; Morrey ICM pp. 183-185.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareMT.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

/-- The original C2 ramp, lifted to a constant auxiliary-circle section and centered at any
parameter, is a genuine regular C2 target curve. Proof expansion for Morgan-Tian (2007),
Lemma 19.15, pp. 447-449. -/
theorem auxiliaryCircle_shifted_ramp_regular
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma : ℝ → P.charts.Point)
    (hgamma : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma)
    (hramp : M63IsRampAt P gamma time) (q : Q.circle.Point) (p : ℝ) :
    let C := fun s => auxiliaryCircleSection Q q (gamma (s + p))
    ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) 2 C ∧
      ∀ s, curveVelocity (n := (n + 1) + 1) C s ≠ 0 := by
  let c := auxiliaryCircleSection Q q ∘ gamma
  have hsection : ContMDiff (𝓡 (n + 1)) (𝓡 ((n + 1) + 1)) 2
      (auxiliaryCircleSection Q q) :=
    (auxiliaryCircle_section_contMDiff Q q).of_le
      (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hc : ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) 2 c :=
    hsection.comp hgamma
  have hne (x : ℝ) : curveVelocity (n := (n + 1) + 1) c x ≠ 0 := by
    intro hz
    have h := auxiliaryCircle_curveVelocity_split Q q
      (hgamma.mdifferentiable (by norm_num) x)
    change Q.charts.split _ (curveVelocity c x) = _ at h
    rw [hz, map_zero] at h
    exact M63.ramp_immersed P hramp x (congrArg Prod.fst h).symm
  refine ⟨hc.comp (contMDiff_iff_contDiff.mpr
    (contDiff_id.add contDiff_const)), ?_⟩
  intro s
  change curveVelocity (fun y => c (y + p)) s ≠ 0
  rw [M63.curveVelocity_comp (phi := fun y : ℝ => y + p) (x := s)
    (hc.mdifferentiable (by norm_num) (s + p))
    ((hasDerivAt_id s).add_const p), one_smul]
  exact hne (s + p)

end PoincareMT.M64
