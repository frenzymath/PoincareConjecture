import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.CurveLift
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.RampInitialBounds
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

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

end PoincareConjecture.M64
