import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Asymptotics.CylinderJetLocality
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Asymptotics.EndCylinderPatches
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Existence.Asymptotics.EndCylinderIntrinsicJets

/-!
# Intrinsic errors of the fixed centered end coordinate

A fixed centered coordinate agrees locally with any suitable translated
reference coordinate followed by an axial shift. Locality and exact
translation invariance transfer its actual frozen error. This is
Proposition 12.7, pp. 298-299 and asymptotic-certificate-patches.md.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.M34

variable {g0 : RiemannianMetric 3 StandardCapSpace}

/-- The two actual coordinate maps agree on a genuine open positive-height
neighborhood; the integer index is fixed throughout that neighborhood
(Proposition 12.7, pp. 298-299). -/
theorem endCenteredCylinderMap_eq_translated_germ (e : StandardCylindricalEnd g0)
    (j : ℕ) (H : ℝ) {z : RoundCylinderSpace} (hz : 0 < z.2 + (H - j)) :
    endCenteredCylinderMap e H =ᶠ[𝓝 z]
      (endAxialTranslation e j ∘ e.coordinate) ∘ cylinderAxialTranslation (H - j) := by
  filter_upwards [(isOpen_lt continuous_const
    (continuous_snd.add continuous_const)).mem_nhds hz] with y hy
  change e.coordinate (y.1, y.2 + H) =
    endAxialTranslation e j (e.coordinate (y.1, y.2 + (H - j)))
  rw [endAxialTranslation_coordinate e j (show 0 ≤ y.2 + (H - j) from hy.le)]
  congr 1
  apply Prod.ext
  · rfl
  · dsimp
    ring

/-- The actual pullback tensor of the fixed coordinate is locally the
axially shifted reference pullback (Proposition 12.7, pp. 298-299). -/
theorem endCenteredCylinderPullback_eq_shift (e : StandardCylindricalEnd g0)
    (j : ℕ) (H : ℝ) (g : RiemannianMetric 3 StandardCapSpace)
    {z : RoundCylinderSpace} (hz : 0 < z.2 + (H - j)) :
    roundCylinderPullback g (endCenteredCylinderMap e H) z =
      roundCylinderShift (H - j)
        (roundCylinderPullback g (endAxialTranslation e j ∘ e.coordinate)) z := by
  have hs := (endAxialTranslation_comp_coordinate_contMDiffOn e j).contMDiffAt
    ((isOpen_univ.prod isOpen_Ioi).mem_nhds
      (show cylinderAxialTranslation (H - j) z ∈ univ ×ˢ Ioi (0 : ℝ) from
        ⟨mem_univ _, hz⟩))
  exact (roundCylinderPullback_congr_of_eventuallyEq g
    (endCenteredCylinderMap_eq_translated_germ e j H hz)).trans
    (roundCylinderPullback_comp_axialTranslation g _ _ z (hs.mdifferentiableAt (by simp)))

/-- The actual scalar coefficients agree as germs in any sphere chart
at a valid positive reference height (Proposition 12.7, pp. 298-299). -/
theorem endCenteredCylinderCoefficient_eq_shift_germ (e : StandardCylindricalEnd g0)
    (j : ℕ) (H : ℝ) (g : RiemannianMetric 3 StandardCapSpace)
    (c : OpenPartialHomeomorph UnitTwoSphere (EuclideanSpace ℝ (Fin 2)))
    {p : RoundCylinderCoordinates} (hp : 0 < p.2 + (H - j)) (a b : Fin 3) :
    (fun y => roundCylinderTensorCoefficient
      (roundCylinderPullback g (endCenteredCylinderMap e H)) c y a b) =ᶠ[𝓝 p]
    (fun y => roundCylinderTensorCoefficient (roundCylinderShift (H - j)
      (roundCylinderPullback g (endAxialTranslation e j ∘ e.coordinate))) c y a b) := by
  filter_upwards [(isOpen_lt continuous_const
    (continuous_snd.add continuous_const)).mem_nhds hp] with y hy
  have h := endCenteredCylinderPullback_eq_shift e j H g
    (z := (c.symm y.1, y.2)) hy
  exact congrFun (congrFun h _) _

/-- The actual fixed-patch error equals the translated reference error
at the shifted point (Proposition 12.7, pp. 298-299). -/
theorem endCenteredCylinderJetErrorSquared_eq (e : StandardCylindricalEnd g0)
    (j : ℕ) (H : ℝ) (g : RiemannianMetric 3 StandardCapSpace)
    (t : ℝ) (m : ℕ) {z : RoundCylinderSpace} (hz : 0 < z.2 + (H - j)) :
    roundCylinderJetErrorSquared t (roundCylinderPullback g (endCenteredCylinderMap e H)) m z =
      roundCylinderJetErrorSquared t
        (roundCylinderPullback g (endAxialTranslation e j ∘ e.coordinate)) m
        (cylinderAxialTranslation (H - j) z) :=
  (roundCylinderJetErrorSquared_congr_germ t m z (fun a b =>
    endCenteredCylinderCoefficient_eq_shift_germ e j H g _ hz a b)).trans
      (roundCylinderJetErrorSquared_shift (H - j) t _ m z)

end PoincareMT.M34
