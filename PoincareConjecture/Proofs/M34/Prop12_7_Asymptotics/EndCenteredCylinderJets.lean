import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.CylinderJetLocality
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderPatches
import PoincareConjecture.Proofs.M34.Prop12_7_Asymptotics.EndCylinderIntrinsicJets










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M34

variable {g0 : RiemannianMetric 3 StandardCapSpace}




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

end PoincareConjecture.M34
