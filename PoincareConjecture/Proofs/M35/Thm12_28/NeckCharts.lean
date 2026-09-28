import PoincareConjecture.Proofs.M35.Thm12_28.CylinderCharts
import PoincareConjecture.Definitions.Ch12.StandardCap
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients
import Mathlib.Geometry.Manifold.LocalDiffeomorph

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.StandardCylinderPatch

variable {length : ℝ} {center : StandardCapSpace}

theorem coordinate_localDiffeomorph (N : StandardCylinderPatch length center) :
    IsLocalDiffeomorphOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ N.coordinate
      (univ ×ˢ Ioo (-length) length) := by
  let P : PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace StandardCapSpace ∞ :=
    { toFun := N.coordinate
      invFun := N.inverse
      source := univ ×ˢ Ioo (-length) length
      target := N.carrier
      map_source' := fun z hz => N.coordinate_image ▸ mem_image_of_mem _ hz
      map_target' := fun x hx => ⟨mem_univ _, N.inverse_domain x hx⟩
      left_inv' := N.coordinate_left_inverse
      right_inv' := N.coordinate_right_inverse
      open_source := isOpen_univ.prod isOpen_Ioo
      open_target := N.carrier_open
      contMDiffOn_toFun := N.coordinate_smooth
      contMDiffOn_invFun := N.inverse_smooth }
  intro z
  exact ⟨P, z.property, fun _ _ => rfl⟩

theorem euclideanChart_contMDiffAt (N : StandardCylinderPatch length center)
    (q : UnitTwoSphere) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-length) length) :
    ContMDiffAt (𝓡 3) (𝓡 3) ∞ (N.coordinate ∘ M35.cylinderChart q) p := by
  have hc := (N.coordinate_localDiffeomorph
    ⟨M35.cylinderChart q p, ⟨mem_univ _, hp⟩⟩).contMDiffAt
  exact hc.comp p (M35.cylinderChart_contMDiff q p)

theorem euclideanChart_mfderiv_invertible (N : StandardCylinderPatch length center)
    (q : UnitTwoSphere) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-length) length) :
    (mfderiv (𝓡 3) (𝓡 3) (N.coordinate ∘ M35.cylinderChart q) p).IsInvertible := by
  have hc := N.coordinate_localDiffeomorph
    ⟨M35.cylinderChart q p, ⟨mem_univ _, hp⟩⟩
  have hi : (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      N.coordinate (M35.cylinderChart q p)).IsInvertible :=
    ⟨hc.mfderivToContinuousLinearEquiv (by simp), rfl⟩
  rw [mfderiv_comp p (hc.mdifferentiableAt (by simp))
    ((M35.cylinderChart_contMDiff q p).mdifferentiableAt (by simp))]
  exact hi.comp (M35.cylinderChart_mfderiv_invertible q p)

theorem euclideanChart_coefficient (N : StandardCylinderPatch length center)
    (g : RiemannianMetric 3 StandardCapSpace) (q : UnitTwoSphere)
    {p : EuclideanSpace ℝ (Fin 3)}
    (hp : (M35.cylinderCoordinateEquiv p).2 ∈ Ioo (-length) length) (a b : Fin 3) :
    g.pullbackCoefficients (N.coordinate ∘ M35.cylinderChart q) p
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b) =
      roundCylinderTensorCoefficient (roundCylinderPullback g N.coordinate)
        (chartAt (EuclideanSpace ℝ (Fin 2)) q) (M35.cylinderCoordinateEquiv p) a b := by
  have hc := (N.coordinate_localDiffeomorph
    ⟨M35.cylinderChart q p, ⟨mem_univ _, hp⟩⟩).mdifferentiableAt (by simp)
  have hd := (M35.cylinderChart_contMDiff q p).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp p hc hd
  have hv (i : Fin 3) :
      mfderiv (𝓡 3) (𝓡 3) (N.coordinate ∘ M35.cylinderChart q) p
        (EuclideanSpace.basisFun (Fin 3) ℝ i) =
      mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate (M35.cylinderChart q p)
        (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
          (M35.cylinderCoordinateEquiv p).1 (roundCylinderCoordinateBasis i).1,
          (roundCylinderCoordinateBasis i).2) := by
    have hchart := M35.mfderiv_cylinderChart q p (EuclideanSpace.basisFun (Fin 3) ℝ i)
    rw [M35.cylinderCoordinateEquiv_basis] at hchart
    refine Eq.trans (congrArg (fun L => L (EuclideanSpace.basisFun (Fin 3) ℝ i)) hcomp) ?_
    exact congrArg
      (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.coordinate (M35.cylinderChart q p)) hchart
  exact congrArg₂ (fun v w => g.inner (N.coordinate (M35.cylinderChart q p)) v w) (hv a) (hv b)

end PoincareConjecture.StandardCylinderPatch
