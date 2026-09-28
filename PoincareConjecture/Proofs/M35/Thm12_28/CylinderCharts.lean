import PoincareConjecture.Proofs.M35.Thm12_28.EuclideanCylinder
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35

noncomputable def cylinderChart (q : UnitTwoSphere)
    (p : EuclideanSpace ℝ (Fin 3)) : RoundCylinderSpace :=
  ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm (cylinderCoordinateEquiv p).1,
    (cylinderCoordinateEquiv p).2)

private theorem sphere_chart_symm_smooth (q : UnitTwoSphere)
    (p : EuclideanSpace ℝ (Fin 2)) :
    ContMDiffAt (𝓡 2) (𝓡 2) ∞ (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p := by
  have hp : p ∈ (chartAt (EuclideanSpace ℝ (Fin 2)) q).target := by
    rw [sphere_chart_target]
    trivial
  exact (contMDiffOn_chart_symm (I := 𝓡 2) (n := ∞) p hp).contMDiffAt
    ((chartAt (EuclideanSpace ℝ (Fin 2)) q).open_target.mem_nhds hp)

theorem cylinderChart_contMDiff (q : UnitTwoSphere) :
    ContMDiff (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (cylinderChart q) := by
  intro p
  have hfst : ContMDiffAt (𝓡 3) (𝓡 2) ∞
      (fun p : EuclideanSpace ℝ (Fin 3) => (cylinderCoordinateEquiv p).1) p :=
    (contDiff_fst.comp cylinderCoordinateEquiv.contDiff).contDiffAt.contMDiffAt
  have hsnd : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun p : EuclideanSpace ℝ (Fin 3) => (cylinderCoordinateEquiv p).2) p :=
    (contDiff_snd.comp cylinderCoordinateEquiv.contDiff).contDiffAt.contMDiffAt
  exact ((sphere_chart_symm_smooth q _).comp p hfst).prodMk hsnd

theorem preferredCylinderChart_contMDiff (q : UnitTwoSphere) :
    ContMDiff 𝓘(ℝ, RoundCylinderCoordinates) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
      (fun p : RoundCylinderCoordinates =>
        ((chartAt (EuclideanSpace ℝ (Fin 2)) q).symm p.1, p.2)) := by
  have h := (cylinderChart_contMDiff q).comp cylinderCoordinateEquiv.symm.contDiff.contMDiff
  simpa only [cylinderChart, Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using h

theorem mfderiv_cylinderChart (q : UnitTwoSphere)
    (p v : EuclideanSpace ℝ (Fin 3)) :
    mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (cylinderChart q) p v =
      (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
        (cylinderCoordinateEquiv p).1 (cylinderCoordinateEquiv v).1,
        (cylinderCoordinateEquiv v).2) := by
  let L := (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
    cylinderCoordinateEquiv.toContinuousLinearMap
  let A := (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin 2)) ℝ).comp
    cylinderCoordinateEquiv.toContinuousLinearMap
  have hL : MDifferentiableAt (𝓡 3) (𝓡 2) L p :=
    (L.contDiff (n := ∞)).contDiffAt.contMDiffAt.mdifferentiableAt (by simp)
  have hA : MDifferentiableAt (𝓡 3) 𝓘(ℝ, ℝ) A p :=
    (A.contDiff (n := ∞)).contDiffAt.contMDiffAt.mdifferentiableAt (by simp)
  have hc := (sphere_chart_symm_smooth q (L p)).mdifferentiableAt (by simp)
  have hprod := mfderiv_prodMk (hc.comp p hL) hA
  have hcomp := mfderiv_comp p hc hL
  rw [mfderiv_eq_fderiv, L.hasFDerivAt.fderiv] at hcomp
  have heq := congrArg (fun D => D v) hprod
  rw [hcomp, mfderiv_eq_fderiv, A.hasFDerivAt.fderiv] at heq
  exact heq

theorem cylinderChart_mfderiv_invertible (q : UnitTwoSphere)
    (p : EuclideanSpace ℝ (Fin 3)) :
    (mfderiv (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) (cylinderChart q) p).IsInvertible := by
  have hp : (cylinderCoordinateEquiv p).1 ∈ (extChartAt (𝓡 2) q).target := by
    simp [sphere_chart_target]
  have hi : (mfderiv (𝓡 2) (𝓡 2) (chartAt (EuclideanSpace ℝ (Fin 2)) q).symm
      (cylinderCoordinateEquiv p).1).IsInvertible := by
    have h := isInvertible_mfderivWithin_extChartAt_symm hp
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
    exact h
  obtain ⟨e, he⟩ := hi
  refine ⟨cylinderCoordinateEquiv.trans
    (e.prodCongr (ContinuousLinearEquiv.refl ℝ ℝ)), ?_⟩
  ext v
  change (e (cylinderCoordinateEquiv v).1, (cylinderCoordinateEquiv v).2) = _
  refine Eq.trans ?_ (mfderiv_cylinderChart q p v).symm
  exact Prod.ext (congrArg (fun L => L (cylinderCoordinateEquiv v).1) he) rfl

end PoincareConjecture.M35
