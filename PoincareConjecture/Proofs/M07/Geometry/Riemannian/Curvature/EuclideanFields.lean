import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.EuclideanNorm
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module









set_option autoImplicit false
set_option maxSynthPendingDepth 12
open scoped Manifold ContDiff Bundle Topology
open Filter Bundle VectorField

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private noncomputable def connectionBilinear (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap {
    toFun := fun u => LinearMap.toContinuousLinearMap {
      toFun := fun v => D.euclideanConnection u v x
      map_add' := fun v w => congrFun (D.euclideanConnection_add_right u v w) x
      map_smul' := fun c v => congrFun (D.euclideanConnection_smul_right c u v) x }
    map_add' := fun u v => by
      apply ContinuousLinearMap.ext
      intro w
      exact congrFun (D.euclideanConnection_add_left u v w) x
    map_smul' := fun c u => by
      apply ContinuousLinearMap.ext
      intro w
      exact congrFun (D.euclideanConnection_smul_left c u w) x }

private theorem connectionBilinear_apply (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    D.connectionBilinear x u v = D.euclideanConnection u v x := rfl

private theorem contDiff_connectionBilinear (D : LeviCivitaData g) :
    ContDiff ℝ ∞ D.connectionBilinear := by
  apply contDiff_clm_apply_iff.mpr
  intro u
  apply contDiff_clm_apply_iff.mpr
  intro v
  exact contDiff_iff_contDiffAt.mpr fun x => D.contDiffAt_euclideanConnection x u v

private theorem connection_eventually_eq (D : LeviCivitaData g)
    {Y Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)} (hZ : ContDiffAt ℝ ∞ Z x) :
    (fun y => D.connection Z y (Y y)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ Z y (Y y) + D.connectionBilinear y (Y y) (Z y)) := by
  filter_upwards [(hZ.of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).eventually (by simp)] with y hy
  exact D.connection_eq_fderiv_add (hy.differentiableAt (by simp)) (Y y)

private theorem differentiableAt_connectionOnFields (D : LeviCivitaData g)
    {Y Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hY : ContDiffAt ℝ ∞ Y x) (hZ : ContDiffAt ℝ ∞ Z x) :
    DifferentiableAt ℝ (fun y => D.connection Z y (Y y)) x := by
  have hdZ : ContDiffAt ℝ ∞ (fderiv ℝ Z) x := hZ.fderiv_right (by simp)
  have h := (hdZ.clm_apply hY).add
    ((D.contDiff_connectionBilinear.contDiffAt.clm_apply hY).clm_apply hZ)
  exact (h.differentiableAt (by simp)).congr_of_eventuallyEq
    (D.connection_eventually_eq hZ)

private theorem fderiv_connectionOnFields (D : LeviCivitaData g)
    {Y Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hY : ContDiffAt ℝ ∞ Y x) (hZ : ContDiffAt ℝ ∞ Z x)
    (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => D.connection Z y (Y y)) x v =
      fderiv ℝ Z x (fderiv ℝ Y x v) +
        fderiv ℝ (fderiv ℝ Z) x v (Y x) +
      (D.connectionBilinear x (Y x) (fderiv ℝ Z x v) +
        D.connectionBilinear x (fderiv ℝ Y x v) (Z x) +
        fderiv ℝ D.connectionBilinear x v (Y x) (Z x)) := by
  have hY' := hY.differentiableAt (by simp)
  have hZ' := hZ.differentiableAt (by simp)
  have hdZ : DifferentiableAt ℝ (fderiv ℝ Z) x :=
    (hZ.fderiv_right (show (∞ : ℕ∞ω) + 1 ≤ ∞ by simp)).differentiableAt (by simp)
  have hG : DifferentiableAt ℝ D.connectionBilinear x :=
    D.contDiff_connectionBilinear.differentiable (by simp) x
  rw [(D.connection_eventually_eq hZ).fderiv_eq,
    fderiv_fun_add (hdZ.clm_apply hY') ((hG.clm_apply hY').clm_apply hZ'),
    fderiv_clm_apply hdZ hY',
    fderiv_clm_apply (hG.clm_apply hY') hZ', fderiv_clm_apply hG hY']
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply]
  abel

private theorem fderiv_connectionBilinear_apply (D : LeviCivitaData g)
    (x u v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (D.euclideanConnection u v) x w =
      fderiv ℝ D.connectionBilinear x w u v := by
  change fderiv ℝ (fun y => D.connectionBilinear y u v) x w = _
  have hG : DifferentiableAt ℝ D.connectionBilinear x :=
    D.contDiff_connectionBilinear.differentiable (by simp) x
  rw [fderiv_clm_apply (hG.clm_apply (differentiableAt_const u)) (differentiableAt_const v),
    fderiv_clm_apply hG (differentiableAt_const u)]
  simp

set_option backward.isDefEq.respectTransparency false in


theorem curvatureOnFields_eq_curvature_euclidean (D : LeviCivitaData g)
    {X Y Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hX : ContDiffAt ℝ ∞ X x) (hY : ContDiffAt ℝ ∞ Y x)
    (hZ : ContDiffAt ℝ ∞ Z x) :
    D.curvatureOnFields X Y Z x = D.curvature x (X x) (Y x) (Z x) := by
  have hZ' := hZ.differentiableAt (by simp)
  have hb : mlieBracket (𝓡 n) X Y x =
      fderiv ℝ Y x (X x) - fderiv ℝ X x (Y x) := by
    simp only [mlieBracket, mlieBracketWithin_eq_lieBracketWithin,
      lieBracketWithin, fderivWithin_univ]
  have hs := (hZ.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)).eq (X x) (Y x)
  rw [curvature_eq_euclideanConnection]
  unfold curvatureOnFields
  rw [hb,
    D.connection_eq_fderiv_add (D.differentiableAt_connectionOnFields hY hZ),
    D.connection_eq_fderiv_add (D.differentiableAt_connectionOnFields hX hZ),
    D.connection_eq_fderiv_add hZ',
    D.fderiv_connectionOnFields hY hZ, D.fderiv_connectionOnFields hX hZ,
    D.connection_eq_fderiv_add hZ', D.connection_eq_fderiv_add hZ',
    D.fderiv_connectionBilinear_apply, D.fderiv_connectionBilinear_apply]
  simp only [← connectionBilinear_apply, map_add, map_sub, sub_apply]
  rw [hs]
  module


theorem curvatureOnFields_eq_curvature_euclidean_of_contMDiffAt (D : LeviCivitaData g)
    {X Y Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {x : EuclideanSpace ℝ (Fin n)}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) (X y)) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) (Y y)) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y => TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) (Z y)) x) :
    D.curvatureOnFields X Y Z x = D.curvature x (X x) (Y x) (Z x) := by
  apply D.curvatureOnFields_eq_curvature_euclidean
  · have h := (Bundle.contMDiffAt_totalSpace.mp hX).2
    exact contMDiffAt_iff_contDiffAt.mp (by simpa using h)
  · have h := (Bundle.contMDiffAt_totalSpace.mp hY).2
    exact contMDiffAt_iff_contDiffAt.mp (by simpa using h)
  · have h := (Bundle.contMDiffAt_totalSpace.mp hZ).2
    exact contMDiffAt_iff_contDiffAt.mp (by simpa using h)

end PoincareConjecture.LeviCivitaData
