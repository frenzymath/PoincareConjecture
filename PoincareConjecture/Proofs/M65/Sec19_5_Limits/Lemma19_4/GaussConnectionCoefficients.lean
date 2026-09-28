import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Curvature.Euclidean
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension










noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Manifold Bundle Topology

namespace PoincareConjecture.M65Gauss

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}



def connectionCoefficient (D : LeviCivitaData g) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) := by
  have hc (w : EuclideanSpace ℝ (Fin n)) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
        (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
          (E := TangentSpace (𝓡 n)) w) x := by
    rw [mdifferentiableAt_totalSpace]
    exact ⟨mdifferentiableAt_id, by simpa using
      (mdifferentiableAt_const (I := 𝓡 n) (I' := 𝓡 n) (c := w) (x := x))⟩
  exact LinearMap.toContinuousLinearMap {
    toFun := fun u => LinearMap.toContinuousLinearMap {
      toFun := fun v => D.euclideanConnection u v x
      map_add' := fun v w => congrArg (fun A => A u)
        (D.connection.isCovariantDerivativeOnUniv.add (hc v) (hc w))
      map_smul' := fun c v => congrArg (fun A => A u)
        (D.connection.isCovariantDerivativeOnUniv.smul_const c (hc v)) }
    map_add' := fun u v => by
      apply ContinuousLinearMap.ext
      intro w
      exact (D.connection (fun _ => w) x).map_add u v
    map_smul' := fun c u => by
      apply ContinuousLinearMap.ext
      intro w
      exact (D.connection (fun _ => w) x).map_smul c u }



theorem connectionCoefficient_apply (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    connectionCoefficient D x u v = D.euclideanConnection u v x := rfl



theorem contDiff_connectionCoefficient (D : LeviCivitaData g) :
    ContDiff ℝ ∞ (connectionCoefficient D) := by
  apply contDiff_clm_apply_iff.mpr
  intro u
  apply contDiff_clm_apply_iff.mpr
  intro v
  exact contDiff_iff_contDiffAt.mpr fun x => D.contDiffAt_euclideanConnection x u v



private theorem fderiv_metric_apply (x a b c : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (fun y => g.inner y a b) x c =
      fderiv ℝ g.euclideanCoefficients x c a b := by
  have hG := ((g.contDiffAt_euclideanCoefficients x).differentiableAt (by simp)).hasFDerivAt
  have h := (hG.clm_apply (hasFDerivAt_const a x)).clm_apply (hasFDerivAt_const b x)
  have hh := congrArg (fun L => L c) h.fderiv
  simp only [ContinuousLinearMap.comp_zero, zero_add, ContinuousLinearMap.flip_apply] at hh
  convert! hh using 1



private theorem fderiv_metric_symm (x a b c : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ g.euclideanCoefficients x c a b =
      fderiv ℝ g.euclideanCoefficients x c b a := by
  rw [← fderiv_metric_apply, ← fderiv_metric_apply]
  congr 2
  ext y
  exact g.symm y a b



theorem connectionCoefficient_metricCompatible (D : LeviCivitaData g)
    (x u v w : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ g.euclideanCoefficients x u v w =
      g.inner x (connectionCoefficient D x u v) w +
        g.inner x v (connectionCoefficient D x u w) := by
  have huv := D.inner_connection_const x u v w
  have huw := D.inner_connection_const x u w v
  rw [fderiv_metric_apply, fderiv_metric_apply, fderiv_metric_apply] at huv huw
  rw [fderiv_metric_symm x w v u, fderiv_metric_symm x v u w,
    fderiv_metric_symm x u w v] at huw
  rw [g.symm x v]
  change fderiv ℝ g.euclideanCoefficients x u v w =
    g.inner x (D.connection (fun _ => v) x u) w +
      g.inner x (D.connection (fun _ => w) x u) v
  linarith



theorem connectionCoefficient_symm (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    connectionCoefficient D x u v = connectionCoefficient D x v u := by
  have hc (w : EuclideanSpace ℝ (Fin n)) :
      MDifferentiableAt (𝓡 n) ((𝓡 n).prod (𝓡 n))
        (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
          (E := TangentSpace (𝓡 n)) w) x := by
    rw [mdifferentiableAt_totalSpace]
    exact ⟨mdifferentiableAt_id, by simpa using
      (mdifferentiableAt_const (I := 𝓡 n) (I' := 𝓡 n) (c := w) (x := x))⟩
  have ht := D.covariantDerivativeOnFields_sub_swap (hc u) (hc v)
  change connectionCoefficient D x u v - connectionCoefficient D x v u = _ at ht
  simp only [VectorField.mlieBracket, VectorField.mlieBracketWithin_eq_lieBracketWithin,
    VectorField.lieBracketWithin, fderivWithin_univ, fderiv_const_apply,
    zero_apply, sub_self] at ht
  exact sub_eq_zero.mp ht

end PoincareConjecture.M65Gauss
