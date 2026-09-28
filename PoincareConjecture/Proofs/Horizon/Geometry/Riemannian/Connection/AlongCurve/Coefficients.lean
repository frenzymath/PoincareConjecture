import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.EuclideanNorm
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Geodesic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension









noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


def connectionCoefficient (D : LeviCivitaData g) (x : EuclideanSpace ℝ (Fin n)) :
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

theorem connectionCoefficient_apply (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    D.connectionCoefficient x u v = D.euclideanConnection u v x := rfl

theorem connectionCoefficient_eq_coordinateChristoffel (D : LeviCivitaData g)
    (x u v : EuclideanSpace ℝ (Fin n)) :
    D.connectionCoefficient x u v = coordinateChristoffel g.euclideanCoefficients x u v :=
  D.connection_const_eq_inverse x u v

theorem contDiff_connectionCoefficient (D : LeviCivitaData g) :
    ContDiff ℝ ∞ D.connectionCoefficient := by
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
  simp at hh
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
      g.inner x (D.connection (fun _ => v) x u) w +
        g.inner x v (D.connection (fun _ => w) x u) := by
  have huv := D.inner_connection_const x u v w
  have huw := D.inner_connection_const x u w v
  rw [fderiv_metric_apply, fderiv_metric_apply, fderiv_metric_apply] at huv huw
  rw [fderiv_metric_symm x w v u, fderiv_metric_symm x v u w,
    fderiv_metric_symm x u w v] at huw
  rw [g.symm x v]
  linarith


def parallelCoefficient (D : LeviCivitaData g)
    (q : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  -(D.connectionCoefficient (q t) (deriv q t))

theorem parallelCoefficient_apply (D : LeviCivitaData g)
    (q : ℝ → EuclideanSpace ℝ (Fin n)) (t : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    D.parallelCoefficient q t v =
      -coordinateChristoffel g.euclideanCoefficients (q t) (deriv q t) v := by
  simp only [parallelCoefficient, ContinuousLinearMap.neg_apply,
    connectionCoefficient_eq_coordinateChristoffel]

theorem contDiffOn_parallelCoefficient (D : LeviCivitaData g)
    {q : ℝ → EuclideanSpace ℝ (Fin n)} {I : Set ℝ}
    (hI : IsOpen I) (hq : ContDiffOn ℝ ∞ q I) :
    ContDiffOn ℝ ∞ (D.parallelCoefficient q) I := by
  exact ((D.contDiff_connectionCoefficient.comp_contDiffOn hq).clm_apply
    (hq.deriv_of_isOpen hI (by simp))).neg


theorem hasDerivAt_metricAlong {q : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hq : DifferentiableAt ℝ q t) :
    HasDerivAt (fun s => g.euclideanCoefficients (q s))
      (fderiv ℝ g.euclideanCoefficients (q t) (deriv q t)) t :=
  ((g.contDiffAt_euclideanCoefficients (q t)).differentiableAt (by simp)).hasFDerivAt
    |>.comp_hasDerivAt t hq.hasDerivAt

theorem deriv_metricAlong_apply (D : LeviCivitaData g)
    {q : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ} (hq : DifferentiableAt ℝ q t)
    (v w : EuclideanSpace ℝ (Fin n)) :
    deriv (fun s => g.euclideanCoefficients (q s)) t v w =
      (g.euclideanCoefficients (q t)) (D.euclideanConnection (deriv q t) v (q t)) w +
        (g.euclideanCoefficients (q t)) v (D.euclideanConnection (deriv q t) w (q t)) := by
  rw [(hasDerivAt_metricAlong hq).deriv]
  exact D.connectionCoefficient_metricCompatible (q t) (deriv q t) v w


theorem parallelCoefficient_metricCompatible (D : LeviCivitaData g)
    {q : ℝ → EuclideanSpace ℝ (Fin n)} {t : ℝ} (hq : DifferentiableAt ℝ q t)
    (v w : EuclideanSpace ℝ (Fin n)) :
    deriv (fun s => g.euclideanCoefficients (q s)) t v w +
      (g.euclideanCoefficients (q t)) (D.parallelCoefficient q t v) w +
      (g.euclideanCoefficients (q t)) v (D.parallelCoefficient q t w) = 0 := by
  rw [D.deriv_metricAlong_apply hq]
  simp only [parallelCoefficient, ContinuousLinearMap.neg_apply]
  rw [D.connectionCoefficient_apply, D.connectionCoefficient_apply]
  simp only [map_neg, neg_apply]
  ring

end PoincareConjecture.LeviCivitaData
