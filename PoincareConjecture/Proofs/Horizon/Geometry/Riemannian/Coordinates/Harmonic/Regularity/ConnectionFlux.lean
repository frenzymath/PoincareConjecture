import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Euclidean
import Mathlib.Analysis.InnerProductSpace.Trace









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}


def connectionFlux (D : LeviCivitaData g)
    (V Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  (g.euclideanCoefficients x).inverse
    ((g.euclideanCoefficients x (Z x)).comp (D.connection V x))


theorem inner_connectionFlux (D : LeviCivitaData g)
    (V Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (x w : EuclideanSpace ℝ (Fin n)) :
    g.inner x (D.connectionFlux V Z x) w = g.inner x (D.connection V x w) (Z x) := by
  have h := congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L w)
    ((g.inner_isInvertible x).self_apply_inverse
      ((g.inner x (Z x)).comp (D.connection V x)))
  change g.inner x (D.connectionFlux V Z x) w = g.inner x (Z x) (D.connection V x w) at h
  exact h.trans (g.symm x _ _)


theorem contDiff_connectionFlux (D : LeviCivitaData g)
    {V Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hV : ContDiff ℝ ∞ V) (hZ : ContDiff ℝ ∞ Z) :
    ContDiff ℝ ∞ (D.connectionFlux V Z) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  have hG := g.contDiffAt_euclideanCoefficients x
  have hginv : (g.euclideanCoefficients x).IsInvertible := g.inner_isInvertible x
  have hinv := (hginv.contDiffAt_map_inverse (n := ∞)).comp x hG
  apply hinv.clm_apply
  apply contMDiffAt_iff_contDiffAt.mp
  apply PoincareConjecture.contMDiffAt_clm_of_apply
  intro v
  have hconst : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) v) x :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mpr contDiffAt_const
  have hVs : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) (V y)) x :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mpr hV.contDiffAt
  have hN := D.contMDiffAt_covariantDerivativeOnFields hconst hVs
  have hNv := contMDiffAt_vectorSpace_iff_contDiffAt.mp hN
  exact ((hG.clm_apply hZ.contDiffAt).clm_apply hNv).contMDiffAt


theorem connectionFlux_eq_zero_of_eq_zero (D : LeviCivitaData g)
    (V Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {x : EuclideanSpace ℝ (Fin n)} (hZ : Z x = 0) : D.connectionFlux V Z x = 0 := by
  simp [connectionFlux, hZ]


theorem hasCompactSupport_connectionFlux (D : LeviCivitaData g)
    (V : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hZ : HasCompactSupport Z) : HasCompactSupport (D.connectionFlux V Z) := by
  apply HasCompactSupport.of_support_subset_isCompact hZ
  intro x hx
  by_contra hn
  exact hx (D.connectionFlux_eq_zero_of_eq_zero V Z (image_eq_zero_of_notMem_tsupport hn))



theorem trace_connectionFlux (D : LeviCivitaData g)
    {V Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hV : ContDiff ℝ ∞ V) (hZ : ContDiff ℝ ∞ Z) (x : EuclideanSpace ℝ (Fin n)) :
    let b := g.orthonormalBasis x
    let E := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
    LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
      (D.connection (D.connectionFlux V Z) x).toLinearMap =
      ∑ i, (g.inner x
        (D.connection (D.covariantDerivativeOnFields (E i) V) x (b i) -
          D.connection V x (D.connection (E i) x (b i))) (Z x) +
        g.inner x (D.connection V x (b i)) (D.connection Z x (b i))) := by
  let b := g.orthonormalBasis x
  let E := fun i => FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (b i)
  let F := D.connectionFlux V Z
  have hVs : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) (V y)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hV
  have hZs : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) (Z y)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hZ
  have hFs : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      ∞ (fun y => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) y
        (E := TangentSpace (𝓡 n)) (F y)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr (D.contDiff_connectionFlux hV hZ)
  have hterm (i) : g.inner x (D.connection F x (b i)) (b i) =
      g.inner x
        (D.connection (D.covariantDerivativeOnFields (E i) V) x (b i) -
          D.connection V x (D.connection (E i) x (b i))) (Z x) +
        g.inner x (D.connection V x (b i)) (D.connection Z x (b i)) := by
    have hE : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        ∞ (T% (E i)) x := FiberBundle.contMDiffAt_extend (𝓡 n)
          (EuclideanSpace ℝ (Fin n)) (b i)
    have hN := D.contMDiffAt_covariantDerivativeOnFields hE (hVs x)
    have hleft := D.horizon_mvfderiv_inner (E i) ((hFs x).mdifferentiableAt (by simp))
      (hE.mdifferentiableAt (by simp))
    have hright := D.horizon_mvfderiv_inner (E i) (hN.mdifferentiableAt (by simp))
      ((hZs x).mdifferentiableAt (by simp))
    have hdual : (fun y => g.inner y (F y) (E i y)) =
        fun y => g.inner y (D.covariantDerivativeOnFields (E i) V y) (Z y) := by
      funext y
      exact D.inner_connectionFlux V Z y (E i y)
    rw [hdual, hright] at hleft
    simp only [covariantDerivativeOnFields, E, FiberBundle.extend_apply_self] at hleft
    rw [D.inner_connectionFlux] at hleft
    simp only [map_sub, sub_apply]
    exact (eq_sub_iff_add_eq.mpr hleft.symm).trans (by ring)
  let : Bundle.RiemannianBundle
      (TangentSpace (𝓡 n) : EuclideanSpace ℝ (Fin n) → Type _) :=
    ⟨g.toRiemannianMetric⟩
  dsimp only
  change LinearMap.trace ℝ (TangentSpace (𝓡 n) x) (D.connection F x).toLinearMap = _
  rw [LinearMap.trace_eq_sum_inner _ (g.orthonormalBasis x)]
  apply Finset.sum_congr rfl
  intro i _
  change g.inner x (b i) (D.connection F x (b i)) = _
  rw [g.symm]
  exact hterm i

end PoincareConjecture.LeviCivitaData
