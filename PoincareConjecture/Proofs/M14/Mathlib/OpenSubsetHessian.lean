import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetChart
import PoincareConjecture.Proofs.M09.LocalCenteredHessian
import PoincareConjecture.Proofs.M09.SecondDerivativeComposition

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M14

variable {n : ℕ} (U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)))

theorem openSubset_chartVectorField (x y : U) (v : EuclideanSpace ℝ (Fin n)) :
    Proofs.M09.chartVectorField x v y = v := by
  change (mfderiv (𝓡 n) (𝓡 n)
    (Subtype.val : U → EuclideanSpace ℝ (Fin n)) y).inverse v = v
  rw [Proofs.M11.mfderiv_openSubtype_val]
  change (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))).inverse v = v
  simp

theorem openSubset_secondDeriv_comp {g : RiemannianMetric n U}
    (D : LeviCivitaData g) (f : U → ℝ) (O : Set U) (hO : IsOpen O)
    (hf : ContMDiffOn (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f O)
    (y : ℝ → U) {s : ℝ} (hy : ContMDiffAt (𝓘(ℝ, ℝ)) (𝓡 n) ∞ y s)
    (hp : y s ∈ O) :
    deriv (deriv (fun r => f (y r))) s =
      D.hessian f (y s) (deriv (fun r => (y r).val) s) (deriv (fun r => (y r).val) s) +
        mvfderiv (𝓡 n) f (y s)
          (deriv (deriv (fun r => (y r).val)) s +
            (show EuclideanSpace ℝ (Fin n) from
              D.connection (fun _ : U => deriv (fun r => (y r).val) s) (y s)
                (deriv (fun r => (y r).val) s))) := by
  let p := y s
  let e := chartAt (EuclideanSpace ℝ (Fin n)) p
  let q : ℝ → EuclideanSpace ℝ (Fin n) := fun r => (y r).val
  let φ : EuclideanSpace ℝ (Fin n) → ℝ := fun z => f (e.symm z)
  have hφ : ContDiffAt ℝ ∞ φ p.val := by
    have he : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm p.val :=
      contMDiffOn_chart_symm.contMDiffAt (e.open_target.mem_nhds (by
        rw [U.chartAt_target_eq]
        exact p.property))
    have hp' : e.symm p.val ∈ O := by
      rw [U.chartAt_symm_apply_val]
      exact hp
    exact ((hf.contMDiffAt (hO.mem_nhds hp')).comp p.val he).contDiffAt
  have hq : ContDiffAt ℝ ∞ q s := (contMDiff_subtype_val.contMDiffAt.comp s hy).contDiffAt
  have heq : f =ᶠ[𝓝 p] (fun z => φ (e z)) := Eventually.of_forall (fun z => by
    dsimp only [φ, e]
    rw [U.chartAt_apply_eq_val, U.chartAt_symm_apply_val])
  have hfirst (v : EuclideanSpace ℝ (Fin n)) :
      mvfderiv (𝓡 n) f p v = fderiv ℝ φ p.val v :=
    Proofs.M09.mvfderiv_centeredChart_of_eventuallyEq p f φ
      (hφ.differentiableAt (by simp)) heq v
  have hH := Proofs.M09.hessian_centeredCoordinates_local D f p O hO hp hf
    (deriv q s) (deriv q s)
  have hconst : Proofs.M09.chartVectorField p (deriv q s) =
      fun _ : U => deriv q s := funext (fun z => openSubset_chartVectorField U p z _)
  have hDφ := ((hφ.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have heval : fderiv ℝ (fun z => fderiv ℝ φ z (deriv q s)) p.val (deriv q s) =
      fderiv ℝ (fderiv ℝ φ) p.val (deriv q s) (deriv q s) := by
    simpa using congrArg (fun L => L (deriv q s))
      (hDφ.clm_apply (hasFDerivAt_const (deriv q s) p.val)).fderiv
  change D.hessian f p (deriv q s) (deriv q s) =
    fderiv ℝ (fun z => fderiv ℝ φ z (deriv q s)) p.val (deriv q s) -
      fderiv ℝ φ p.val (D.connection (Proofs.M09.chartVectorField p (deriv q s)) p
        (deriv q s)) at hH
  rw [heval, hconst] at hH
  have hcomp : (fun r => f (y r)) = fun r => φ (q r) := funext (fun r => by
    dsimp only [φ, q, e]
    rw [U.chartAt_symm_apply_val])
  rw [hcomp, Proofs.M09.secondDeriv_comp φ q s hφ hq]
  change _ = D.hessian f p (deriv q s) (deriv q s) +
    mvfderiv (𝓡 n) f p (deriv (deriv q) s + (show EuclideanSpace ℝ (Fin n) from
      D.connection (fun _ : U => deriv q s) p (deriv q s)))
  rw [hH, hfirst, map_add]
  ring

end PoincareConjecture.M14
