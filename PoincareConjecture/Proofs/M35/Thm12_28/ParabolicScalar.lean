import PoincareConjecture.Statements.M35Providers
import PoincareConjecture.Definitions.M35StandardCapUniqueness
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Scaling










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.OrdinaryParabolicRescaling

variable {I : SpacetimeInterval} {F : RicciFlow 3 StandardCapSpace I.domain}
  {Q a : ℝ} {hQ : 0 < Q} (R : OrdinaryParabolicRescaling F Q hQ a)



theorem scalar_directional_eq (s : ℝ) (x : StandardCapSpace)
    (v : TangentSpace (𝓡 3) x) :
    mvfderiv (𝓡 3) (R.flow.connection s).scalarCurvature x v =
      mvfderiv (𝓡 3) (F.connection (parabolicTimeInv Q a s)).scalarCurvature x v / Q := by
  have hf : (R.flow.connection s).scalarCurvature = fun y =>
      Q⁻¹ * (F.connection (parabolicTimeInv Q a s)).scalarCurvature y := by
    funext y
    have h := (R.metric_calculus s).scalar_eq
      (F.connection (parabolicTimeInv Q a s)) (R.flow.connection s) y
    change (R.flow.connection s).scalarCurvature y =
      (F.connection (parabolicTimeInv Q a s)).scalarCurvature y / Q at h
    simpa only [div_eq_mul_inv, mul_comm] using h
  rw [hf, mvfderiv_const_mul]
  ring



theorem scalar_evolution_eq_of_interval (P : RicciFlowCurvatureTheory.{0})
    {T : ℝ} (hT : 0 < T)
    (hsub : Icc (0 : ℝ) T ⊆ (parabolicInterval Q hQ a I).domain)
    (x : StandardCapSpace) :
    (R.flow.connection T).laplacian (R.flow.connection T).scalarCurvature x +
        2 * (R.flow.connection T).ricciNormSq x =
      ((F.connection (parabolicTimeInv Q a T)).laplacian
          (F.connection (parabolicTimeInv Q a T)).scalarCurvature x +
        2 * (F.connection (parabolicTimeInv Q a T)).ricciNormSq x) / Q ^ 2 := by
  have hmem : T ∈ Icc (0 : ℝ) T := ⟨hT.le, le_rfl⟩
  have hmap : MapsTo (parabolicTimeInv Q a) (Icc (0 : ℝ) T) I.domain := by
    intro s hs
    exact (mem_parabolicInterval_iff Q hQ a I s).mp (hsub hs)
  have hclock : HasDerivWithinAt (parabolicTimeInv Q a) (1 / Q) (Icc (0 : ℝ) T) T :=
    (((hasDerivAt_id T).div_const Q).const_add a).hasDerivWithinAt
  have hold := P.scalar_evolution 3 StandardCapSpace I.domain F
    (parabolicTimeInv Q a T) (hmap hmem) x
  have hcomp := (hold.comp T hclock hmap).div_const Q
  have hf : (fun s => (F.connection (parabolicTimeInv Q a s)).scalarCurvature x / Q) =
      fun s => (R.flow.connection s).scalarCurvature x := by
    funext s
    exact ((R.metric_calculus s).scalar_eq
      (F.connection (parabolicTimeInv Q a s)) (R.flow.connection s) x).symm
  change HasDerivWithinAt
    (fun s => (F.connection (parabolicTimeInv Q a s)).scalarCurvature x / Q) _ _ _ at hcomp
  rw [hf] at hcomp
  have hnew := (P.scalar_evolution 3 StandardCapSpace _ R.flow T (hsub hmem) x).mono hsub
  have hud := uniqueDiffOn_Icc hT T hmem
  have heq := (hnew.derivWithin hud).symm.trans (hcomp.derivWithin hud)
  exact heq.trans (by ring)



theorem scalar_evolution_eq (P : RicciFlowCurvatureTheory.{0})
    (hsub : Icc (0 : ℝ) 1 ⊆ (parabolicInterval Q hQ a I).domain)
    (x : StandardCapSpace) :
    (R.flow.connection 1).laplacian (R.flow.connection 1).scalarCurvature x +
        2 * (R.flow.connection 1).ricciNormSq x =
      ((F.connection (parabolicTimeInv Q a 1)).laplacian
          (F.connection (parabolicTimeInv Q a 1)).scalarCurvature x +
        2 * (F.connection (parabolicTimeInv Q a 1)).ricciNormSq x) / Q ^ 2 :=
  R.scalar_evolution_eq_of_interval P zero_lt_one hsub x

end PoincareConjecture.OrdinaryParabolicRescaling
