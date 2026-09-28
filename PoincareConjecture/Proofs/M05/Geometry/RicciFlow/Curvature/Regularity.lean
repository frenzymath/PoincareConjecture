
import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Connection.Regularity
import PoincareConjecture.Proofs.M05.Geometry.Manifold.ContDiff.TimeDerivative
import PoincareConjecture.Statements.Ch04.CurvatureTheory
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.Structures



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology
open Bundle Filter Set

universe u

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}







theorem contMDiffAt_ricci_fields
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {x : M}
    {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (hX : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M =>
        (F.connection p.1).ricci p.2 (X p.2) (Y p.2)) (t, x) := by
  have hmetric := F.contMDiffAt_inner_fields ht hX hY
  have hderiv := Poincare.Manifold.contMDiffAt_deriv_time hmetric
  have heq :
      (fun p : ℝ × M => deriv (fun s =>
        (F.metric s).inner p.2 (X p.2) (Y p.2)) p.1) =ᶠ[𝓝 (t, x)]
      (fun p : ℝ × M => -2 *
        (F.connection p.1).ricci p.2 (X p.2) (Y p.2)) := by
    have htime : ∀ᶠ s in 𝓝 t, s ∈ interior J :=
      isOpen_interior.mem_nhds ht
    have hprod : ∀ᶠ p : ℝ × M in 𝓝 (t, x), p.1 ∈ interior J := by
      filter_upwards [(continuousAt_fst : ContinuousAt Prod.fst (t, x)).eventually htime]
        with p hp
      exact hp
    filter_upwards [hprod] with p hp
    exact (F.equation p.1 (interior_subset hp) p.2 (X p.2) (Y p.2)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp hp) |>.deriv
  have heq' :
      (fun p : ℝ × M => deriv (fun s =>
        (F.metric (s, p.2).1).inner (s, p.2).2 (X (s, p.2).2) (Y (s, p.2).2)) p.1) =ᶠ[𝓝 (t, x)]
      (fun p : ℝ × M => -2 *
        (F.connection p.1).ricci p.2 (X p.2) (Y p.2)) := by
    simpa only [Prod.fst, Prod.snd] using heq
  have hderiv' := hderiv.congr_of_eventuallyEq heq'.symm
  have hscale := hderiv'.div_const (-2 : ℝ)
  convert hscale using 1 <;> ext p <;> ring



theorem hasDerivAt_mvfderiv_ricci_fields
    (hC : RicciFlowCurvatureTheory.{u})
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {x : M}
    {X Y : (y : M) → TangentSpace (𝓡 n) y}
    (hX : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (v : TangentSpace (𝓡 n) x) :
    HasDerivAt (fun s => mvfderiv (𝓡 n)
      (fun y => (F.connection s).ricci y (X y) (Y y)) x v)
      (mvfderiv (𝓡 n) (fun y =>
        (F.connection t).tensorLaplacian (F.connection t).ricciEvaluation y
            ![X y, Y y] + (F.connection t).ricciReaction y (X y) (Y y)) x v) t := by
  apply Poincare.Manifold.hasDerivAt_mvfderiv_time
    (contMDiffAt_ricci_fields F ht hX hY)
  · intro y
    exact (hC.ricci_evolution n M J F t (interior_subset ht) y (X y) (Y y)).hasDerivAt
      (mem_interior_iff_mem_nhds.mp ht)

end PoincareConjecture.RicciFlow
