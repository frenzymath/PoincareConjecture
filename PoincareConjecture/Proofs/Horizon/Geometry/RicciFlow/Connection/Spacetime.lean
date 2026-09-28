import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Connection.Regularity
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.ContDiff.SpatialDerivative
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

lemma contMDiffAt_inner_connection_fields
    (F : RicciFlow n M J) {t : ℝ} (ht : t ∈ interior J) {x : M}
    {X Y Z : (x : M) → TangentSpace (𝓡 n) x}
    (hX : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% X) x)
    (hY : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Y) x)
    (hZ : ContMDiffAt (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞ (T% Z) x) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (F.metric p.1).inner p.2
        ((F.connection p.1).connection Y p.2 (X p.2)) (Z p.2)) (t, x) := by
  have hXY := LeviCivitaData.contMDiffAt_mlieBracket hX hY
  have hYZ := LeviCivitaData.contMDiffAt_mlieBracket hY hZ
  have hZX := LeviCivitaData.contMDiffAt_mlieBracket hZ hX
  have h := (((((Poincare.Manifold.contMDiffAt_mvfderiv_spatial
    (F.contMDiffAt_inner_fields ht hY hZ) hX).add
    (Poincare.Manifold.contMDiffAt_mvfderiv_spatial
      (F.contMDiffAt_inner_fields ht hZ hX) hY)).sub
    (Poincare.Manifold.contMDiffAt_mvfderiv_spatial
      (F.contMDiffAt_inner_fields ht hX hY) hZ)).add
    (F.contMDiffAt_inner_fields ht hXY hZ)).sub
    (F.contMDiffAt_inner_fields ht hYZ hX)).add
    (F.contMDiffAt_inner_fields ht hZX hY)
  apply ((contMDiffAt_const (c := (1 / 2 : ℝ))).mul h).congr_of_eventuallyEq
  have hsnd : Tendsto (Prod.snd : ℝ × M → M) (𝓝 (t, x)) (𝓝 x) := continuousAt_snd
  filter_upwards
    [hsnd.eventually (LeviCivitaData.eventually_mdifferentiableAt_of_contMDiffAt hX),
      hsnd.eventually (LeviCivitaData.eventually_mdifferentiableAt_of_contMDiffAt hY),
      hsnd.eventually (LeviCivitaData.eventually_mdifferentiableAt_of_contMDiffAt hZ)]
    with p hpX hpY hpZ
  have hk := (F.connection p.1).koszul_identity hpX hpY hpZ
  dsimp only [LeviCivitaData.covariantDerivativeOnFields] at hk
  dsimp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  linarith

end PoincareConjecture.RicciFlow
