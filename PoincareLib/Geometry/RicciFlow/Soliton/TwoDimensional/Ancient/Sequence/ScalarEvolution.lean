import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.ScalarEvolution
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Minimum.Variation.Geometry.MetricPairBase
import PoincareLib.Geometry.RicciFlow.AncientKappa.Basic

/-!
# Scalar evolution along square-root-time curves

The actual surface scalar equation and the manifold chain rule give the
scalar derivative in the reduced-length index integration. No curvature
evolution service is required. The derivative is asserted away from the
terminal time, where the Ricci-flow equation holds on an open interval.

Morgan--Tian, Lemma 6.48, p. 130, and Claim 7.11, pp. 155--156.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.AncientKappaSolution

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]

theorem hasDerivAt_scalarCurvature_square_curve (K : AncientKappaSolution 2 M)
    {α : ℝ → M} {s : ℝ} (hs : s ≠ 0)
    (hα : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 2) α s) :
    HasDerivAt (fun r => (K.flow.connection (-(r ^ 2))).scalarCurvature (α r))
      (-2 * s * ((K.flow.connection (-(s ^ 2))).laplacian
        (K.flow.connection (-(s ^ 2))).scalarCurvature (α s) +
          (K.flow.connection (-(s ^ 2))).scalarCurvature (α s) ^ 2) +
        mvfderiv (𝓡 2) (K.flow.connection (-(s ^ 2))).scalarCurvature (α s)
          (curveVelocity α s)) s := by
  have ht : -(s ^ 2) ∈ interior (Iic (0 : ℝ)) := by
    rw [interior_Iic]
    exact neg_lt_zero.mpr (sq_pos_of_ne_zero hs)
  have hclock : HasDerivAt (fun r : ℝ => -(r ^ 2)) (-2 * s) s := by
    have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    simpa only [neg_mul, one_mul] using hsq.const_mul (-1)
  have hclockM : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
      (fun r : ℝ => -(r ^ 2)) s :=
    contMDiff_iff_contDiff.mpr ((contDiff_id.pow 2).neg) s
  have hfield := (K.flow.contMDiffAt_scalarCurvature_surface ht (α s)).comp
    (s, α s) ((hclockM.comp (s, α s) contMDiffAt_fst).prodMk contMDiffAt_snd)
  have hchain := ReducedLengthMinimum.Variation.Geometry.scalar_graph_hasDerivAt
    (fun z : ℝ × M => (K.flow.connection (-(z.1 ^ 2))).scalarCurvature z.2)
    (hfield.mdifferentiableAt (by simp)) hα
  have htime := (K.flow.hasDerivAt_scalarCurvature_surface ht (α s)).comp s hclock
  dsimp only [Function.comp_def, Prod.fst, Prod.snd] at htime hchain
  rw [htime.deriv] at hchain
  exact hchain.congr_deriv (by ring)

end PoincareMT.AncientKappaSolution
