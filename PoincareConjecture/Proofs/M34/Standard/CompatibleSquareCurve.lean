import PoincareConjecture.Proofs.M34.Standard.CompatibleCylinderCurve
import PoincareConjecture.Proofs.M09.VelocityRestriction










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M34

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {S : GeneralizedFlowSpacetime n X time I}
  {D : SmoothSpacetimeInterval K} {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



noncomputable def compatibleSquareCurve (e : CompatibleSpacetimeCylinder S D M)
    (T : ℝ) (alpha : ℝ → M) : ℝ → S.Point :=
  fun s => e.toSpacetime (D.realParam (T - s ^ 2), alpha s)



noncomputable def compatibleSquareHorizontal (e : CompatibleSpacetimeCylinder S D M)
    (g : SpacetimeCylinderMetric e) (T : ℝ) (alpha : ℝ → M) (s : ℝ) :
    S.Horizontal (compatibleSquareCurve e T alpha s) :=
  g.spatialTangentEquiv (D.realParam (T - s ^ 2)) (alpha s)
    (curveVelocity (n := n) alpha s)



theorem compatibleSquareCurve_time (e : CompatibleSpacetimeCylinder S D M)
    (T : ℝ) (alpha : ℝ → M) {s : ℝ} (hs : T - s ^ 2 ∈ K.domain) :
    S.timeFunction (compatibleSquareCurve e T alpha s) = T - s ^ 2 :=
  (e.time_eq _).trans (D.realParam_val hs)



theorem compatibleSquareCurve_smooth (e : CompatibleSpacetimeCylinder S D M)
    (T : ℝ) {alpha : ℝ → M} {A : Set ℝ}
    (hclock : ∀ s ∈ A, T - s ^ 2 ∈ K.domain)
    (ha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ alpha A) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (compatibleSquareCurve e T alpha) A := by
  have hc : ContMDiff (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun s : ℝ => T - s ^ 2) :=
    (contDiff_const.sub (contDiff_id.pow 2)).contMDiff
  exact e.smooth.comp_contMDiffOn
    ((D.realParam_smoothOn.comp hc.contMDiffOn hclock).prodMk ha)

set_option backward.isDefEq.respectTransparency false in



theorem compatibleSquareCurve_derivative (e : CompatibleSpacetimeCylinder S D M)
    (g : SpacetimeCylinderMetric e) (T : ℝ) {alpha : ℝ → M} {A : Set ℝ}
    (hclock : ∀ s ∈ A, T - s ^ 2 ∈ K.domain)
    {s : ℝ} (hs : s ∈ A) (hA : UniqueDiffWithinAt ℝ A s)
    (ha : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) alpha s) :
    mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) (compatibleSquareCurve e T alpha) A s 1 =
      -(2 * s) • S.timeVector (compatibleSquareCurve e T alpha s) +
        (compatibleSquareHorizontal e g T alpha s).val := by
  have hc : HasDerivWithinAt (fun r : ℝ => T - r ^ 2) (-(2 * s)) A s := by
    simpa using ((hasDerivAt_pow 2 s).const_sub T).hasDerivWithinAt
  have hd := compatibleCylinder_curve_mfderivWithin_one e g hs hA hc hclock
    ha.mdifferentiableWithinAt
  rw [mfderivWithin_eq_mfderiv hA.uniqueMDiffWithinAt ha] at hd
  convert! hd using 1

end PoincareConjecture.M34
