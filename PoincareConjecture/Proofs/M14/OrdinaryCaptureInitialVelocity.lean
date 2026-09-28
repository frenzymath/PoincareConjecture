import PoincareConjecture.Proofs.M14.OrdinaryCaptureClock
import PoincareConjecture.Proofs.M14.OrdinaryCaptureVelocity
import PoincareConjecture.Proofs.M09.InitialVectorIdentification











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {C : Type v} [TopologicalSpace C]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) C] [IsManifold (𝓡 n) ∞ C]
  {K : SpacetimeInterval}
  (e : CompatibleSpacetimeCylinder G.spacetime (G.timeIntervals.interval K) C)
  (g : SpacetimeCylinderMetric e)

private theorem capture_spatial_tangent_heq
    {t r : (G.timeIntervals.interval K).Point} {c d : C}
    (ht : t = r) (hc : c = d)
    {v : TangentSpace (𝓡 n) c} {w : TangentSpace (𝓡 n) d}
    (hv : (show EuclideanSpace ℝ (Fin n) from v) = w) :
    HEq (g.spatialTangentEquiv t c v) (g.spatialTangentEquiv r d w) := by
  cases ht
  cases hc
  exact heq_of_eq (congrArg (g.spatialTangentEquiv t c) hv)



theorem ordinaryCapture_square_initial_velocity_of_eqOn
    (t₀ : (G.timeIntervals.interval K).Point) (c₀ : C)
    {F : RicciFlow n C K.domain} {τmax τ : ℝ} {y : G.Point}
    (A : LExponentialFamily F t₀.val τmax c₀)
    (W : TangentSpace (𝓡 n) c₀)
    (p : M14BackwardPath G t₀.val 0 τ (e.toSpacetime (t₀, c₀)) y)
    (R : M14SquareRootPath G p) (hmax : τ < τmax)
    (θ : ℝ → (G.timeIntervals.interval K).Point) (hθ₀ : θ 0 = t₀)
    (hθ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (𝓡∂ 1) θ
      (M14SqrtParameterInterval 0 τ) 0)
    (heq : EqOn R.curve (fun s => e.toSpacetime (θ s, A.squareFamily W s))
      (M14SqrtParameterInterval 0 τ)) :
    ∃ h : R.curve 0 = e.toSpacetime (t₀, c₀),
      h ▸ R.horizontal_velocity 0 = (2 : ℝ) • g.spatialTangentEquiv t₀ c₀ W := by
  have hτ : 0 < τ := p.tau_lt
  have hroot : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hzero : (0 : ℝ) ∈ M14SqrtParameterInterval 0 τ := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using
      (show (0 : ℝ) ∈ Icc 0 (Real.sqrt τ) from ⟨le_rfl, hroot.le⟩)
  have hdiff : UniqueDiffWithinAt ℝ (M14SqrtParameterInterval 0 τ) 0 := by
    simpa only [M14SqrtParameterInterval, Real.sqrt_zero] using
      uniqueDiffOn_Icc hroot 0 ⟨le_rfl, hroot.le⟩
  have hA := (Proofs.M09.lExponentialFamily_squareSlice_contMDiffAt A W 0
    ⟨le_rfl, Real.sqrt_pos.mpr (hτ.trans hmax)⟩).mdifferentiableAt (by simp)
  have hv : (show EuclideanSpace ℝ (Fin n) from
      curveVelocityWithin (A.squareFamily W) (M14SqrtParameterInterval 0 τ) 0) =
      (2 : ℝ) • W := by
    unfold curveVelocityWithin
    rw [mfderivWithin_eq_mfderiv hdiff.uniqueMDiffWithinAt hA]
    exact Proofs.M09.lExponentialFamily_initial_velocity A W
  have hcyl := ordinaryCapture_cylinderVelocityWithin e g θ (A.squareFamily W)
    hθ hA.mdifferentiableWithinAt hdiff
  have hsp := capture_spatial_tangent_heq e g hθ₀ (A.square_at_zero W) hv
  have hvel : HEq (R.horizontal_velocity 0)
      ((2 : ℝ) • g.spatialTangentEquiv t₀ c₀ W) :=
    (heq_of_eq (squareRoot_horizontalVelocity_eq_projection R hzero)).trans
      ((projectedCurveVelocityWithin_congrOn heq hzero).trans
        ((heq_of_eq hcyl).trans (hsp.trans
          (heq_of_eq ((g.spatialTangentEquiv t₀ c₀).map_smul (2 : ℝ) W)))))
  have hbase : R.curve 0 = e.toSpacetime (t₀, c₀) := by
    simpa only [hθ₀, A.square_at_zero] using heq hzero
  exact ⟨hbase, eq_of_heq ((eqRec_heq hbase (R.horizontal_velocity 0)).trans hvel)⟩

end PoincareConjecture.M14
