import PoincareConjecture.Proofs.M14.Sec6_4_GaugeCovariantFields
import PoincareConjecture.Proofs.M14.Sec6_4_GaugeVelocity
import PoincareConjecture.Proofs.M14.Sec6_2_PullbackCongruence

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)
  {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b} {J : Set ℝ}

theorem gaugeHorizontalField_contMDiffOn
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β J)
    {f : ℝ → EuclideanSpace ℝ (Fin n)} (hf : ContDiffOn ℝ ∞ f J) :
    ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        ((G.gaugeCover.cylinder b).toSpacetime (β s))
        ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 (f s))) J := by
  let D := G.timeIntervals.interval (G.gaugeCover.interval b)
  let U := G.gaugeCover.spatial b
  have hzero : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1).tangent ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin 1))
        (E := (TangentSpace (𝓡∂ 1) : D.Point → Type _))
        (β s).1 0) J :=
    (Bundle.contMDiff_zeroSection ℝ
      (TangentSpace (𝓡∂ 1) : D.Point → Type _)).comp_contMDiffOn
        (fun s hs => (hβ s hs).fst)
  have hsp : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n).tangent ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := (TangentSpace (𝓡 n) : U → Type _)) (β s).2 (f s)) J :=
    fun s hs => U.tangentField_contMDiffWithinAt ((hβ s hs).snd)
      (hf s hs).contMDiffWithinAt
  have hv := (contMDiff_equivTangentBundleProd_symm
    (I := 𝓡∂ 1) (M := D.Point) (I' := 𝓡 n) (M' := U) (n := ∞)).comp_contMDiffOn
      (hzero.prodMk hsp)
  have he := ((G.gaugeCover.cylinder b).smooth.contMDiff_tangentMap (m := ∞)
    (by simp)).comp_contMDiffOn hv
  have hp : ContMDiff (spacetimeModel n).tangent
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun v : TangentBundle (spacetimeModel n) G.Point =>
        Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
          (E := G.Horizontal) v.proj (G.spacetime.horizontalProjection v.proj v.2)) :=
    G.spacetime.horizontalProjection_smooth
  apply (hp.comp_contMDiffOn he).congr
  intro s hs
  change Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := G.Horizontal) _ _ =
    Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := G.Horizontal)
      ((G.gaugeCover.cylinder b).toSpacetime (β s))
      (G.spacetime.horizontalProjection _
        (mfderiv (spacetimeModel n) (spacetimeModel n)
          (G.gaugeCover.cylinder b).toSpacetime (β s) (0, f s)))
  rw [gauge_projectedDifferential b]

noncomputable def horizontalFieldOfGauge {γ : ℝ → G.Point}
    (hrec : ∀ s ∈ J, (G.gaugeCover.cylinder b).toSpacetime (β s) = γ s)
    (f : ℝ → EuclideanSpace ℝ (Fin n)) (s : ℝ) : G.Horizontal (γ s) := by
  classical
  exact if hs : s ∈ J then
    hrec s hs ▸ ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 (f s))
  else 0

private theorem horizontal_cast_heq {q r : G.Point} (h : q = r) (v : G.Horizontal q) :
    HEq (h ▸ v : G.Horizontal r) v := by
  cases h
  rfl

theorem horizontalFieldOfGauge_heq {γ : ℝ → G.Point}
    (hrec : ∀ s ∈ J, (G.gaugeCover.cylinder b).toSpacetime (β s) = γ s)
    (f : ℝ → EuclideanSpace ℝ (Fin n)) {s : ℝ} (hs : s ∈ J) :
    HEq (horizontalFieldOfGauge b hrec f s)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 (f s)) := by
  simp only [horizontalFieldOfGauge, dif_pos hs]
  exact horizontal_cast_heq (hrec s hs) _

theorem horizontalFieldOfGauge_contMDiffOn {γ : ℝ → G.Point}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β J)
    (hrec : ∀ s ∈ J, (G.gaugeCover.cylinder b).toSpacetime (β s) = γ s)
    {f : ℝ → EuclideanSpace ℝ (Fin n)} (hf : ContDiffOn ℝ ∞ f J) :
    ContMDiffOn (𝓘(ℝ, ℝ))
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun s => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (γ s) (horizontalFieldOfGauge b hrec f s)) J := by
  apply (gaugeHorizontalField_contMDiffOn b hβ hf).congr
  intro s hs
  exact Bundle.TotalSpace.ext (hrec s hs).symm (horizontalFieldOfGauge_heq b hrec f hs)

theorem horizontalCovariantDerivative_lifted_gauge
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (T : ℝ) (x₀ : G.gaugeCover.spatial b) {γ : ℝ → G.Point}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β J)
    (hrec : ∀ s ∈ J, (G.gaugeCover.cylinder b).toSpacetime (β s) = γ s)
    (hclock : ∀ s ∈ J, (β s).1.val = T - s ^ 2)
    {Y : ∀ s, G.Horizontal (γ s)} (E : M14PullbackExtension G γ J Y)
    (f : ℝ → EuclideanSpace ℝ (Fin n))
    (hY : ∀ s ∈ J,
      HEq (Y s) ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2 (f s)))
    {s : ℝ} (hs : s ∈ J) (hJ : UniqueDiffWithinAt ℝ J s) :
    HEq (M14HorizontalCovariantDerivative G γ J Y E s)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
        (derivWithin f J s + M08.closedChartConnection W.flow T x₀ J (s, (β s).2.val)
          (derivWithin (fun r => (β r).2.val) J s) (f s))) := by
  let γ' := fun r => (G.gaugeCover.cylinder b).toSpacetime (β r)
  let Y' : ∀ r, G.Horizontal (γ' r) := fun r =>
    (G.gaugeCover.metric b).spatialTangentEquiv (β r).1 (β r).2 (f r)
  have hγ : EqOn γ γ' J := fun r hr => (hrec r hr).symm
  let E' := pullbackExtensionCongrOn E hγ hY
  have hc := horizontalCovariantDerivative_gauge_chart b hCoordinates W T x₀ hclock E'
    hs hJ ((hβ s hs).mdifferentiableWithinAt (by simp))
  have hform : M14HorizontalCovariantDerivative G γ' J Y' E' s =
      (G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
        (derivWithin f J s + M08.closedChartConnection W.flow T x₀ J (s, (β s).2.val)
          (derivWithin (fun r => (β r).2.val) J s) (f s)) := by
    apply ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2).symm.injective
    simpa only [Y', ContinuousLinearEquiv.symm_apply_apply] using hc
  exact (horizontalCovariantDerivative_congrOn E hγ hY hs).trans (heq_of_eq hform)

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}
  (R : M14SquareRootPath G p)

theorem squareRootVelocity_gauge_subset
    (hJC : J ⊆ M14SqrtParameterInterval τ₁ τ₂)
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β J)
    (hrec : ∀ s ∈ J, (G.gaugeCover.cylinder b).toSpacetime (β s) = R.curve s)
    {s : ℝ} (hs : s ∈ J) (hJ : UniqueDiffWithinAt ℝ J s) :
    HEq (R.horizontal_velocity s)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β s).1 (β s).2
        (derivWithin (fun r => (β r).2.val) J s)) := by
  have hR := R.smooth.mono R.interval_subset
  have hp := gaugeCurve_projectedVelocityWithin b
    ((hβ s hs).mdifferentiableWithinAt (by simp)) hJ
  have hc := projectedCurveVelocityWithin_congrOn (G := G)
    (fun r hr => (hrec r hr).symm) hs
  have hleft : projectedCurveVelocityWithin G R.curve J s = R.horizontal_velocity s := by
    unfold projectedCurveVelocityWithin
    rw [mfderivWithin_subset hJC hJ.uniqueMDiffWithinAt
      ((hR s (hJC hs)).mdifferentiableWithinAt (by simp))]
    exact (squareRoot_horizontalVelocity_eq_projection R (hJC hs)).symm
  rw [hleft] at hc
  exact hc.trans (heq_of_eq hp)

end PoincareConjecture.M14
