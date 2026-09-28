import PoincareConjecture.Proofs.M14.Sec6_3_CornerVariationMinimum
import PoincareConjecture.Proofs.M14.Sec6_3_ActionFirstVariation
import PoincareConjecture.Proofs.M14.Sec6_4_FixedEndpointBoundary

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T a b c : ℝ} {x y : G.Point}

private theorem left_variationField_eq_zero {p : M14BackwardPath G T a b x y}
    {R : M14SquareRootPath G p} (V : M14LVariationData G p R)
    (hleft : V.left_endpoint_fixed) : M14VariationField V (Real.sqrt a) = 0 := by
  have hs : Real.sqrt a ∈ M14SqrtParameterInterval a b :=
    ⟨le_rfl, Real.sqrt_le_sqrt p.tau_lt.le⟩
  have heq (u : ℝ) (hu : u ∈ V.parameterDomain) :
      V.squareFamily (Real.sqrt a) u = R.curve (Real.sqrt a) := by
    rw [V.square_agrees _ hs u hu, Real.sq_sqrt p.tau_nonneg,
      V.left_endpoint_fixed_spec.mp hleft u hu, R.agrees _ hs, Real.sq_sqrt p.tau_nonneg]
  apply variationField_eq_zero_of_constant V
  intro u hu
  exact (heq u hu).trans (V.square_base _).symm

theorem cornerVariation_momentum_pairing
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (q : M14BackwardPath G T a b x y) (hmin : M14IsMinimizing q)
    (p : M14BackwardPath G T a c x (q.curve c)) (hc : c < b)
    (haction : M14BackwardLAction G p =
      M14BackwardLAction G (prefixPath q c p.tau_lt hc.le))
    (Rp : M14SquareRootPath G p) (Rq : M14SquareRootPath G q)
    (Ep : M14PullbackExtension G Rp.curve (M14SqrtParameterInterval a c)
      Rp.horizontal_velocity)
    (Eq : M14PullbackExtension G Rq.curve (M14SqrtParameterInterval a b)
      Rq.horizontal_velocity)
    (hEp : ∀ s ∈ M14SqrtParameterInterval a c, ∀ W,
      M14SquareRootEulerResidual G Rp Ep s W = 0)
    (hEq : ∀ s ∈ M14SqrtParameterInterval a b, ∀ W,
      M14SquareRootEulerResidual G Rq Eq s W = 0)
    (Vp : M14LVariationData G p Rp) (Vq : M14LVariationData G q Rq)
    (hleft : Vp.left_endpoint_fixed) (hfix : M14BothEndpointsFixed Vq)
    (hjoin : ∀ u ∈ Vp.parameterDomain ∩ Vq.parameterDomain, Vp.family c u = Vq.family c u) :
    G.spacetime.horizontalMetric.inner (Rp.curve (Real.sqrt c))
        (Rp.horizontal_velocity (Real.sqrt c)) (M14VariationField Vp (Real.sqrt c)) =
      G.spacetime.horizontalMetric.inner (Rq.curve (Real.sqrt c))
        (Rq.horizontal_velocity (Real.sqrt c)) (M14VariationField Vq (Real.sqrt c)) := by
  have hP := left_variationField_eq_zero Vp hleft
  obtain ⟨hQ₁, hQ₂⟩ := variationField_fixed_endpoints_eq_zero Vq hfix
  have hdp := firstVariation_euler_fixedInitial hCoordinates hM12 Ep hEp Vp hP
  have hdq : HasDerivAt (M14VariationAction Vq) 0 0 := by
    simpa only [hQ₂, map_zero] using
      firstVariation_euler_fixedInitial hCoordinates hM12 Eq hEq Vq hQ₁
  have hdqc := firstVariation_euler_fixedInitial hCoordinates hM12
    (R := prefixSquarePath Rq p.tau_lt hc.le)
    (pullbackExtensionRestrict Eq (Icc_subset_Icc le_rfl (Real.sqrt_le_sqrt hc.le)))
    (prefixSquarePath_euler Rq p.tau_lt hc.le Eq hEq)
    (prefixVariation Vq p.tau_lt hc.le) hQ₁
  have hstat := (isLocalMin_cornerVariationAction hM12 q hmin p hc haction
    Vp Vq hleft hfix hjoin).hasDerivAt_eq_zero ((hdp.add hdq).sub hdqc)
  have hboundary : G.spacetime.horizontalMetric.inner
      ((prefixSquarePath Rq p.tau_lt hc.le).curve (Real.sqrt c))
      ((prefixSquarePath Rq p.tau_lt hc.le).horizontal_velocity (Real.sqrt c))
      (M14VariationField (prefixVariation Vq p.tau_lt hc.le) (Real.sqrt c)) =
      G.spacetime.horizontalMetric.inner (Rq.curve (Real.sqrt c))
        (Rq.horizontal_velocity (Real.sqrt c)) (M14VariationField Vq (Real.sqrt c)) := rfl
  rw [hboundary] at hstat
  exact sub_eq_zero.mp (by simpa only [add_zero] using hstat)

end PoincareConjecture.M14
