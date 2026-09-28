import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Normalization.Carrier.Cap
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Small











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow

attribute [local instance] smallCarrier smallChartedSpace smallIsManifold
  smallT3Space smallMeasurableSpace smallBorelSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ}

omit [MeasurableSpace M] [BorelSpace M] in

theorem metricHomothety_shrink (F : RicciFlow 3 M J) (t : ℝ) :
    MetricHomothety (F.metric t) (F.shrink.metric t)
      (Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M) 1 := by
  let e := Poincare.Manifold.shrinkDiffeomorph (𝓡 3) M
  have hid : e.symm ∘ e = id := by funext x; exact e.symm_apply_apply x
  intro x v w
  change (F.pullbackDiffeomorph e.symm |>.metric t).inner (e x)
    (mfderiv (𝓡 3) (𝓡 3) e x v) (mfderiv (𝓡 3) (𝓡 3) e x w) = _
  rw [pullbackDiffeomorph_inner]
  have hi := mfderiv_comp x (e.symm.mdifferentiable (by simp) (e x))
    (e.mdifferentiable (by simp) x)
  rw [hid, mfderiv_id] at hi
  have hv := congrArg (fun L => L v) hi
  have hw := congrArg (fun L => L w) hi
  change v = mfderiv (𝓡 3) (𝓡 3) e.symm (e x)
    (mfderiv (𝓡 3) (𝓡 3) e x v) at hv
  change w = mfderiv (𝓡 3) (𝓡 3) e.symm (e x)
    (mfderiv (𝓡 3) (𝓡 3) e x w) at hw
  rw [← hv, ← hw, e.symm_apply_apply, one_mul]



noncomputable def capFromShrink (F : RicciFlow 3 M J) (t : ℝ)
    (A : CapCertificate (F.shrink.metric t)) : CapCertificate (F.metric t) :=
  A.pullbackSmall (F.metricHomothety_shrink t) (F.connection t)

@[simp] theorem capFromShrink_epsilon (F : RicciFlow 3 M J) (t : ℝ)
    (A : CapCertificate (F.shrink.metric t)) :
    (F.capFromShrink t A).epsilon = A.epsilon := rfl

@[simp] theorem capFromShrink_constant (F : RicciFlow 3 M J) (t : ℝ)
    (A : CapCertificate (F.shrink.metric t)) :
    (F.capFromShrink t A).cap_constant = A.cap_constant := rfl

@[simp] theorem capFromShrink_carrier (F : RicciFlow 3 M J) (t : ℝ)
    (A : CapCertificate (F.shrink.metric t)) :
    (F.capFromShrink t A).carrier = equivShrink M ⁻¹' A.carrier := rfl

@[simp] theorem capFromShrink_core (F : RicciFlow 3 M J) (t : ℝ)
    (A : CapCertificate (F.shrink.metric t)) :
    (F.capFromShrink t A).core = equivShrink M ⁻¹' A.core := rfl

@[simp] theorem capFromShrink_connection (F : RicciFlow 3 M J) (t : ℝ)
    (A : CapCertificate (F.shrink.metric t)) :
    (F.capFromShrink t A).connection = F.connection t := rfl

end PoincareConjecture.RicciFlow
