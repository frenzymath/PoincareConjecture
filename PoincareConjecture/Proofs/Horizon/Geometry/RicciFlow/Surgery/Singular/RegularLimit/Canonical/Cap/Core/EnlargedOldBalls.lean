import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.UniformClearance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.CoreBalls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SingularTimeAssumptions

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}

theorem exists_eventually_cap_core_enlarged_old_balls
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t),
          N.epsilon ≤ CapCertificate.coreBallClearanceThreshold.{u} →
          N.cap_constant ≤ H.constant → N.connection = F.connection t →
          H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
          H.reference.forward t ht x₀ ∈ N.core →
          ∀ p ∈ N.core,
            closure ((F.metric t).ball p (N.core_radius p + δ)) ⊆ N.carrier ∧
            IsCompact (closure ((F.metric t).ball p (N.core_radius p + δ))) := by
  obtain ⟨δ, hδ, hclearance⟩ := H.exists_eventually_cap_core_uniform_clearance P04 x₀ hx₀
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  filter_upwards [hclearance] with t hclearance
  intro ht N hε hconstant hconnection hcapture hx₀core p hp
  have hr := N.core_radius_pos p hp
  have hinside : closure ((F.metric t).ball p (N.core_radius p + δ / 2)) ⊆ N.carrier := by
    intro y hy
    rw [RiemannianMetric.closure_ball_eq_edist_le _ p (by positivity)] at hy
    by_contra hout
    have hlow := hclearance ht N hε hconstant hconnection hx₀core p hp y hout
    have hstrict : ENNReal.ofReal (N.core_radius p + δ / 2) <
        ENNReal.ofReal (N.core_radius p + δ) :=
      ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr (by linarith)
    exact (not_lt_of_ge (hlow.trans hy)) hstrict
  refine ⟨hinside, ?_⟩
  let f : H.regularRegion P04 → (F.slice t).carrier :=
    fun x => H.reference.forward t ht x
  have hf : Continuous f :=
    (H.reference.forward_smooth t ht).continuous.comp continuous_subtype_val
  have hcaptured : N.carrier ⊆ f '' A := by
    intro y hy
    obtain ⟨x, hx, heq⟩ := hcapture ⟨y, hy, rfl⟩
    refine ⟨x, hx, ?_⟩
    change H.reference.forward t ht x = y
    rw [heq, H.reference.right_inverse]
  exact (hA.image hf).of_isClosed_subset isClosed_closure (hinside.trans hcaptured)

end PoincareConjecture.SingularTimeAssumptions
