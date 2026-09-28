import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.SameCore.Clearance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.EnlargedOldBalls



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



theorem exists_eventually_same_core_enlarged_old_balls
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t),
          N.epsilon ≤ CapCertificate.sameCoreBallClearanceThreshold.{u} →
          N.cap_constant ≤ H.constant → N.connection = F.connection t →
          H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
          H.reference.forward t ht x₀ ∈ N.core →
          ∀ p ∈ N.closed_core, ∀ r : ℝ, 0 < r →
            (F.metric t).ball p r ⊆ N.carrier →
            scalarCurvatureSupOn (F.metric t) N.connection ((F.metric t).ball p r) = r⁻¹ ^ 2 →
          ∀ b : ℝ, -N.epsilon⁻¹ + 40 ≤ b →
            closure ((F.metric t).ball p (r + δ)) ⊆
              N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b ∧
            IsCompact (closure ((F.metric t).ball p (r + δ))) := by
  let B := (H.terminalConnection P04).scalarCurvature x₀ + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let δ := (H.constant * B) ^ (-1 / 2 : ℝ)
  have hδ : 0 < δ := Real.rpow_pos_of_pos (mul_pos H.constant_pos hB) _
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  have hlate : ∀ᶠ t in 𝓝[<] T, H.reference.scalar t x₀ < B :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually (Iio_mem_nhds (lt_add_one _))
  filter_upwards [hlate] with t hlate
  intro ht N hε hconstant hconnection hcapture hx₀core p hp r hr hball hcal b hb
  have hx₀carrier := N.core_subset_carrier hx₀core
  have hpos := N.scalar_pos _ hx₀carrier
  have hscale := (N.neck_scales_lower_of_constant_le hconstant hx₀carrier).1
  rw [hconnection, H.reference.scalar_pullback] at hpos hscale
  have hpow : δ ≤ (H.constant * H.reference.scalar t x₀) ^ (-1 / 2 : ℝ) :=
    Real.rpow_le_rpow_of_nonpos (mul_pos H.constant_pos hpos)
      (mul_le_mul_of_nonneg_left hlate.le H.constant_pos.le) (by norm_num)
  have hscale' : δ ≤ N.end_neck.scale := hpow.trans hscale.le
  have hinside : closure ((F.metric t).ball p (r + δ / 2)) ⊆
      N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b := by
    intro y hy
    rw [RiemannianMetric.closure_ball_eq_edist_le _ p (by positivity)] at hy
    by_contra hout
    have hlow := N.calibrated_ball_same_core_clearance_of_small hε hr hp hb hout hball hcal
    have hstrict : ENNReal.ofReal (r + δ / 2) <
        ENNReal.ofReal (r + N.end_neck.scale) :=
      ENNReal.ofReal_lt_ofReal_iff (by linarith) |>.mpr (by linarith)
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
  have hcarrier : N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) b ⊆ N.carrier :=
    union_subset N.closed_core_subset_carrier
      ((N.end_neck.region_subset_carrier _ _).trans N.end_neck_subset)
  exact (hA.image hf).of_isClosed_subset isClosed_closure
    (hinside.trans (hcarrier.trans hcaptured))

end PoincareConjecture.SingularTimeAssumptions
