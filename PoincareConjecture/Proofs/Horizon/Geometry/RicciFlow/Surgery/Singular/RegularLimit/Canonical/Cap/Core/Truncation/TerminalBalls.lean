import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.OldBalls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.TerminalContainment



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



theorem terminal_closedBall_subset_of_captured_old_ball
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (t : ℝ) (ht : t ∈ Ico H.reference.tMinus T) (x : H.regularRegion P04)
    {r R c : ℝ} (hR : 0 < R) (hc : 0 < c) (hcr : c * r ≤ R)
    (S : Set (F.slice t).carrier)
    (hcapture : H.reference.inverse t ht '' S ⊆ Subtype.val '' A)
    (hclosed : closure ((F.metric t).ball (H.reference.forward t ht x) R) ⊆ S)
    (hnorm : ∀ y ∈ A, ∀ v : TangentSpace (𝓡 3) y,
      ((H.terminalFlow P04).metric t).tangentNorm y v ≤
        c * (H.terminalMetric P04).tangentNorm y v) :
    closure ((H.terminalMetric P04).ball x r) ⊆ H.regularReferencePreimage P04 t ht S ∧
      IsCompact (closure ((H.terminalMetric P04).ball x r)) := by
  let B := (F.metric t).ball (H.reference.forward t ht x) R
  have hBS : B ⊆ S := fun _ hy => hclosed (subset_closure hy)
  have hBcapture : H.reference.inverse t ht '' B ⊆ Subtype.val '' A :=
    (image_mono hBS).trans hcapture
  have hBregular : H.reference.inverse t ht '' B ⊆ H.reference.regularLimitSet := by
    rintro y hy
    obtain ⟨a, _, rfl⟩ := hBcapture hy
    exact a.property
  have hballEq := H.regularReferencePreimage_ball_eq P04 t ht x R hBregular
  have hsubset : ((H.terminalFlow P04).metric t).ball x R ⊆ A := by
    rw [← hballEq]
    exact H.regularReferencePreimage_subset P04 t ht B hBcapture
  have hclosureA : closure (((H.terminalFlow P04).metric t).ball x R) ⊆ A :=
    closure_minimal hsubset hA.isClosed
  let f : H.regularRegion P04 → (F.slice t).carrier :=
    fun y => H.reference.forward t ht y
  have hf : Continuous f :=
    (H.reference.forward_smooth t ht).continuous.comp continuous_subtype_val
  have hclosureB : closure (((H.terminalFlow P04).metric t).ball x R) ⊆
      f ⁻¹' closure B := by
    apply closure_minimal ?_ (isClosed_closure.preimage hf)
    intro y hy
    apply subset_closure
    change y ∈ H.regularReferencePreimage P04 t ht
      ((F.metric t).ball (H.reference.forward t ht x) R)
    rwa [hballEq]
  have hsmallball := RiemannianMetric.ball_subset_ball_of_tangentNorm_le_on_closedBall
    ((H.terminalFlow P04).metric t) (H.terminalMetric P04) x hR hc hcr
    (fun y hy v => hnorm y (hclosureA (by
      rwa [RiemannianMetric.closure_ball_eq_edist_le _ x hR])) v)
  have hinside : closure ((H.terminalMetric P04).ball x r) ⊆
      H.regularReferencePreimage P04 t ht S := fun y hy =>
    hclosed (hclosureB (closure_mono hsmallball hy))
  exact ⟨hinside, hA.of_isClosed_subset isClosed_closure
    (hinside.trans (H.regularReferencePreimage_subset P04 t ht S hcapture))⟩



theorem exists_eventually_truncated_cap_core_terminal_ball_containment
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀)
    (L : ℝ) {cmax : ℝ} (hcmax : 1 < cmax) :
    ∃ c : ℝ, 1 < c ∧ c < cmax ∧
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t),
          N.epsilon ≤ CapCertificate.truncatedBallClearanceThreshold.{u} →
          N.cap_constant ≤ H.constant → N.connection = F.connection t →
          H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
          H.reference.forward t ht x₀ ∈ N.core →
          ∀ x : H.regularRegion P04, H.reference.forward t ht x ∈ N.core →
            N.core_radius (H.reference.forward t ht x) ≤ L →
            closure ((H.terminalMetric P04).ball x
              (c * N.core_radius (H.reference.forward t ht x))) ⊆
                H.regularReferencePreimage P04 t ht
                  (N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) ((2 / 5 : ℝ) * N.epsilon⁻¹)) := by
  obtain ⟨δ, hδ, henlarge⟩ := H.exists_eventually_truncated_cap_enlarged_old_balls P04 hA x₀ hx₀
  have hcont : ContinuousAt (fun c : ℝ => (c ^ 2 - 1) * L) 1 := by fun_prop
  have hsmall : ∀ᶠ c : ℝ in 𝓝 1, (c ^ 2 - 1) * L < δ :=
    hcont.eventually (Iio_mem_nhds (by simpa using hδ))
  have hchoose : ∀ᶠ c : ℝ in 𝓝[>] 1,
      1 < c ∧ c < cmax ∧ (c ^ 2 - 1) * L < δ := by
    have hmax : ∀ᶠ c : ℝ in 𝓝[>] 1, c < cmax :=
      nhdsWithin_le_nhds (Iio_mem_nhds hcmax)
    filter_upwards [self_mem_nhdsWithin, hsmall.filter_mono nhdsWithin_le_nhds,
      hmax] with c hc hs hmax'
    exact ⟨hc, hmax', hs⟩
  obtain ⟨c, hc, hcmax', hmargin⟩ := hchoose.exists
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hfactor : 0 ≤ c ^ 2 - 1 := by nlinarith
  refine ⟨c, hc, hcmax', ?_⟩
  filter_upwards [henlarge, H.eventually_terminal_tangentNorm_comparison P04 hA hc]
    with t henlarge hnorm
  intro ht N hε hconstant hconnection hcapture hx₀core x hxcore hrL
  let p := H.reference.forward t ht x
  let r := N.core_radius p
  have hr : 0 < r := N.core_radius_pos p hxcore
  obtain ⟨hclosed, _⟩ := henlarge ht N hε hconstant hconnection hcapture hx₀core p
    (Or.inl (N.core_subset_closed_core hxcore)) r hr
    (fun _ hy => N.core_ball_subset p hxcore (subset_closure hy)) (N.core_radius_eq p hxcore)
  have hcomparison : c * (c * r) ≤ r + δ := by
    have hm := (mul_le_mul_of_nonneg_left hrL hfactor).trans_lt hmargin
    change (c ^ 2 - 1) * r < δ at hm
    nlinarith
  have hsub : N.closed_core ∪ N.end_neck.region (-N.epsilon⁻¹) ((2 / 5 : ℝ) * N.epsilon⁻¹) ⊆
      N.carrier := union_subset N.closed_core_subset_carrier
    ((N.end_neck.region_subset_carrier _ _).trans N.end_neck_subset)
  exact (H.terminal_closedBall_subset_of_captured_old_ball P04 hA t ht x (add_pos hr hδ)
    hcpos hcomparison _ ((image_mono hsub).trans hcapture) hclosed
    (fun y hy v => (hnorm y hy v).2)).1

end PoincareConjecture.SingularTimeAssumptions
