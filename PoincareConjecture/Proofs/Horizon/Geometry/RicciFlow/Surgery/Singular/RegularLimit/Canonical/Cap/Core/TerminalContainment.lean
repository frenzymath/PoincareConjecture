import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.EnlargedOldBalls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.CoreRadiusPersistence

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

theorem exists_eventually_cap_core_terminal_ball_containment
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀)
    (L : ℝ) {cmax : ℝ} (hcmax : 1 < cmax) :
    ∃ c : ℝ, 1 < c ∧ c < cmax ∧
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t),
          N.epsilon ≤ CapCertificate.coreBallClearanceThreshold.{u} →
          N.cap_constant ≤ H.constant → N.connection = F.connection t →
          H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
          H.reference.forward t ht x₀ ∈ N.core →
          ∀ x : H.regularRegion P04, H.reference.forward t ht x ∈ N.core →
            N.core_radius (H.reference.forward t ht x) ≤ L →
            closure ((H.terminalMetric P04).ball x
              (c * N.core_radius (H.reference.forward t ht x))) ⊆
                H.regularReferencePreimage P04 t ht N.carrier := by
  obtain ⟨δ, hδ, henlarge⟩ := H.exists_eventually_cap_core_enlarged_old_balls P04 hA x₀ hx₀
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
  let R := r + δ
  let B := (F.metric t).ball p R
  have hr : 0 < r := N.core_radius_pos p hxcore
  have hR : 0 < R := add_pos hr hδ
  obtain ⟨hclosed, _⟩ := henlarge ht N hε hconstant hconnection hcapture hx₀core p hxcore
  have hBN : B ⊆ N.carrier := fun y hy => hclosed (subset_closure hy)
  have hBcapture : H.reference.inverse t ht '' B ⊆ Subtype.val '' A :=
    (image_mono hBN).trans hcapture
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
  have hcomparison : c * (c * r) ≤ R := by
    have hm := (mul_le_mul_of_nonneg_left hrL hfactor).trans_lt hmargin
    change (c ^ 2 - 1) * r < δ at hm
    dsimp [R]
    nlinarith
  have hsmallball := RiemannianMetric.ball_subset_ball_of_tangentNorm_le_on_closedBall
    ((H.terminalFlow P04).metric t) (H.terminalMetric P04) x hR hcpos hcomparison
    (fun y hy v => (hnorm y (hclosureA (by
      rwa [RiemannianMetric.closure_ball_eq_edist_le _ x hR])) v).2)
  intro y hy
  exact hclosed (hclosureB (closure_mono hsmallball hy))

theorem exists_eventually_cap_core_contained_calibrated_radius
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀)
    {cmax : ℝ} (hcmax : 1 < cmax) :
    ∃ c : ℝ, 1 < c ∧ c < cmax ∧
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t),
          N.epsilon ≤ CapCertificate.coreBallClearanceThreshold.{u} →
          N.cap_constant ≤ H.constant → N.connection = F.connection t →
          H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
          H.reference.forward t ht x₀ ∈ N.core →
          ∀ x : H.regularRegion P04, H.reference.forward t ht x ∈ N.core →
            ∃ r : ℝ, 0 < r ∧
              N.core_radius (H.reference.forward t ht x) / c ≤ r ∧
              r ≤ c * N.core_radius (H.reference.forward t ht x) ∧
              scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04)
                ((H.terminalMetric P04).ball x r) = r⁻¹ ^ 2 ∧
              closure ((H.terminalMetric P04).ball x r) ⊆
                H.regularReferencePreimage P04 t ht N.carrier ∧
              IsCompact (closure ((H.terminalMetric P04).ball x r)) := by
  let m := (H.terminalConnection P04).scalarCurvature x₀ / 2
  have hm : 0 < m := half_pos hx₀
  let L := H.constant / m + 1
  have hL : 0 < L := by dsimp [L]; positivity [H.constant_pos]
  have hscale : H.constant ≤ m * L ^ 2 := by
    have hcancel : m * (H.constant / m) = H.constant := mul_div_cancel₀ _ hm.ne'
    have hnonneg := mul_nonneg hm.le (sq_nonneg (H.constant / m))
    dsimp only [L]
    nlinarith [H.constant_pos]
  obtain ⟨c₁, hc₁, hc₁max, hcontainment⟩ :=
    H.exists_eventually_cap_core_terminal_ball_containment P04 hA x₀ hx₀ L hcmax
  obtain ⟨c, hc, hcc₁, hcalibration⟩ :=
    H.exists_eventually_cap_core_radius_persistence P04 hA x₀ hx₀ hc₁
  have hscalar : ∀ᶠ t in 𝓝[<] T, m < H.reference.scalar t x₀ :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually (Ioi_mem_nhds (half_lt_self hx₀))
  refine ⟨c, hc, hcc₁.trans hc₁max, ?_⟩
  filter_upwards [hscalar, hcontainment, hcalibration] with t hscalar hcontainment hcalibration
  intro ht N hε hconstant hconnection hcapture hx₀core x hxcore
  have hbase : m ≤ N.connection.scalarCurvature (H.reference.forward t ht x₀) := by
    rw [hconnection, H.reference.scalar_pullback]
    exact hscalar.le
  have hrL := (N.core_radius_lt_of_scalar_lower hconstant hm hL hscale
    (N.core_subset_carrier hx₀core) hbase hxcore).le
  have hinside := hcontainment ht N hε hconstant hconnection hcapture hx₀core x hxcore hrL
  obtain ⟨r, hr, hrlo, hrhi, hcal, hcompact⟩ :=
    hcalibration ht N hconstant hconnection hcapture hx₀core x hxcore
  refine ⟨r, hr, hrlo, hrhi, hcal, ?_, hcompact⟩
  apply Subset.trans (closure_mono ?_) hinside
  intro y hy
  exact hy.trans_le (ENNReal.ofReal_le_ofReal (hrhi.trans
    (mul_le_mul_of_nonneg_right hcc₁.le (N.core_radius_pos _ hxcore).le)))

end PoincareConjecture.SingularTimeAssumptions
