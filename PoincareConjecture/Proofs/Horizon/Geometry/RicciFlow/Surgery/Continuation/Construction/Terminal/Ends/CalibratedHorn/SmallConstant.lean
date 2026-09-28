import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.AtNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.SourceTube
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.CapContainment
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Frontier
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckBoundary

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

theorem exists_calibrated_strongHorn_of_constant_le_ninetyNine
    (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u}) (hA : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (rho : ℝ) (hrho : 0 < rho) (hrho_r₀ : rho < H.r₀)
    (hconstant : 1 ≤ H.constant) (hsmall : H.constant ≤ 99)
    (hcore : ∃ x ∈ K.component, Q.terminal_scalar x ≤ rho⁻¹ ^ 2) :
    ∃ horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon),
      horn.carrier ⊆ K.component ∧
      Disjoint horn.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} ∧
      (∃ n : ℕ, Subtype.val '' e.tail n ⊆ horn.carrier) ∧
      HornBoundaryBelow horn (rho / (2 * H.constant)) ∧
      ∀ x ∈ horn.boundary_sphere,
        Q.terminal_scalar x < 8 * H.constant * rho⁻¹ ^ 2 := by
  have hε : terminalAccuracyFactor * H.epsilon ≤ 1 / 200 := hA.trans A.epsilon₀_le_one_two_hundred
  have hhalf : terminalAccuracyFactor * H.epsilon < 1 / 2 := hε.trans_lt (by norm_num)
  have hqpos : 0 < rho⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hrho)
  have hr₀q : H.r₀⁻¹ ^ 2 < rho⁻¹ ^ 2 := by
    have hi := (inv_lt_inv₀ H.r₀_pos hrho).mpr hrho_r₀
    nlinarith [inv_pos.mpr H.r₀_pos, inv_pos.mpr hrho]
  have hlevel : rho⁻¹ ^ 2 < 2 * H.constant * rho⁻¹ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hconstant hqpos.le]
  obtain ⟨n, X, hclosed, hconn, hcomponent, htail, _, hbound,
    ⟨x, hx, hxlevel⟩, hfront, _⟩ :=
    Q.exists_end_superlevel_region_compact_frontier K e (2 * H.constant * rho⁻¹ ^ 2)
      (by obtain ⟨y, hy, hyR⟩ := hcore; exact ⟨y, hy, hyR.trans_lt hlevel⟩)
  have hstrongX : ∀ y ∈ X,
      ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = y := by
    intro y hy
    exact Q.neck_on_end_component_of_constant_le_ninetyNine hsmall K e
      (hcomponent hy) (hr₀q.trans (hlevel.trans_le (hbound y hy)))
  obtain ⟨R⟩ := Q.exists_source_tube_of_strong_centers A hA K e X hconn n htail hstrongX
  let tube := R.tube
  have htubeε : tube.epsilon = terminalAccuracyFactor * H.epsilon := R.epsilon_eq
  have htubeK : tube.carrier ⊆ K.component := by
    intro y hy
    rw [tube.carrier_eq_chain_union] at hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    have hcenter := hcomponent (R.selected_centers_mem i.val i.property)
    have heq : connectedComponent (tube.chain.neck i.val).center = K.component := by
      rw [K.component_eq] at hcenter ⊢
      exact (connectedComponent_eq hcenter).symm
    rw [← heq]
    exact (tube.chain.neck i.val).carrier_subset_connectedComponent hyi
  have htubeHigh : ∀ y ∈ tube.carrier, rho⁻¹ ^ 2 < Q.terminal_scalar y := by
    intro y hy
    rw [tube.carrier_eq_chain_union] at hy
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hy
    let N := tube.chain.neck i.val
    have hNε : N.epsilon ≤ 1 / 200 :=
      (tube.chain.epsilon_eq i.val i.property).trans_le tube.epsilon_le_threshold
    have hcenter := hbound N.center (R.selected_centers_mem i.val i.property)
    have hratio := N.scalar_lt_two_mul_of_mem_carrier
      (Q.extension.extended.connection T) hNε
      (N.central_sphere_subset N.center_on_central_sphere) hyi
    rw [← Q.terminal_scalar_eq] at hratio
    nlinarith [mul_le_mul_of_nonneg_right hconstant hqpos.le]
  have hstrongU : ∀ y ∈ tube.carrier,
      ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = y := by
    intro y hy
    exact Q.neck_on_end_component_of_constant_le_ninetyNine hsmall K e (htubeK hy)
      (hr₀q.trans (htubeHigh y hy))
  have hxtube : x ∈ tube.carrier := tube.contains_X hx
  rw [tube.carrier_eq_chain_union] at hxtube
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxtube
  obtain ⟨S, hS, hsame⟩ := tube.chain.selected i.val i.property
  have hsource := R.source_subset hS
  obtain ⟨N, hN, _⟩ := hsource
  have hcarrier : (tube.chain.neck i.val).carrier = N.carrier := by
    exact hsame.2.2.2.1.trans (congrArg EpsilonNeck.carrier hN)
  have hsphere : (tube.chain.neck i.val).central_sphere = N.central_sphere := by
    exact hsame.2.2.2.2.1.trans (congrArg EpsilonNeck.central_sphere hN)
  have hNU : N.carrier ⊆ tube.carrier := by
    rw [← hcarrier, tube.carrier_eq_chain_union]
    exact subset_iUnion (fun j : {j // j ∈ tube.chain.shape.active} =>
      (tube.chain.neck j.val).carrier) i
  have hsep : (N.spatialNeck hhalf).IsSeparating := by
    have h := R.separating_necks S (R.source_subset hS)
    rwa [hN] at h
  have hlinear : ∀ y ∈ N.central_sphere,
      Q.terminal_scalar y < 4 * H.constant * rho⁻¹ ^ 2 := by
    intro y hy
    have hyi : y ∈ (tube.chain.neck i.val).carrier := by
      rw [hcarrier]
      exact N.central_sphere_subset hy
    have hratio := (tube.chain.neck i.val).scalar_lt_two_mul_of_mem_carrier
      (Q.extension.extended.connection T)
      ((tube.chain.epsilon_eq i.val i.property).trans_le tube.epsilon_le_threshold) hyi hxi
    rw [← Q.terminal_scalar_eq, hxlevel] at hratio
    nlinarith
  obtain ⟨horn, hboundary, hsub, k, hk⟩ :=
    e.exists_strongHorn_at_neck_of_epsilon_le tube hclosed hfront n htail hε N hNU hsep hstrongU
  refine ⟨horn, hsub.trans htubeK,
    disjoint_left.mpr (fun y hy hylow => (htubeHigh y (hsub hy)).not_ge hylow),
    ⟨k, hk⟩, ?_, ?_⟩
  · intro y hy
    rw [hboundary] at hy
    rw [← Q.terminal_scalar_eq]
    have hC : H.constant ≤ H.constant ^ 2 := by
      nlinarith [sq_nonneg (H.constant - 1)]
    have hid : (rho / (2 * H.constant))⁻¹ ^ 2 =
        4 * H.constant ^ 2 * rho⁻¹ ^ 2 := by
      rw [inv_div, div_eq_mul_inv]
      ring
    rw [hid]
    nlinarith [hlinear y hy, mul_le_mul_of_nonneg_right hC hqpos.le]
  · intro y hy
    rw [hboundary] at hy
    have hpositive := mul_pos H.constant_pos hqpos
    nlinarith [hlinear y hy]

end PoincareConjecture.SingularLimitConclusion
