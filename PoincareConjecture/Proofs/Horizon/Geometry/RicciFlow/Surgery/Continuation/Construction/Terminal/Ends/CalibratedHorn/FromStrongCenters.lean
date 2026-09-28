import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.AtNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.SourceTube
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Frontier











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

theorem exists_calibrated_strongHorn_of_high_strong_centers
    (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u}) (hA : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (rho : ℝ) (hrho : 0 < rho) (hconstant : 2 ≤ H.constant)
    (hcore : ∃ x ∈ K.component, Q.terminal_scalar x ≤ rho⁻¹ ^ 2)
    (hstrong : ∀ x ∈ K.component,
      2 * H.constant * rho⁻¹ ^ 2 ≤ Q.terminal_scalar x →
      ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = x) :
    ∃ horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon),
      horn.carrier ⊆ K.component ∧
      (∃ n : ℕ, Subtype.val '' e.tail n ⊆ horn.carrier) ∧
      Disjoint horn.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} ∧
      (∀ x ∈ horn.boundary_sphere,
        Q.terminal_scalar x < 8 * H.constant * rho⁻¹ ^ 2) ∧
      HornBoundaryBelow horn (rho / (2 * H.constant)) := by
  have hε : terminalAccuracyFactor * H.epsilon ≤ 1 / 200 := hA.trans A.epsilon₀_le_one_two_hundred
  have hhalf : terminalAccuracyFactor * H.epsilon < 1 / 2 := hε.trans_lt (by norm_num)
  have hqpos : 0 < rho⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hrho)
  have hlevel : rho⁻¹ ^ 2 < 4 * H.constant * rho⁻¹ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hconstant hqpos.le]
  obtain ⟨n, X, hclosed, hconn, hcomponent, htail, _, hbound,
    ⟨x, hx, hxlevel⟩, hfront, _⟩ :=
    Q.exists_end_superlevel_region_compact_frontier K e (4 * H.constant * rho⁻¹ ^ 2)
      (by obtain ⟨y, hy, hyR⟩ := hcore; exact ⟨y, hy, hyR.trans_lt hlevel⟩)
  have hstrongX : ∀ y ∈ X,
      ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = y := by
    intro y hy
    apply hstrong y (hcomponent hy)
    nlinarith [hbound y hy, mul_pos H.constant_pos hqpos]
  obtain ⟨R⟩ := Q.exists_source_tube_of_strong_centers A hA K e X hconn n htail hstrongX
  let tube := R.tube
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
  have htubeHigh : ∀ y ∈ tube.carrier,
      2 * H.constant * rho⁻¹ ^ 2 < Q.terminal_scalar y := by
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
    linarith
  have hstrongU : ∀ y ∈ tube.carrier,
      ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = y := by
    intro y hy
    exact hstrong y (htubeK hy) (htubeHigh y hy).le
  have hxtube : x ∈ tube.carrier := tube.contains_X hx
  rw [tube.carrier_eq_chain_union] at hxtube
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hxtube
  obtain ⟨S, hS, hsame⟩ := tube.chain.selected i.val i.property
  obtain ⟨N, hN, _⟩ := R.source_subset hS
  have hcarrier : (tube.chain.neck i.val).carrier = N.carrier :=
    hsame.carrier_eq.trans (congrArg EpsilonNeck.carrier hN)
  have hNU : N.carrier ⊆ tube.carrier := by
    rw [← hcarrier, tube.carrier_eq_chain_union]
    exact subset_iUnion (fun j : {j // j ∈ tube.chain.shape.active} =>
      (tube.chain.neck j.val).carrier) i
  have hsep : (N.spatialNeck hhalf).IsSeparating := by
    have h := R.separating_necks S (R.source_subset hS)
    rwa [hN] at h
  have hlinear : ∀ y ∈ N.central_sphere,
      Q.terminal_scalar y < 8 * H.constant * rho⁻¹ ^ 2 := by
    intro y hy
    have hyi : y ∈ (tube.chain.neck i.val).carrier :=
      hcarrier.symm ▸ N.central_sphere_subset hy
    have hratio := (tube.chain.neck i.val).scalar_lt_two_mul_of_mem_carrier
      (Q.extension.extended.connection T)
      ((tube.chain.epsilon_eq i.val i.property).trans_le tube.epsilon_le_threshold) hyi hxi
    rw [← Q.terminal_scalar_eq, hxlevel] at hratio
    nlinarith
  obtain ⟨horn, hboundary, hsub, k, hk⟩ :=
    e.exists_strongHorn_at_neck_of_epsilon_le tube hclosed hfront n htail hε N hNU hsep hstrongU
  refine ⟨horn, hsub.trans htubeK, ⟨k, hk⟩, ?_, ?_, ?_⟩
  · apply disjoint_left.mpr
    intro y hy hylow
    have h := htubeHigh y (hsub hy)
    have hylow' : Q.terminal_scalar y ≤ rho⁻¹ ^ 2 := hylow
    nlinarith [mul_le_mul_of_nonneg_right hconstant hqpos.le]
  · intro y hy
    exact hlinear y (hboundary ▸ hy)
  · intro y hy
    have h := hlinear y (hboundary ▸ hy)
    have hCsq : 2 * H.constant ≤ H.constant ^ 2 := by nlinarith [H.constant_pos]
    have hmul := mul_le_mul_of_nonneg_right hCsq hqpos.le
    have hid : (rho / (2 * H.constant))⁻¹ ^ 2 =
        4 * H.constant ^ 2 * rho⁻¹ ^ 2 := by
      rw [inv_div, div_eq_mul_inv]
      ring
    rw [← Q.terminal_scalar_eq, hid]
    linarith

end PoincareConjecture.SingularLimitConclusion
