import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.TubeRegion
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.SourceTube
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.AtNeck










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions G T M}

theorem exists_calibrated_strongHorn_of_tube_region (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u}) (hA : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (X : Set (Q.extension.extended.slice T).carrier)
    (tube : EpsilonTubeCertificate (Q.extension.extended.metric T) X)
    (rho : ℝ) (hrho : 0 < rho) (hrho_r₀ : rho < H.r₀)
    (hconstant : 2 ≤ H.constant) (hclosed : IsClosed X)
    (hcomponent : X ⊆ K.component)
    (hfront : ∀ x ∈ frontier X, Q.terminal_scalar x = rho⁻¹ ^ 2)
    (k : ℕ) (htail : Subtype.val '' e.tail k ⊆ X)
    (hlow : ∃ x ∈ K.component, Q.terminal_scalar x ≤ rho⁻¹ ^ 2) :
    ∃ horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon),
      horn.carrier ⊆ K.component ∧
      (∃ n : ℕ, Subtype.val '' e.tail n ⊆ horn.carrier) ∧
      Disjoint horn.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} ∧
      (∀ x ∈ horn.boundary_sphere, Q.terminal_scalar x < 8 * H.constant * rho⁻¹ ^ 2) ∧
      HornBoundaryBelow horn (rho / (2 * H.constant)) := by
  have hqpos : 0 < rho⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hrho)
  have hq : H.r₀⁻¹ ^ 2 < rho⁻¹ ^ 2 := by
    have hinv := (inv_lt_inv₀ H.r₀_pos hrho).mpr hrho_r₀
    nlinarith [inv_pos.mpr H.r₀_pos, inv_pos.mpr hrho]
  have hC : 1 ≤ H.constant := by linarith
  have hlevel : rho⁻¹ ^ 2 < 4 * H.constant * rho⁻¹ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hC hqpos.le]
  have hlow' : ∃ x ∈ K.component,
      Q.terminal_scalar x < 4 * H.constant * rho⁻¹ ^ 2 := by
    obtain ⟨x, hx, hlow⟩ := hlow
    exact ⟨x, hx, hlow.trans_lt hlevel⟩
  obtain ⟨n, Z, hZclosed, hZconnected, hZfront, hZX, hZtail, hZhigh, hattain,
    hstrong, hsource⟩ := Q.exists_strong_end_region_in_tube K e X tube (rho⁻¹ ^ 2)
      hq hC hclosed hcomponent hfront k htail hlow'
  obtain ⟨R⟩ := Q.exists_source_tube_of_strong_centers A hA K e Z hZconnected n hZtail hstrong
  have hε : terminalAccuracyFactor * H.epsilon ≤ 1 / 200 := H.terminal_epsilon_le_threshold
  have hhalf : terminalAccuracyFactor * H.epsilon < 1 / 2 := hε.trans_lt (by norm_num)
  have hselected (i : ℤ) (hi : i ∈ R.tube.chain.shape.active) :
      ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center ∈ Z ∧
        (R.tube.chain.neck i).carrier = N.carrier ∧
        (R.tube.chain.neck i).central_sphere = N.central_sphere ∧
        (N.spatialNeck hhalf).IsSeparating := by
    obtain ⟨P, hP, hsame⟩ := R.tube.chain.selected i hi
    obtain ⟨N, rfl, hN⟩ := R.source_subset hP
    exact ⟨N, hN, hsame.carrier_eq, hsame.central_sphere_eq,
      R.separating_necks _ ⟨N, rfl, hN⟩⟩
  have htubeX : R.tube.carrier ⊆ X := by
    intro x hx
    rw [R.tube.carrier_eq_chain_union] at hx
    obtain ⟨⟨i, hi⟩, hxi⟩ := mem_iUnion.mp hx
    obtain ⟨N, hN, hcarrier, _⟩ := hselected i hi
    exact interior_subset ((hsource N hN).1 (hcarrier ▸ hxi))
  have htubeStrong : ∀ x ∈ R.tube.carrier,
      ∃ N : TerminalStrongNeck Q.extension (terminalAccuracyFactor * H.epsilon), N.center = x := by
    intro x hx
    rw [R.tube.carrier_eq_chain_union] at hx
    obtain ⟨⟨i, hi⟩, hxi⟩ := mem_iUnion.mp hx
    obtain ⟨N, hN, hcarrier, _⟩ := hselected i hi
    exact (hsource N hN).2 x (hcarrier ▸ hxi)
  have htubeHigh : ∀ x ∈ R.tube.carrier, rho⁻¹ ^ 2 < Q.terminal_scalar x := by
    intro x hx
    rw [R.tube.carrier_eq_chain_union] at hx
    obtain ⟨⟨i, hi⟩, hxi⟩ := mem_iUnion.mp hx
    obtain ⟨N, hN, hcarrier, _⟩ := hselected i hi
    have h := (N.scalar_strictly_within_factor_two_on_carrier hε (hcarrier ▸ hxi)).1
    rw [← Q.terminal_scalar_eq] at h
    have hNlevel := hZhigh N.center hN
    nlinarith [mul_le_mul_of_nonneg_right hC hqpos.le]
  obtain ⟨x, hx, hxlevel⟩ := hattain
  have hxU := R.contains_X hx
  rw [R.tube.carrier_eq_chain_union] at hxU
  obtain ⟨⟨i, hi⟩, hxi⟩ := mem_iUnion.mp hxU
  obtain ⟨N, hN, hcarrier, hsphere, hsep⟩ := hselected i hi
  have hNU : N.carrier ⊆ R.tube.carrier := by
    intro y hy
    rw [R.tube.carrier_eq_chain_union]
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hcarrier.symm ▸ hy⟩
  have hlinear : ∀ y ∈ N.carrier, Q.terminal_scalar y < 8 * H.constant * rho⁻¹ ^ 2 := by
    intro y hy
    have h := (R.tube.chain.neck i).scalar_lt_two_mul_of_mem_carrier
      (Q.extension.extended.connection T)
      ((R.tube.chain.epsilon_eq i hi).trans_le R.tube.epsilon_le_threshold)
      (hcarrier.symm ▸ hy) hxi
    rw [← Q.terminal_scalar_eq, hxlevel] at h
    nlinarith
  obtain ⟨horn, hboundary, hhorn, m, hm⟩ :=
    e.exists_strongHorn_at_neck_of_epsilon_le R.tube hZclosed hZfront n hZtail
      hε N hNU hsep htubeStrong
  refine ⟨horn, hhorn.trans (htubeX.trans hcomponent), ⟨m, hm⟩,
    disjoint_left.mpr (fun y hy hlow => (htubeHigh y (hhorn hy)).not_ge hlow), ?_, ?_⟩
  · intro y hy
    exact hlinear y (N.central_sphere_subset (hboundary ▸ hy))
  · intro y hy
    have h := hlinear y (N.central_sphere_subset (hboundary ▸ hy))
    have hCsq : 2 * H.constant ≤ H.constant ^ 2 := by nlinarith [H.constant_pos]
    have hmul := mul_le_mul_of_nonneg_right hCsq hqpos.le
    have hid : (rho / (2 * H.constant))⁻¹ ^ 2 =
        4 * H.constant ^ 2 * rho⁻¹ ^ 2 := by
      rw [inv_div, div_eq_mul_inv]
      ring
    rw [← Q.terminal_scalar_eq, hid]
    linarith

end PoincareConjecture.SingularLimitConclusion
