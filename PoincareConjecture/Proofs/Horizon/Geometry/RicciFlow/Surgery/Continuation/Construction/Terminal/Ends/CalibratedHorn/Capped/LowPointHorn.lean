import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.Capped.LowNeck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.CalibratedHorn.TubeHorn

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

theorem exists_calibrated_strongHorn_of_cappedTube_low_neck (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u}) (hA : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (Y : CappedTubeCertificate (Q.extension.extended.metric T))
    {X : Set (Q.extension.extended.slice T).carrier}
    (hX : IsClosed X) (hfront : IsCompact (frontier X)) (hXY : X ⊆ Y.carrier)
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ X)
    (N : EpsilonNeck (Q.extension.extended.metric T))
    (hepsilon : N.epsilon ≤ 1 / 200) (hNU : N.carrier ⊆ Y.tube.carrier)
    (rho : ℝ) (hrho : 0 < rho) (hrho_r₀ : rho < H.r₀) (hconstant : 8 ≤ H.constant)
    (hNlow : ∀ x ∈ N.central_sphere, Q.terminal_scalar x < 2 * rho⁻¹ ^ 2)
    (hlow : ∃ x ∈ K.component, Q.terminal_scalar x ≤ rho⁻¹ ^ 2) :
    ∃ horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon),
      horn.carrier ⊆ K.component ∧
      (∃ k : ℕ, Subtype.val '' e.tail k ⊆ horn.carrier) ∧
      Disjoint horn.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} ∧
      (∀ x ∈ horn.boundary_sphere, Q.terminal_scalar x < 32 * H.constant * rho⁻¹ ^ 2) ∧
      HornBoundaryBelow horn (rho / (2 * H.constant)) := by
  have hqpos : 0 < rho⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hrho)
  obtain ⟨k, Z, hZclosed, _, hZK, hZtail, _, _, _, _, hZfront, hZtube⟩ :=
    Q.exists_end_region_in_tube_of_low_neck K e Y hX hfront hXY n htail N hepsilon hNU
      (rho⁻¹ ^ 2) hqpos hNlow hlow
  let tube : EpsilonTubeCertificate (Q.extension.extended.metric T) Z :=
    { Y.tube with contains_X := hZtube }
  have hid : (rho / 2)⁻¹ ^ 2 = 4 * rho⁻¹ ^ 2 := by
    rw [inv_div, div_eq_mul_inv]
    ring
  have hlow' : ∃ x ∈ K.component, Q.terminal_scalar x ≤ (rho / 2)⁻¹ ^ 2 := by
    obtain ⟨x, hx, h⟩ := hlow
    refine ⟨x, hx, ?_⟩
    rw [hid]
    linarith
  obtain ⟨horn, hhornK, hhornTail, hhornLow, hlinear, _⟩ :=
    Q.exists_calibrated_strongHorn_of_tube_region A hA K e Z tube (rho / 2)
      (by linarith) (by linarith) (by linarith) hZclosed hZK
      (fun x hx => (hZfront x hx).trans hid.symm) k hZtail hlow'
  have hlinear' : ∀ x ∈ horn.boundary_sphere,
      Q.terminal_scalar x < 32 * H.constant * rho⁻¹ ^ 2 := by
    intro x hx
    have h := hlinear x hx
    rw [hid] at h
    nlinarith
  refine ⟨horn, hhornK, hhornTail, ?_, hlinear', ?_⟩
  · apply disjoint_left.mpr
    intro x hx hlowx
    apply disjoint_left.mp hhornLow hx
    change Q.terminal_scalar x ≤ (rho / 2)⁻¹ ^ 2
    rw [hid]
    have hlowx' : Q.terminal_scalar x ≤ rho⁻¹ ^ 2 := hlowx
    linarith
  · intro x hx
    have h := hlinear' x hx
    have hCsq : 8 * H.constant ≤ H.constant ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hconstant) H.constant_pos.le]
    have hmul := mul_le_mul_of_nonneg_right hCsq hqpos.le
    have hscale : (rho / (2 * H.constant))⁻¹ ^ 2 =
        4 * H.constant ^ 2 * rho⁻¹ ^ 2 := by
      rw [inv_div, div_eq_mul_inv]
      ring
    rw [← Q.terminal_scalar_eq, hscale]
    linarith

theorem exists_calibrated_strongHorn_of_cappedTube_low_tube_point
    (Q : SingularLimitConclusion H)
    (A : RepairedNeckCapTopologyTheory.{u}) (hA : terminalAccuracyFactor * H.epsilon ≤ A.epsilon₀)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (Y : CappedTubeCertificate (Q.extension.extended.metric T))
    {X : Set (Q.extension.extended.slice T).carrier}
    (hX : IsClosed X) (hfront : IsCompact (frontier X)) (hXY : X ⊆ Y.carrier)
    (n : ℕ) (htail : Subtype.val '' e.tail n ⊆ X)
    (rho : ℝ) (hrho : 0 < rho) (hrho_r₀ : rho < H.r₀) (hconstant : 8 ≤ H.constant)
    {p : (Q.extension.extended.slice T).carrier}
    (hp : p ∈ Y.tube.carrier) (hpK : p ∈ K.component)
    (hplow : Q.terminal_scalar p ≤ rho⁻¹ ^ 2) :
    ∃ horn : StrongHorn Q.extension (terminalAccuracyFactor * H.epsilon),
      horn.carrier ⊆ K.component ∧
      (∃ k : ℕ, Subtype.val '' e.tail k ⊆ horn.carrier) ∧
      Disjoint horn.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} ∧
      (∀ x ∈ horn.boundary_sphere, Q.terminal_scalar x < 32 * H.constant * rho⁻¹ ^ 2) ∧
      HornBoundaryBelow horn (rho / (2 * H.constant)) := by
  rw [Y.tube.carrier_eq_chain_union] at hp
  obtain ⟨⟨i, hi⟩, hpi⟩ := mem_iUnion.mp hp
  have hepsilon : (Y.tube.chain.neck i).epsilon ≤ 1 / 200 :=
    (Y.tube.chain.epsilon_eq i hi).trans_le Y.tube.epsilon_le_threshold
  have hNU : (Y.tube.chain.neck i).carrier ⊆ Y.tube.carrier := by
    intro x hx
    rw [Y.tube.carrier_eq_chain_union]
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩
  apply Q.exists_calibrated_strongHorn_of_cappedTube_low_neck A hA K e Y hX hfront hXY
    n htail (Y.tube.chain.neck i) hepsilon hNU rho hrho hrho_r₀ hconstant
    (hlow := ⟨p, hpK, hplow⟩)
  intro x hx
  have h := (Y.tube.chain.neck i).scalar_lt_two_mul_of_mem_carrier
    (Q.extension.extended.connection T) hepsilon
    ((Y.tube.chain.neck i).central_sphere_subset hx) hpi
  rw [← Q.terminal_scalar_eq] at h
  linarith

end PoincareConjecture.SingularLimitConclusion
