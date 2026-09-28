import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Ends.NeckBoundary

noncomputable section
set_option autoImplicit false

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

theorem neck_disjoint_low_core_of_high_point (Q : SingularLimitConclusion H)
    (N : EpsilonNeck (Q.extension.extended.metric T)) (hε : N.epsilon ≤ 1 / 200)
    (rho : ℝ) (hconstant : 1 ≤ H.constant)
    (hhigh : ∃ x ∈ N.carrier, 2 * H.constant * rho⁻¹ ^ 2 ≤ Q.terminal_scalar x) :
    Disjoint N.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} := by
  obtain ⟨x, hx, hhigh⟩ := hhigh
  refine disjoint_left.mpr fun y hy hlow => ?_
  have hratio := N.scalar_lt_two_mul_of_mem_carrier
    (Q.extension.extended.connection T) hε hx hy
  rw [← Q.terminal_scalar_eq] at hratio
  have hprod := mul_le_mul_of_nonneg_right hconstant (sq_nonneg rho⁻¹)
  change Q.terminal_scalar y ≤ rho⁻¹ ^ 2 at hlow
  nlinarith

theorem cap_disjoint_low_core_of_linear_high_point (Q : SingularLimitConclusion H)
    (cap : CapCertificate (Q.extension.extended.metric T))
    (rho : ℝ) (hcap : cap.cap_constant ≤ 2 * H.constant)
    (hhigh : ∃ x ∈ cap.carrier, 2 * H.constant * rho⁻¹ ^ 2 ≤ Q.terminal_scalar x) :
    Disjoint cap.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} := by
  obtain ⟨x, hx, hxhigh⟩ := hhigh
  have heq (z) : cap.connection.scalarCurvature z = Q.terminal_scalar z := by
    rw [Q.terminal_scalar_eq]
    exact cap.connection.scalarCurvature_eq _ z
  refine disjoint_left.mpr fun y hy hylow => ?_
  have hratio := cap.scalar_lt_constant_mul hy hx
  rw [heq x, heq y] at hratio
  have hpos : 0 < Q.terminal_scalar y := by
    rw [← heq y]
    exact cap.scalar_pos y hy
  have hupper := (mul_le_mul_of_nonneg_right hcap hpos.le).trans
    (mul_le_mul_of_nonneg_left hylow (by positivity [H.constant_pos] : 0 ≤ 2 * H.constant))
  exact (not_lt_of_ge hxhigh) (hratio.trans_le hupper)

theorem cap_below_calibrated_level_of_linear_low_point (Q : SingularLimitConclusion H)
    (cap : CapCertificate (Q.extension.extended.metric T))
    (rho : ℝ) (hcap : cap.cap_constant ≤ 2 * H.constant)
    (hlow : ∃ x ∈ cap.carrier, Q.terminal_scalar x ≤ 2 * H.constant * rho⁻¹ ^ 2) :
    ∀ y ∈ cap.carrier, Q.terminal_scalar y < (rho / (2 * H.constant))⁻¹ ^ 2 := by
  obtain ⟨x, hx, hxlow⟩ := hlow
  have heq (z) : cap.connection.scalarCurvature z = Q.terminal_scalar z := by
    rw [Q.terminal_scalar_eq]
    exact cap.connection.scalarCurvature_eq _ z
  intro y hy
  have hratio := cap.scalar_lt_constant_mul hx hy
  rw [heq x, heq y] at hratio
  have hpos : 0 < Q.terminal_scalar x := by
    rw [← heq x]
    exact cap.scalar_pos x hx
  have hupper := (mul_le_mul_of_nonneg_right hcap hpos.le).trans
    (mul_le_mul_of_nonneg_left hxlow (by positivity [H.constant_pos] : 0 ≤ 2 * H.constant))
  have hid : (rho / (2 * H.constant))⁻¹ ^ 2 =
      2 * H.constant * (2 * H.constant * rho⁻¹ ^ 2) := by
    rw [inv_div, div_eq_mul_inv]
    ring
  rw [hid]
  exact hratio.trans_le hupper

theorem exists_linear_calibrated_end_region (Q : SingularLimitConclusion H)
    (K : TerminalComponentPath Q.extension) (e : TerminalEnd K)
    (rho : ℝ) (hrho : 0 < rho) (hrho_r₀ : rho < H.r₀)
    (hconstant : 1 ≤ H.constant)
    (hcore : ∃ x ∈ K.component, Q.terminal_scalar x ≤ rho⁻¹ ^ 2) :
    ∃ (n : ℕ) (X : Set (Q.extension.extended.slice T).carrier),
      IsClosed X ∧ IsConnected X ∧ X ⊆ K.component ∧
      Subtype.val '' e.tail n ⊆ X ∧ ¬ IsCompact X ∧
      (∀ x ∈ X, 2 * H.constant * rho⁻¹ ^ 2 ≤ Q.terminal_scalar x) ∧
      (∀ x ∈ X, H.r₀⁻¹ ^ 2 < Q.terminal_scalar x) ∧
      ∃ x ∈ X, Q.terminal_scalar x = 2 * H.constant * rho⁻¹ ^ 2 := by
  have hrho_sq : 0 < rho⁻¹ ^ 2 := sq_pos_of_pos (inv_pos.mpr hrho)
  have hlevel : rho⁻¹ ^ 2 < 2 * H.constant * rho⁻¹ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hconstant hrho_sq.le]
  have hr₀_sq : H.r₀⁻¹ ^ 2 ≤ rho⁻¹ ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr H.r₀_pos.le)
      ((inv_le_inv₀ H.r₀_pos hrho).mpr hrho_r₀.le) 2
  obtain ⟨n, X, hclosed, hconn, hsub, htail, hnoncompact, hlower, hattain⟩ :=
    Q.exists_end_superlevel_region K e (2 * H.constant * rho⁻¹ ^ 2)
      (by obtain ⟨x, hx, hcurv⟩ := hcore; exact ⟨x, hx, hcurv.trans_lt hlevel⟩)
  exact ⟨n, X, hclosed, hconn, hsub, htail, hnoncompact, hlower,
    fun x hx => hr₀_sq.trans_lt (hlevel.trans_le (hlower x hx)), hattain⟩

theorem cappedTube_cap_disjoint_core_or_subset_tube (Q : SingularLimitConclusion H)
    (Y : CappedTubeCertificate (Q.extension.extended.metric T))
    {X : Set (Q.extension.extended.slice T).carrier} (hX : X ⊆ Y.carrier)
    (rho : ℝ) (hcap : Y.cap.cap_constant ≤ 2 * H.constant)
    (hhigh : ∀ x ∈ X, 2 * H.constant * rho⁻¹ ^ 2 ≤ Q.terminal_scalar x) :
    Disjoint Y.cap.carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} ∨ X ⊆ Y.tube.carrier := by
  by_cases hmeet : (X ∩ Y.cap.carrier).Nonempty
  · obtain ⟨x, hx, hxcap⟩ := hmeet
    exact Or.inl (Q.cap_disjoint_low_core_of_linear_high_point Y.cap rho hcap
      ⟨x, hxcap, hhigh x hx⟩)
  · right
    intro x hx
    have hy := hX hx
    rw [Y.carrier_eq_union] at hy
    exact hy.resolve_left (fun hcap => hmeet ⟨x, hx, hcap⟩)

theorem tube_neck_disjoint_core_of_inter_high_region (Q : SingularLimitConclusion H)
    {Y X : Set (Q.extension.extended.slice T).carrier}
    (tube : EpsilonTubeCertificate (Q.extension.extended.metric T) Y)
    (rho : ℝ) (hconstant : 1 ≤ H.constant)
    (hhigh : ∀ x ∈ X, 2 * H.constant * rho⁻¹ ^ 2 ≤ Q.terminal_scalar x)
    (i : ℤ) (hi : i ∈ tube.chain.shape.active)
    (hmeet : (X ∩ (tube.chain.neck i).carrier).Nonempty) :
    Disjoint (tube.chain.neck i).carrier {x | Q.terminal_scalar x ≤ rho⁻¹ ^ 2} := by
  obtain ⟨x, hx, hxN⟩ := hmeet
  exact Q.neck_disjoint_low_core_of_high_point (tube.chain.neck i)
    ((tube.chain.epsilon_eq i hi).trans_le tube.epsilon_le_threshold) rho hconstant
      ⟨x, hxN, hhigh x hx⟩

end PoincareConjecture.SingularLimitConclusion
