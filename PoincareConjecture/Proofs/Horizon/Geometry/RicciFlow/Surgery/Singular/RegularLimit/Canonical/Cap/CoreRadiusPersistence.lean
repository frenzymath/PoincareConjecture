import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.CoreBallEnlargement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.RadiusBound
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.ScaleMargins
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.TerminalRadius











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





theorem exists_eventually_cap_core_radius_persistence
    (H : SingularTimeAssumptions F T M) (P04 : RicciFlowCurvatureTheory.{u})
    {A : Set (H.regularRegion P04)} (hA : IsCompact A)
    (x₀ : H.regularRegion P04)
    (hx₀ : 0 < (H.terminalConnection P04).scalarCurvature x₀)
    {cmax : ℝ} (hcmax : 1 < cmax) :
    ∃ c : ℝ, 1 < c ∧ c < cmax ∧
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ N : CapCertificate (F.metric t), N.cap_constant ≤ H.constant →
        N.connection = F.connection t →
        H.reference.inverse t ht '' N.carrier ⊆ Subtype.val '' A →
        H.reference.forward t ht x₀ ∈ N.core →
        ∀ x : H.regularRegion P04, H.reference.forward t ht x ∈ N.core →
        ∃ r : ℝ, 0 < r ∧
          N.core_radius (H.reference.forward t ht x) / c ≤ r ∧
          r ≤ c * N.core_radius (H.reference.forward t ht x) ∧
          scalarCurvatureSupOn (H.terminalMetric P04) (H.terminalConnection P04)
            ((H.terminalMetric P04).ball x r) = r⁻¹ ^ 2 ∧
          IsCompact (closure ((H.terminalMetric P04).ball x r)) := by
  let m := (H.terminalConnection P04).scalarCurvature x₀ / 2
  have hm : 0 < m := half_pos hx₀
  let L := H.constant / m + 1
  have hL : 0 < L := by dsimp [L]; positivity [H.constant_pos]
  have hscale : H.constant ≤ m * L ^ 2 := by
    have hcancel : m * (H.constant / m) = H.constant := mul_div_cancel₀ _ (ne_of_gt hm)
    have hnonneg := mul_nonneg hm.le (sq_nonneg (H.constant / m))
    dsimp only [L]
    nlinarith [H.constant_pos]
  obtain ⟨c, hc, hcmax', hgeometry⟩ :=
    H.exists_eventually_cap_core_ball_enlargement P04 hA L hcmax
  obtain ⟨δ, hδ, hmargins⟩ := SingularRegularLimit.exists_uniform_inverse_square_margin hc hL
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hscalar : ∀ᶠ t in 𝓝[<] T, m < H.reference.scalar t x₀ :=
    (H.tendsto_terminal_scalarCurvature P04 x₀).eventually
      (Ioi_mem_nhds (half_lt_self hx₀))
  have hcont := (P04.tensor_calculus 3 (H.regularRegion P04) (H.terminalMetric P04)
    (H.terminalConnection P04)).contMDiff_scalarCurvature.continuous
  refine ⟨c, hc, hcmax', ?_⟩
  filter_upwards [hscalar, hgeometry, H.eventually_cap_core_calibration_close P04 hA hδ]
    with t hscalar hgeometry hcalibration
  intro ht N hconstant hconnection hcapture hx₀core x hxcore
  let ρ := N.core_radius (H.reference.forward t ht x)
  have hρ : 0 < ρ := N.core_radius_pos _ hxcore
  have hbase : m ≤ N.connection.scalarCurvature (H.reference.forward t ht x₀) := by
    rw [hconnection, H.reference.scalar_pullback]
    exact hscalar.le
  have hρL : ρ ≤ L := (N.core_radius_lt_of_scalar_lower hconstant hm hL hscale
    (N.core_subset_carrier hx₀core) hbase hxcore).le
  obtain ⟨hsmall, hlarge, R, hR, hcompact⟩ := hgeometry ht N hcapture x hxcore hρL
  obtain ⟨hleft, hright⟩ := hmargins ρ hρ hρL
  have hab : ρ / c ≤ c * ρ := by
    have h₁ : ρ / c ≤ ρ := (div_le_iff₀ hcpos).mpr (by nlinarith)
    have h₂ : ρ ≤ c * ρ := by nlinarith
    exact h₁.trans h₂
  obtain ⟨r, hr, hcal⟩ := exists_scalar_calibrated_radius_of_sandwich
    (H.terminalMetric P04) (H.terminalConnection P04) hcont x
    (div_pos hρ hcpos) hab hR hcompact hsmall hlarge
    (hcalibration ht N hconnection hcapture _ hxcore).le hleft hright
  refine ⟨r, (div_pos hρ hcpos).trans_le hr.1, hr.1, hr.2, hcal, ?_⟩
  apply hcompact.of_isClosed_subset isClosed_closure
  apply closure_mono
  intro y hy
  exact hy.trans_le (ENNReal.ofReal_le_ofReal (hr.2.trans hR.le))

end PoincareConjecture.SingularTimeAssumptions
