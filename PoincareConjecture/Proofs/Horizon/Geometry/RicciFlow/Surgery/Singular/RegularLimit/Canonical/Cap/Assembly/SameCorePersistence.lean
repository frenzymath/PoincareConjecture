import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.TerminalAccuracy
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Assembly.Construction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Assembly.SameCoreBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Cap.Core.Truncation.SameCoreBoundary
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Static.CapBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Static.Recenter
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.Static.RestrictionTransfer



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.SingularRegularLimit


theorem exists_terminal_same_core_cap_persistence_threshold_of_budget
    (P04 : RicciFlowCurvatureTheory.{u}) {κ : ℝ} (hκ : 4 < κ)
    (hbudget : 32 + 6 * (2000000000004 : ℝ) ^ 2 < κ ^ 2) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M), H.epsilon ≤ ε₀ →
        ∀ {A : Set (H.regularRegion P04)}, IsCompact A →
        ∀ x₀ : H.regularRegion P04, 0 < (H.terminalConnection P04).scalarCurvature x₀ →
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ C : CapCertificate (F.metric t), C.epsilon = H.epsilon →
          C.cap_constant ≤ H.constant → C.connection = F.connection t →
          H.reference.inverse t ht '' C.carrier ⊆ Subtype.val '' A →
          H.reference.forward t ht x₀ ∈ C.core →
          ∃ N : CapCertificate (H.terminalMetric P04),
            N.epsilon = κ * H.epsilon ∧ N.cap_constant ≤ 2 * H.constant ∧
            N.connection = H.terminalConnection P04 ∧ x₀ ∈ N.core := by
  obtain ⟨ε₁, hε₁, _, htopology⟩ :=
    exists_terminal_same_core_truncated_domain_topology_threshold.{u}
  obtain ⟨ε₂, hε₂, _, hboundary⟩ :=
    CapCertificate.exists_same_core_boundary_region_subset_threshold.{u}
  obtain ⟨ε₃, hε₃, _, hquantitative⟩ :=
    exists_terminal_cap_same_core_quantitative_threshold.{u}
  have hκpos : 0 < κ := by linarith
  let ε₀ := min (min ε₁ ε₂) (min ε₃ (min (1 / 10000000000000) (1 / (200 * κ))))
  have hε₀ : 0 < ε₀ := lt_min (lt_min hε₁ hε₂)
    (lt_min hε₃ (lt_min (by norm_num) (by positivity)))
  have hsmall₀ : ε₀ ≤ 1 / 10000000000000 :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  refine ⟨ε₀, hε₀, by linarith, ?_⟩
  intro M _ _ _ _ _ _ _ _ F T H hε A hA x₀ hx₀
  have he₁ : H.epsilon ≤ ε₁ := hε.trans ((min_le_left _ _).trans (min_le_left _ _))
  have he₂ : H.epsilon ≤ ε₂ := hε.trans ((min_le_left _ _).trans (min_le_right _ _))
  have he₃ : H.epsilon ≤ ε₃ := hε.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hesmall := hε.trans hsmall₀
  have heκ : H.epsilon ≤ 1 / (200 * κ) :=
    hε.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  let δ := κ * H.epsilon
  have hδ : 0 < δ := mul_pos hκpos H.epsilon_pos
  have hδsmall : δ ≤ 1 / 200 := by
    have := (le_div_iff₀ (by positivity : 0 < 200 * κ)).mp heκ
    dsimp [δ]
    nlinarith
  have hεδ : 2 * H.epsilon ≤ δ := by dsimp [δ]; nlinarith [H.epsilon_pos]
  have hjet : (32 + 6 * (2000000000004 : ℝ) ^ 2) * H.epsilon ^ 2 < δ ^ 2 := by
    simpa only [δ, mul_pow] using mul_lt_mul_of_pos_right hbudget (sq_pos_of_pos H.epsilon_pos)
  obtain ⟨l, u, hl, hu, hscalar⟩ :=
    H.exists_eventually_captured_cap_neck_scalar_bounds P04 hA x₀ hx₀
  obtain ⟨s, _, hsT, hboundaryNeck⟩ :=
    H.exists_late_captured_static_neck_transfer_of_two_le P04 hA H.epsilon_pos
      (by linarith) hεδ (by linarith) hl hu x₀
  filter_upwards [hscalar, hquantitative H P04 hA x₀ hx₀,
    Ioo_mem_nhdsLT hsT,
    H.eventually_static_neck_terminal_recenter P04 hA H.epsilon_pos hesmall
      hεδ (by linarith) hl hu hjet] with t hscalar hquant htlate hneck
  intro ht C hCe hCC hCD hcapture hxcore
  have hcapture' : H.reference.inverse t ht '' C.carrier ⊆ H.reference.regularLimitSet := by
    rintro y hy
    obtain ⟨z, _, rfl⟩ := hcapture hy
    exact z.property
  have hendcapture : MapsTo (H.reference.inverse t ht) C.end_neck.carrier
      H.reference.regularLimitSet := fun y hy =>
    hcapture' (mem_image_of_mem _ (C.end_neck_subset hy))
  let E := H.regularStaticNeck P04 ht C.end_neck x₀ hendcapture
  have hEe : E.epsilon = H.epsilon := C.end_neck_epsilon.trans hCe
  have hEA : E.carrier ⊆ A := H.regularReferencePreimage_subset P04 t ht _
    ((image_mono C.end_neck_subset).trans hcapture)
  obtain ⟨hEl, hEu⟩ := hscalar ht C hCC hCD hcapture hxcore C.end_neck C.end_neck_subset
  have hEq := H.regularStaticNeck_scalar_center P04 ht C.end_neck x₀ hendcapture
  let r := δ⁻¹
  let L := C.epsilon⁻¹
  have hr : 0 < r := inv_pos.mpr hδ
  have hrlarge : 200 ≤ r := by
    have := one_div_le_one_div_of_le hδ hδsmall
    norm_num only [one_div_one_div, div_inv_eq_mul, mul_one, one_div] at this
    exact this
  have hL : L = κ * r := by
    dsimp [L, r, δ]
    rw [hCe, mul_inv_rev, mul_left_comm, mul_inv_cancel₀ hκpos.ne', mul_one]
  let b := -L + 2 * r
  let d := -L + r / 2
  let shift := -L + r
  have hb : -L < b := by dsimp [b]; linarith
  have hbhalf : b < -L / 2 := by
    have := mul_lt_mul_of_pos_right hκ hr
    dsimp [b]
    rw [← hL] at this
    linarith
  have hbL : b < L := by have : 0 < L := hL ▸ mul_pos hκpos hr; linarith
  have hd : -L < d := by dsimp [d]; linarith
  have hsub : MapsTo (fun z : ℝ => z + shift)
      (Ioo (-δ⁻¹) δ⁻¹) (Ioo (-H.epsilon⁻¹) H.epsilon⁻¹) := by
    intro z hz
    change -r < z ∧ z < r at hz
    have hLe : L = H.epsilon⁻¹ := by dsimp [L]; rw [hCe]
    rw [← hLe]
    dsimp [shift, b] at *
    constructor <;> linarith
  obtain ⟨N, hNe, hND, _, _, hNU, hNregion⟩ :=
    hneck E hEe hEA (by simpa only [E, hEq] using hEl)
      (by simpa only [E, hEq] using hEu) shift
      (Classical.arbitrary UnitTwoSphere) hsub
  have hNU' : N.carrier = H.regularReferencePreimage P04 t ht
      (C.end_neck.region (-L) b) := by
    rw [hNU]
    have hleft : -δ⁻¹ + shift = -L := by dsimp [shift, r]; ring
    have hright : δ⁻¹ + shift = b := by dsimp [shift, b, r]; ring
    rw [hleft, hright]
    rfl
  have hNneg : N.region (-δ⁻¹) (-δ⁻¹ / 2) =
      H.regularReferencePreimage P04 t ht (C.end_neck.region (-L) d) := by
    rw [hNregion _ _ le_rfl (by dsimp [r] at hr; linarith)]
    have hleft : -δ⁻¹ + shift = -L := by dsimp [shift, r]; ring
    have hright : -δ⁻¹ / 2 + shift = d := by dsimp [shift, d, r]; ring
    rw [hleft, hright]
    rfl
  obtain ⟨hBl, hBu⟩ := hscalar ht C hCC hCD hcapture hxcore C.boundary_neck C.boundary_neck_subset
  obtain ⟨B, hBe, hBD, _, _, _, _, hBsphere, hBU, _⟩ :=
    hboundaryNeck t ht htlate.1.le C.boundary_neck
      (C.boundary_neck_epsilon.trans hCe)
      ((image_mono C.boundary_neck_subset).trans hcapture) hBl hBu
  obtain ⟨topology⟩ := htopology H P04 ht C (hCe ▸ he₁) hcapture' x₀ hxcore b d hb hbL hd
  rw [← hNU', ← hNneg] at topology
  obtain ⟨quantitative⟩ := hquant ht C (hCe ▸ he₃) hCC hCD hcapture hxcore b
    (by dsimp [b]; linarith) hbL
  have hBsub := hboundary C (hCe ▸ he₂) b r hb hbhalf hr (by
    have := Real.pi_lt_four
    change r < 0.9 * (L + b) - 5 * Real.pi
    dsimp [b]
    linarith)
  obtain ⟨K, hKe, hKC, hKD, _, hKcore, _⟩ := exists_cap_of_linked_necks
    (H.terminalMetric P04) (H.terminalConnection P04) hδsmall
    (by positivity [H.constant_pos]) C.model_kind C.puncture _ _ _ _ N B hNe hBe hND hBD
    (by rw [hBU]; exact preimage_mono hBsub)
    (by rw [hBsphere, ← C.boundary_eq_neck_sphere]) topology quantitative
  exact ⟨K, hKe, hKC.le, hKD, hKcore.symm ▸ hxcore⟩



theorem exists_terminal_same_core_cap_persistence_threshold
    (P04 : RicciFlowCurvatureTheory.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
        (H : SingularTimeAssumptions F T M), H.epsilon ≤ ε₀ →
        ∀ {A : Set (H.regularRegion P04)}, IsCompact A →
        ∀ x₀ : H.regularRegion P04, 0 < (H.terminalConnection P04).scalarCurvature x₀ →
      ∀ᶠ t in 𝓝[<] T, ∀ ht : t ∈ Ico H.reference.tMinus T,
        ∀ C : CapCertificate (F.metric t), C.epsilon = H.epsilon →
          C.cap_constant ≤ H.constant → C.connection = F.connection t →
          H.reference.inverse t ht '' C.carrier ⊆ Subtype.val '' A →
          H.reference.forward t ht x₀ ∈ C.core →
          ∃ N : CapCertificate (H.terminalMetric P04),
            N.epsilon = terminalAccuracyFactor * H.epsilon ∧
            N.cap_constant ≤ 2 * H.constant ∧
            N.connection = H.terminalConnection P04 ∧ x₀ ∈ N.core :=
  exists_terminal_same_core_cap_persistence_threshold_of_budget P04
    four_lt_terminalAccuracyFactor terminalAccuracyFactor_scalar_ratio_budget

end PoincareConjecture.SingularRegularLimit
