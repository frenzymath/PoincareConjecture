import PoincareConjecture.Proofs.M47.CanonicalCapNearbyPhysical
import PoincareConjecture.Proofs.M47.CanonicalStandardCapCarrier









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

open PoincareConjecture.M47



theorem exists_compact_standard_cap_physical_tolerance_above {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {theta gamma C R : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1) (hC : 0 < C) (hR : 0 ≤ R)
    {K : Set (ℝ × StandardCapSpace)} (hK : IsCompact K)
    (hKsub : K ⊆ Icc 0 theta ×ˢ {x | g0.metric.edist 0 x ≤ ENNReal.ofReal R})
    (hcaps : ∀ p ∈ K, ∃ N : CapCertificate (P.standard_cap.flow.metric p.1),
      N.epsilon = gamma ∧ N.cap_constant ≤ C ∧
      N.connection = P.standard_cap.flow.connection p.1 ∧ p.2 ∈ N.core) :
    ∃ A0 : ℝ, 0 < A0 ∧ R < A0 ∧ ∀ A : ℝ, A0 ≤ A →
      ∃ eta0 : ℝ, 0 < eta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S P.standard_cap.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (_hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J)
        (x : StandardCapSpace), (s, x) ∈ K →
      let q := actualCapSliceChart e initial comparison s hs
      let Q := (F.parameters.h t)⁻¹ ^ 2
      ∃ H : CapCertificate (F.metric (t + s / Q)),
        H.epsilon = gamma ∧ H.cap_constant ≤ C ∧
        H.connection = F.connection (t + s / Q) ∧ q x ∈ H.core := by
  classical
  obtain ⟨A0, hA0, hRA0, hcontain⟩ :=
    exists_standard_cap_uniform_initial_ball P htheta0 htheta hC hR
  refine ⟨A0, hA0, hRA0, ?_⟩
  intro A hAA0
  have hA : 0 < A := hA0.trans_le hAA0
  choose N hNe hNC hND hNx using fun p : K => hcaps p.val p.property
  have hsource (p : K) : (N p).carrier ⊆ g0.metric.ball 0 A := by
    intro x hx
    have h := (hcontain p.val.1 (hKsub p.property).1 (N p)
      (hND p) (hNC p) p.val.2 (hNx p) (hKsub p.property).2).2 (subset_closure hx)
    exact h.trans_le (ENNReal.ofReal_le_ofReal hAA0)
  choose eta delta heta hdelta transfer using fun p : K =>
    exists_actualCap_nearby_physical_certificate_tolerance P.standard_cap htheta hA
      (hKsub p.property).1 (N p) (hND p) (hsource p)
  let V (p : K) : Set (ℝ × StandardCapSpace) :=
    {s | |s - p.val.1| < delta p} ×ˢ (N p).core
  have hV (p : K) : IsOpen (V p) := by
    apply IsOpen.prod (isOpen_lt (continuous_id.sub continuous_const).abs continuous_const)
    rw [(N p).core_eq_interior_closed_core]
    exact isOpen_interior
  have hcover : K ⊆ ⋃ p : K, V p := by
    intro p hp
    refine mem_iUnion.mpr ⟨⟨p, hp⟩, ?_, hNx ⟨p, hp⟩⟩
    simpa only [mem_ofPred_eq, sub_self, abs_zero] using hdelta ⟨p, hp⟩
  obtain ⟨T, hTcover⟩ := hK.elim_finite_subcover V hV hcover
  have hmin (T : Finset K) : ∃ eta0 : ℝ, 0 < eta0 ∧ ∀ p ∈ T, eta0 ≤ eta p := by
    induction T using Finset.induction with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert p T _ ih =>
        obtain ⟨eta0, heta0, hsmall⟩ := ih
        refine ⟨min (eta p) eta0, lt_min (heta p) heta0, ?_⟩
        intro q hq
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact min_le_left _ _
        · exact (min_le_right _ _).trans (hsmall q hq)
  obtain ⟨eta0, heta0, hsmall⟩ := hmin T
  refine ⟨eta0, heta0, ?_⟩
  intro F hinitial S hS t hT hn i J U e initial eta' heta' hetamax comparison hh s hs x hx
  obtain ⟨p, hpT, hpV⟩ := mem_iUnion₂.mp (hTcover hx)
  obtain ⟨H, hHe, hHC, hHD, hHcore, _⟩ :=
    transfer p F hinitial S hS t hT hn i J U e initial eta' heta'
      (hetamax.trans (hsmall p hpT)) comparison hh s hs (hKsub hx).1.2 hpV.1
  refine ⟨H, hHe.trans (hNe p), hHC.le.trans (hNC p), hHD, ?_⟩
  rw [hHcore]
  exact mem_image_of_mem _ hpV.2




theorem exists_compact_standard_cap_physical_tolerance {g0 : StandardInitialMetric}
    (P : RepairedCapPersistenceData.{u} g0) {theta gamma C R : ℝ}
    (htheta0 : 0 ≤ theta) (htheta : theta < 1) (hC : 0 < C) (hR : 0 ≤ R)
    {K : Set (ℝ × StandardCapSpace)} (hK : IsCompact K)
    (hKsub : K ⊆ Icc 0 theta ×ˢ {x | g0.metric.edist 0 x ≤ ENNReal.ofReal R})
    (hcaps : ∀ p ∈ K, ∃ N : CapCertificate (P.standard_cap.flow.metric p.1),
      N.epsilon = gamma ∧ N.cap_constant ≤ C ∧
      N.connection = P.standard_cap.flow.connection p.1 ∧ p.2 ∈ N.core) :
    ∃ A eta0 : ℝ, 0 < A ∧ R < A ∧ 0 < eta0 ∧
      ∀ (F : SurgeryFlowData.{u}) (_hinitial : F.standard_initial = g0)
        (S : MaximalStandardCapFlow F.standard_initial), HEq S P.standard_cap.flow →
      ∀ (t : ℝ) (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (J : Set ℝ) (U : Set (F.slice t).carrier)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
        (initial : SurgeryCapInitialComparison F t hT i A)
        (eta : ℝ), 0 < eta → eta ≤ eta0 →
      ∀ (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
        (_hh : 0 < F.parameters.h t) (s : ℝ) (hs : s ∈ J)
        (x : StandardCapSpace), (s, x) ∈ K →
      let q := actualCapSliceChart e initial comparison s hs
      let Q := (F.parameters.h t)⁻¹ ^ 2
      ∃ H : CapCertificate (F.metric (t + s / Q)),
        H.epsilon = gamma ∧ H.cap_constant ≤ C ∧
        H.connection = F.connection (t + s / Q) ∧ q x ∈ H.core := by
  obtain ⟨A, hA, hRA, tolerances⟩ :=
    exists_compact_standard_cap_physical_tolerance_above P htheta0 htheta hC hR hK hKsub hcaps
  obtain ⟨eta0, heta0, transfer⟩ := tolerances A le_rfl
  exact ⟨A, eta0, hA, hRA, heta0, transfer⟩

end PoincareConjecture.Proofs.M47
