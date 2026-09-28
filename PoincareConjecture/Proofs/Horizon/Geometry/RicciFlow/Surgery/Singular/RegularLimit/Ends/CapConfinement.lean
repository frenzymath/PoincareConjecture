import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Ends.CapCompactness
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Bounds
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Connected

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.TerminalEnd

variable {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {E : GeneralizedFlowExtension F T} {K : TerminalComponentPath E}

theorem subset_tail_image_of_isPreconnected (e : TerminalEnd K) (k : ℕ)
    {S : Set (E.extended.slice T).carrier} (hS : IsPreconnected S)
    (havoid : Disjoint S (Subtype.val '' (e.exhaustion k : Set K.component)))
    {x : K.component} (hx : x ∈ e.tail k) (hxS : x.val ∈ S) :
    S ⊆ Subtype.val '' e.tail k := by
  have hSK : S ⊆ K.component := by
    have hxK := x.property
    simp only [K.component_eq] at hxK ⊢
    rw [connectedComponent_eq hxK]
    exact hS.subset_connectedComponent hxS
  have hpre : IsPreconnected (Subtype.val ⁻¹' S : Set K.component) := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hSK]
  have hpreavoid : (Subtype.val ⁻¹' S : Set K.component) ⊆ (e.exhaustion k)ᶜ := by
    intro y hy hyk
    exact disjoint_left.mp havoid hy ⟨y, hyk, rfl⟩
  obtain ⟨p, _, htail⟩ := e.tail_component k
  have heq : e.tail k = connectedComponentIn (e.exhaustion k)ᶜ x := by
    rw [htail] at hx ⊢
    exact connectedComponentIn_eq hx
  intro y hy
  refine ⟨⟨y, hSK hy⟩, ?_, rfl⟩
  rw [heq]
  exact hpre.subset_connectedComponentIn hxS hpreavoid hy

theorem exists_tail_caps_subset_tail (e : TerminalEnd K)
    (hlower : ∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x)
    (hproper : ∀ A : Set ℝ, IsCompact A →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' A))
    {C : ℝ} (hC : 0 < C) (k : ℕ) :
    ∃ n : ℕ, k ≤ n ∧ ∀ m : ℕ, n ≤ m → ∀ x ∈ e.tail m,
      ∀ N : CapCertificate (E.extended.metric T), N.cap_constant ≤ C →
        x.val ∈ N.carrier → N.carrier ⊆ Subtype.val '' e.tail k := by
  let D := E.extended.connection T
  have hscalar : Continuous (fun x : K.component => D.scalarCurvature x) :=
    D.continuous_scalarCurvature.comp continuous_subtype_val
  obtain ⟨B, hB⟩ := (e.exhaustion.isCompact k).bddAbove_image hscalar.continuousOn
  obtain ⟨n, hn⟩ := e.exists_tail_scalar_gt hlower hproper (C * max B 0)
  refine ⟨max k n, le_max_left _ _, fun m hnm x hx N hNC hxN => ?_⟩
  have hnx : C * max B 0 < D.scalarCurvature x :=
    hn m ((le_max_right _ _).trans hnm) x hx
  apply e.subset_tail_image_of_isPreconnected k N.isConnected_carrier.isPreconnected
    _ (e.nested ((le_max_left _ _).trans hnm) hx) hxN
  apply disjoint_left.mpr
  rintro y hy ⟨z, hzk, rfl⟩
  have hratio := N.scalar_lt_constant_mul hy hxN
  rw [N.connection.scalarCurvature_eq D x,
    N.connection.scalarCurvature_eq D z] at hratio
  have hzpos : 0 < D.scalarCurvature z := by
    rw [← N.connection.scalarCurvature_eq D z]
    exact N.scalar_pos z hy
  have hzB : D.scalarCurvature z ≤ max B 0 :=
    (hB ⟨z, hzk, rfl⟩).trans (le_max_left _ _)
  have hbound : N.cap_constant * D.scalarCurvature z ≤ C * max B 0 :=
    (mul_le_mul_of_nonneg_right hNC hzpos.le).trans
      (mul_le_mul_of_nonneg_left hzB hC.le)
  exact (hnx.trans (hratio.trans_le hbound)).false

theorem exists_tail_caps_subset_of_contains_tail (e : TerminalEnd K)
    (hlower : ∃ L : ℝ, ∀ x, L ≤ (E.extended.connection T).scalarCurvature x)
    (hproper : ∀ A : Set ℝ, IsCompact A →
      IsCompact ((E.extended.connection T).scalarCurvature ⁻¹' A))
    {C : ℝ} (hC : 0 < C) {U : Set (E.extended.slice T).carrier}
    {k : ℕ} (hU : Subtype.val '' e.tail k ⊆ U) :
    ∃ n : ℕ, k ≤ n ∧ ∀ m : ℕ, n ≤ m → ∀ x ∈ e.tail m,
      ∀ N : CapCertificate (E.extended.metric T), N.cap_constant ≤ C →
        x.val ∈ N.carrier → N.carrier ⊆ U := by
  obtain ⟨n, hkn, hn⟩ := e.exists_tail_caps_subset_tail hlower hproper hC k
  exact ⟨n, hkn, fun m hnm x hx N hNC hxN => (hn m hnm x hx N hNC hxN).trans hU⟩

end PoincareConjecture.TerminalEnd
