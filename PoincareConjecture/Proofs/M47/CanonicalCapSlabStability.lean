import PoincareConjecture.Proofs.M47.CanonicalCapPersistence
import PoincareConjecture.Proofs.M47.GeneralizedBridgeIsometry
import PoincareConjecture.Proofs.M34.Standard.CapIsometry
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_SlabScalarTransport










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M47

variable {F : SurgeryFlowData.{u}} {a b : ℝ}



theorem eventually_regularSlab_cap_control
    (hC : RicciFlowCurvatureTheory.{u}) (S : SurgeryRegularSlab F.slice F.metric a b)
    (ha : a ∈ F.time_domain) (t : Icc a b)
    (N : CapCertificate (S.flow.metric t.val))
    (hconnection : N.connection = S.flow.connection t.val)
    (hepsilon : N.epsilon = F.parameters.epsilon)
    (hconstant : N.cap_constant ≤ F.parameters.C) :
    ∀ᶠ s : Icc a b in 𝓝 t, ∀ x ∈ N.core,
      SurgeryCanonicalControl F s.val (S.identify s x)
        F.parameters.epsilon F.parameters.C := by
  let : CompactSpace (F.slice a).carrier := isCompact_univ_iff.mp (F.slices_compact a ha)
  filter_upwards [eventually_same_cap_certificate hC S.ordered S.flow t N hconnection]
    with s hs
  obtain ⟨P, hPe, hPC, _, _, hPcore, _, _⟩ := hs
  obtain ⟨H, hHe, hHC, hHconnection, hHcore, _⟩ :=
    P.exists_isometric_image_cap (S.identify s) (M44.regularSlab_metricHomothety F S s)
      (F.connection s.val)
  intro x hx
  apply SurgeryCanonicalControl.cap H (hHe.trans (hPe.trans hepsilon))
    (hHC.le.trans (hPC.le.trans hconstant)) hHconnection
  rw [hHcore, hPcore]
  exact mem_image_of_mem _ hx



theorem regularSlab_limit_not_cap
    (hC : RicciFlowCurvatureTheory.{u}) (S : SurgeryRegularSlab F.slice F.metric a b)
    (ha : a ∈ F.time_domain) (t : Icc a b)
    (times : ℕ → Icc a b) (points : ℕ → (F.slice a).carrier)
    (x : (F.slice a).carrier)
    (htimes : Tendsto (fun n => (times n).val) atTop (𝓝 t.val))
    (hpoints : Tendsto points atTop (𝓝 x))
    (hbad : ∀ n, ¬ SurgeryCanonicalControl F (times n).val
      (S.identify (times n) (points n)) F.parameters.epsilon F.parameters.C)
    (N : CapCertificate (F.metric t.val))
    (hepsilon : N.epsilon = F.parameters.epsilon)
    (hconstant : N.cap_constant ≤ F.parameters.C) :
    S.identify t x ∉ N.core := by
  intro hx
  obtain ⟨P, hPe, hPC, hPconnection, hPcore, _⟩ :=
    N.exists_isometric_image_cap (S.identify t).symm
      (PoincareConjecture.M47.metricHomothety_one_symm (S.identify t)
        (M44.regularSlab_metricHomothety F S t)) (S.flow.connection t.val)
  have hxP : x ∈ P.core := by
    rw [hPcore]
    exact ⟨S.identify t x, hx, (S.identify t).symm_apply_apply x⟩
  have hopen : IsOpen P.core := by
    rw [P.core_eq_interior_closed_core]
    exact isOpen_interior
  have htime : Tendsto times atTop (𝓝 t) := tendsto_subtype_rng.mpr htimes
  have hcanonical := htime.eventually (eventually_regularSlab_cap_control hC S ha t P
    hPconnection (hPe.trans hepsilon) (hPC.le.trans hconstant))
  have hcore := hpoints.eventually (hopen.mem_nhds hxP)
  have hgood : ∀ᶠ n in atTop, SurgeryCanonicalControl F (times n).val
      (S.identify (times n) (points n)) F.parameters.epsilon F.parameters.C := by
    filter_upwards [hcanonical, hcore] with n hn hpoint
    exact hn (points n) hpoint
  obtain ⟨n, hn⟩ := hgood.exists
  exact hbad n hn

end PoincareConjecture.Proofs.M47
