import PoincareConjecture.Proofs.M47.LimitFinitePhysicalCoherence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderChart
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

theorem limitFinite_endpoint_source_diagonal
    {C : GeneralizedSliceCarrier.{u}} (F : ℕ → SurgeryFlowData.{u})
    (index : ℕ → ℕ) (base Q : ℕ → ℝ) (U : ℕ → Set C.carrier)
    (j : ℕ → ℕ) (T : ℝ) (d : ℕ → ℝ)
    (P : ∀ m k b, SurgeryFlowCylinder (F (index k)) C
      (base (index k)) (Q (index k)) (Icc b 0) (U (j m)) → Prop)
    (havailable : ∀ m, ∀ᶠ k in atTop, ∃ b, b ≤ -(T + d m / 2) ∧
      ∃ E : SurgeryFlowCylinder (F (index k)) C
        (base (index k)) (Q (index k)) (Icc b 0) (U (j m)), P m k b E) :
    ∃ eta : ℕ → ℕ, StrictMono eta ∧
      ∃ b : ∀ k m, m ≤ k → ℝ,
        (∀ k m hmk, b k m hmk ≤ -(T + d m / 2)) ∧
        ∃ E : ∀ k m (hmk : m ≤ k), SurgeryFlowCylinder (F (index (eta k))) C
          (base (index (eta k))) (Q (index (eta k))) (Icc (b k m hmk) 0) (U (j m)),
          ∀ k m hmk, P m (eta k) (b k m hmk) (E k m hmk) := by
  classical
  obtain ⟨eta, heta, hrows⟩ :=
    Poincare.exists_strictMono_forall_le_of_eventually havailable
  choose b hb E hE using hrows
  exact ⟨eta, heta, b, hb, E, hE⟩

theorem limitFinite_endpoint_physical_maps
    {C : GeneralizedSliceCarrier.{u}} (F : ℕ → SurgeryFlowData.{u})
    (base Q : ℕ → ℝ) (U : ℕ → Set C.carrier)
    (hU : ∀ k, IsOpen (U k)) (hmono : Monotone U)
    (j : ℕ → ℕ) (hsub : ∀ k, U k ⊆ U (j k))
    {T : ℝ} (hT : 0 < T) (d : ℕ → ℝ) (hd : ∀ k, 0 < d k)
    (b : ℕ → ℝ) (hb : ∀ k, b k ≤ -(T + d k / 2))
    (E : ∀ k, SurgeryFlowCylinder (F k) C (base k) (Q k) (Icc (b k) 0) (U (j k)))
    (Z : ∀ k, C.carrier → ((F k).slice (base k + 0 / Q k)).carrier)
    (hzero : ∀ k (h0 : 0 ∈ Icc (b k) 0) x, x ∈ U (j k) →
      (E k).forward 0 h0 x = Z k x) :
    ∃ psi : ∀ k, PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier
        ((F k).slice (base k + -T / Q k)).carrier ∞,
      (∀ k, (psi k).source = U k) ∧
      (∀ k, ∀ ht : -T ∈ Icc (b k) 0,
        ((psi k : C.carrier → _) = (E k).forward (-T) ht) ∧
        (((psi k).symm : _ → C.carrier) = (E k).inverse (-T) ht)) ∧
      (∀ k, 0 < Q k ∧ base k + -T / Q k ∈ (F k).time_domain ∧
        base k + -T / Q k ∈ Ico 0 (base k)) ∧
      ∀ m k, j m ≤ k → ∀ b' : ℝ, b' ≤ -(T + d m / 2) →
        ∀ E' : SurgeryFlowCylinder (F k) C (base k) (Q k) (Icc b' 0) (U (j m)),
          (∀ (h0 : 0 ∈ Icc b' 0) x, x ∈ U (j m) → E'.forward 0 h0 x = Z k x) →
          ∀ ht : -T ∈ Icc b' 0, EqOn (psi k) (E'.forward (-T) ht) (U (j m)) := by
  classical
  have htime (k : ℕ) : -T ∈ Icc (b k) 0 :=
    ⟨by linarith [hb k, hd k], neg_nonpos.mpr hT.le⟩
  let er := fun k => (E k).restrict (Subset.refl (Icc (b k) 0))
    ordConnected_Icc (hsub k)
  let psi := fun k => M44.cylinderSliceChart (er k) (hU k) (-T) (htime k)
  refine ⟨psi, fun _ => rfl, fun _ _ => ⟨rfl, rfl⟩, ?_, ?_⟩
  · intro k
    have hQ := (E k).scale_pos
    have hdom := (E k).time_subset (mem_image_of_mem _ (htime k))
    exact ⟨hQ, hdom, (F k).time_domain_nonnegative hdom,
      by linarith [div_neg_of_neg_of_pos (neg_neg_of_pos hT) hQ]⟩
  · intro m k hj b' hb' E' hzero' ht' x hx
    have hI : Icc (-T) 0 ⊆ Icc (b k) 0 := Icc_subset_Icc_left (htime k).1
    have hJ : Icc (-T) 0 ⊆ Icc b' 0 := Icc_subset_Icc_left ht'.1
    have hxk : x ∈ U (j k) := hsub k (hmono hj hx)
    exact terminalCommonInterval_physical_eq (E k) E' (neg_nonpos.mpr hT.le)
      hI hJ x hxk x hx ((hzero k _ x hxk).trans (hzero' _ x hx).symm)

end PoincareConjecture.M47
