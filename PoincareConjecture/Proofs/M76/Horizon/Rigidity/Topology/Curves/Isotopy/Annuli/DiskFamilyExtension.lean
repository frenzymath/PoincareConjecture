import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Disks.SupportedExtension
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.JointPLComposition
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Parameters.RimCircleCoordinates

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip Topology

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_annular_motion_of_closed_disk_family
    {S : Set P2} (hS : IsClosed S)
    (hdepth : S ⊆ depth 8 ⁻¹' Ioo (-1 : ℝ) 1)
    (J : I → S ≃ₜ S) (hzero : J 0 = Homeomorph.refl S)
    (hfix : ∀ t (x : S), (x : P2) ∈ frontier S → J t x = x)
    (hc : Continuous (fun z : I × S => J z.1 z.2))
    (hci : Continuous (fun z : I × S => (J z.1).symm z.2))
    (f fi : (ℝ × P2) → P2)
    (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1 ×ˢ S))
    (hfi : FinitePiecewiseAffineOn fi (Icc (0 : ℝ) 1 ×ˢ S))
    (hv : ∀ t : I, ∀ x : S, f (t, x) = (J t x : P2))
    (hiv : ∀ t : I, ∀ x : S, fi (t, x) = ((J t).symm x : P2)) :
    ∃ (A : I → Ann ≃ₜ Ann) (F Fi : (ℝ × P2) → P2),
      A 0 = Homeomorph.refl Ann ∧
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      (∀ t : I, ∀ x : Ann, F (t, x) = (A t x : P2)) ∧
      (∀ t : I, ∀ x : Ann, Fi (t, x) = ((A t).symm x : P2)) ∧
      Continuous (fun z : I × Ann => A z.1 z.2) ∧
      Continuous (fun z : I × Ann => (A z.1).symm z.2) ∧
      (∀ t side z, A t (annulusRimPoint side z) = annulusRimPoint side z) ∧
      (∀ t (x : Ann), (x : P2) ∉ interior S → A t x = x) ∧
      ∀ t (x : S) (hx : (x : P2) ∈ Ann),
        (A t ⟨x, hx⟩ : P2) = J t x := by
  have hSAnn : S ⊆ Ann := fun x hx => mem_squareAnnulus_iff_depth.mpr
    ⟨(hdepth hx).1.le, (hdepth hx).2.le⟩
  let G (t : I) := (J t).closedExtension hS (hfix t)
  have hfixInv (t : I) (x : S) (hx : (x : P2) ∈ frontier S) : (J t).symm x = x :=
    (J t).symm_apply_eq.mpr (hfix t x hx).symm
  obtain ⟨F, hFv, hF⟩ := Homeomorph.exists_closedExtension_joint_finitePL_track
    hS J hfix hc f hf hv
  obtain ⟨Fi, hFiv, hFi⟩ := Homeomorph.exists_closedExtension_joint_finitePL_track
    hS (fun t => (J t).symm) hfixInv hci fi hfi hiv
  have hGc := Homeomorph.continuous_closedExtension_family J hS hc hfix
  have hGci := Homeomorph.continuous_closedExtension_family_symm J hS hci hfix
  have hfixed (t : I) (x : P2) (hx : x ∉ interior S) : G t x = x := by
    by_cases hxs : x ∈ S
    · exact (J t).closedExtension_apply_frontier hS (hfix t) ⟨subset_closure hxs, hx⟩
    · exact (J t).closedExtension_apply_notMem hS (hfix t) hxs
  have hmapsS (t : I) : MapsTo (G t) S S := by
    intro x hx
    change (J t).closedExtension hS (hfix t) x ∈ S
    rw [(J t).closedExtension_apply_mem hS (hfix t) hx]
    exact (J t ⟨x, hx⟩).property
  have hAnn (t : I) (x : P2) : x ∈ Ann ↔ G t x ∈ Ann := by
    by_cases hx : x ∈ S
    · exact ⟨fun _ => hSAnn (hmapsS t hx), fun _ => hSAnn hx⟩
    · rw [hfixed t x (fun hi => hx (interior_subset hi))]
  let A (t : I) : Ann ≃ₜ Ann := (G t).subtype (hAnn t)
  obtain ⟨K, hK, hKs⟩ := _root_.Dehn.exists_finite_square_annulus_complex
    (by norm_num : (0 : ℝ) < 1) (by norm_num : 4 * (1 : ℝ) < 8)
  refine ⟨A, F, Fi, ?_, hKs ▸ hF K hK, hKs ▸ hFi K hK,
    (fun t x => hFv t x), (fun t x => hFiv t x), ?_, ?_, ?_, ?_, ?_⟩
  · apply Homeomorph.ext
    intro x
    apply Subtype.ext
    change (J 0).closedExtension hS (hfix 0) x = x
    by_cases hx : (x : P2) ∈ S
    · rw [(J 0).closedExtension_apply_mem hS (hfix 0) hx, hzero]
      rfl
    · exact (J 0).closedExtension_apply_notMem hS (hfix 0) hx
  · exact (hGc.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  · exact (hGci.comp (continuous_fst.prodMk
      (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  · intro t side z
    apply Subtype.ext
    apply hfixed
    intro hi
    have hd := hdepth (interior_subset hi)
    change depth 8 (annulusRimPoint side z : P2) ∈ Ioo (-1 : ℝ) 1 at hd
    rw [depth_annulusRimPoint] at hd
    cases side <;> norm_num at hd
  · intro t x hx
    exact Subtype.ext (hfixed t x hx)
  · intro t x hx
    exact (J t).closedExtension_apply_mem hS (hfix t) x.property

end PoincareConjecture.M76.Dehn
