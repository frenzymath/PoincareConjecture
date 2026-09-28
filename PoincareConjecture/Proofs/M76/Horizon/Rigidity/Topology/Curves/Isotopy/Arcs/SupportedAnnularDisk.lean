import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Disks.SupportedExtension
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod



set_option autoImplicit false
open Set Geometry PLAnnularStrip Topology unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_joint_PL_supported_annular_disk_isotopy
    {S : Set P2} (hS : IsFinitePLBallPair P2 S (frontier S)) (hSAnn : S ⊆ Ann)
    (hrimS : ∀ x ∈ S, depth 8 x = -1 ∨ depth 8 x = 1 → x ∈ frontier S)
    (e : S ≃ₜ S) (he : e.IsFinitePL)
    (hefix : ∀ x : S, (x : P2) ∈ frontier S → e x = x) :
    ∃ (H : I → Ann ≃ₜ Ann) (F Fi : (ℝ × P2) → P2),
      H 0 = Homeomorph.refl Ann ∧
      (∀ t : I, ∀ x : Ann, depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1 → H t x = x) ∧
      (∀ t : I, ∀ x : Ann, (x : P2) ∉ interior S → H t x = x) ∧
      Continuous (fun z : I × Ann => H z.1 z.2) ∧
      Continuous (fun z : I × Ann => (H z.1).symm z.2) ∧
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      (∀ t : I, ∀ x : Ann, F ((t : ℝ), x) = (H t x : P2)) ∧
      (∀ t : I, ∀ x : Ann, Fi ((t : ℝ), x) = ((H t).symm x : P2)) ∧
      ∀ x : S, H 1 ⟨x, hSAnn x.property⟩ = ⟨e x, hSAnn (e x).property⟩ := by
  obtain ⟨G, F, Fi, hGzero, hGone, hc, hci, hfixed, hFv, hFiv, hPL⟩ :=
    hS.exists_supported_joint_PL_isotopy e he hefix
  have hfixoff (t : I) (x : P2) (hx : x ∉ S) : G t x = x :=
    hfixed t x (fun h => hx (interior_subset h))
  have hmapsS (t : I) : MapsTo (G t) S S := by
    intro x hx
    by_contra hn
    have heq : G t x = x := (G t).injective (hfixoff t (G t x) hn)
    exact hn (heq.symm ▸ hx)
  have hAnn (t : I) (x : P2) : x ∈ Ann ↔ G t x ∈ Ann := by
    by_cases hx : x ∈ S
    · exact ⟨fun _ => hSAnn (hmapsS t hx), fun _ => hSAnn hx⟩
    · rw [hfixoff t x hx]
  let H : I → Ann ≃ₜ Ann := fun t => (G t).subtype (hAnn t)
  have hHv (t : I) (x : Ann) : (H t x : P2) = G t x := rfl
  obtain ⟨K, hK, hKs⟩ := _root_.Dehn.exists_finite_square_annulus_complex
    (by norm_num : (0 : ℝ) < 1) (by norm_num : 4 * (1 : ℝ) < 8)
  have htracks := hPL K hK
  rw [hKs] at htracks
  refine ⟨H, F, Fi, ?_, ?_, ?_, ?_, ?_, htracks.1, htracks.2,
    fun t x => hFv t x, fun t x => hFiv t x, ?_⟩
  · apply Homeomorph.ext
    intro x
    apply Subtype.ext
    rw [hHv, hGzero]
    rfl
  · intro t x hx
    apply Subtype.ext
    rw [hHv]
    apply hfixed
    intro hxi
    exact (hrimS x (interior_subset hxi) hx).2 hxi
  · intro t x hx
    exact Subtype.ext (hfixed t x hx)
  · apply IsEmbedding.subtypeVal.continuous_iff.mpr
    exact hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  · apply IsEmbedding.subtypeVal.continuous_iff.mpr
    exact hci.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  · intro x
    apply Subtype.ext
    rw [hHv, hGone, e.closedExtension_apply_mem hS.isCompact.isClosed hefix x.property]

end PoincareConjecture.M76.Dehn
