import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.CutEndpoint

set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem finitePL_annulus_family_slice
    (H : I → Ann ≃ₜ Ann) (F : (ℝ × P2) → P2)
    (hF : FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Ann))
    (hv : ∀ t : I, ∀ x : Ann, F (t, x) = (H t x : P2)) (t : I) :
    (H t).IsFinitePL := by
  obtain ⟨K, hK, hKs⟩ := _root_.Dehn.exists_finite_square_annulus_complex
    (by norm_num : (0 : ℝ) < 1)
    (by norm_num : 4 * (1 : ℝ) < 8)
  let a : P2 →ᴬ[ℝ] (ℝ × P2) :=
    (ContinuousAffineMap.const ℝ P2 (t : ℝ)).prod (ContinuousAffineMap.id ℝ P2)
  have ha : FinitePiecewiseAffineOn a Ann := ⟨K, hK, hKs, K.affineOnFaces_affine a⟩
  exact ⟨F ∘ a, hF.comp ha (fun x hx => ⟨t.property, hx⟩), fun x => (hv t x).symm⟩

def HasJointPLAnnularIsotopy (G : Ann ≃ₜ Ann) : Prop :=
  ∃ (H : I → Ann ≃ₜ Ann) (F Fi : (ℝ × P2) → P2),
    H 0 = Homeomorph.refl Ann ∧ H 1 = G ∧
    FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
    FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
    (∀ t : I, ∀ x : Ann, F (t, x) = (H t x : P2)) ∧
    (∀ t : I, ∀ x : Ann, Fi (t, x) = ((H t).symm x : P2)) ∧
    Continuous (fun p : I × Ann => H p.1 p.2) ∧
    Continuous (fun p : I × Ann => (H p.1).symm p.2) ∧
    ∀ t side z, H t (annulusRimPoint side z) = annulusRimPoint side z

theorem HasJointPLAnnularIsotopy.isFinitePL {G : Ann ≃ₜ Ann}
    (h : HasJointPLAnnularIsotopy G) : G.IsFinitePL := by
  obtain ⟨H, F, _, _, h1, hF, _, hv, _⟩ := h
  exact h1 ▸ finitePL_annulus_family_slice H F hF hv 1

theorem HasJointPLAnnularIsotopy.rims {G : Ann ≃ₜ Ann}
    (h : HasJointPLAnnularIsotopy G) :
    ∀ side z, G (annulusRimPoint side z) = annulusRimPoint side z := by
  obtain ⟨H, _, _, _, h1, _, _, _, _, _, _, hr⟩ := h
  exact h1 ▸ hr 1

theorem HasJointPLAnnularIsotopy.symm {G : Ann ≃ₜ Ann}
    (h : HasJointPLAnnularIsotopy G) : HasJointPLAnnularIsotopy G.symm := by
  obtain ⟨H, F, Fi, h0, h1, hF, hFi, hv, hiv, hc, hci, hr⟩ := h
  refine ⟨fun t => (H t).symm, Fi, F, ?_, ?_, hFi, hF, hiv, ?_, hci, ?_, ?_⟩
  · change (H 0).symm = _
    rw [h0]
    rfl
  · change (H 1).symm = _
    rw [h1]
  · exact hv
  · exact hc
  · intro t side z
    exact (H t).symm_apply_eq.mpr (hr t side z).symm

private theorem joint_track_comp
    (H K : I → Ann ≃ₜ Ann) (F G : (ℝ × P2) → P2)
    (hF : FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Ann))
    (hG : FinitePiecewiseAffineOn G (Icc (0 : ℝ) 1 ×ˢ Ann))
    (hv : ∀ t : I, ∀ x : Ann, F (t, x) = (H t x : P2))
    (hw : ∀ t : I, ∀ x : Ann, G (t, x) = (K t x : P2)) :
    FinitePiecewiseAffineOn (fun x => G (x.1, F x)) (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
    ∀ t : I, ∀ x : Ann, G (t, F (t, x)) = (K t (H t x) : P2) := by
  have hcopy := hF
  obtain ⟨J, hJ, hJs, _⟩ := hcopy
  have hfst : FinitePiecewiseAffineOn (fun x : ℝ × P2 => x.1)
      (Icc (0 : ℝ) 1 ×ˢ Ann) :=
    ⟨J, hJ, hJs, J.affineOnFaces_affine (ContinuousLinearMap.fst ℝ ℝ P2).toContinuousAffineMap⟩
  refine ⟨hG.comp (hfst.prod_mk hF) ?_, ?_⟩
  · intro x hx
    refine ⟨hx.1, ?_⟩
    change F x ∈ Ann
    rw [show F x = (H ⟨x.1, hx.1⟩ ⟨x.2, hx.2⟩ : P2) from
      hv ⟨x.1, hx.1⟩ ⟨x.2, hx.2⟩]
    exact (H _ _).property
  · intro t x
    rw [hv, hw]

theorem HasJointPLAnnularIsotopy.trans {G K : Ann ≃ₜ Ann}
    (hG : HasJointPLAnnularIsotopy G) (hK : HasJointPLAnnularIsotopy K) :
    HasJointPLAnnularIsotopy (G.trans K) := by
  obtain ⟨H, F, Fi, h0, h1, hF, hFi, hv, hiv, hc, hci, hr⟩ := hG
  obtain ⟨J, Q, Qi, j0, j1, hQ, hQi, jv, jiv, jc, jci, jr⟩ := hK
  obtain ⟨hforward, hfv⟩ := joint_track_comp H J F Q hF hQ hv jv
  obtain ⟨hinverse, hiv'⟩ := joint_track_comp (fun t => (J t).symm)
    (fun t => (H t).symm) Qi Fi hQi hFi jiv hiv
  refine ⟨fun t => (H t).trans (J t), (fun x => Q (x.1, F x)),
    (fun x => Fi (x.1, Qi x)), ?_, ?_, hforward, hinverse, hfv, hiv', ?_, ?_, ?_⟩
  · change (H 0).trans (J 0) = _
    rw [h0, j0]
    rfl
  · change (H 1).trans (J 1) = _
    rw [h1, j1]
  · exact jc.comp (continuous_fst.prodMk hc)
  · exact hci.comp (continuous_fst.prodMk jci)
  · intro t side z
    change J t (H t (annulusRimPoint side z)) = _
    rw [hr, jr]

end PoincareConjecture.M76.Dehn
