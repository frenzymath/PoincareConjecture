import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.JointPLComposition
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.RadialAlignment
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.TerminalLift



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem hasJointPLAnnularIsotopy_of_radial_invariance
    (G : Ann ≃ₜ Ann) (hG : G.IsFinitePL)
    (hrims : ∀ side z, G (annulusRimPoint side z) = annulusRimPoint side z)
    (hmem : ∀ x : Ann, x ∈ range (fun t : I => annulusCylinderHomeomorph (t, 0)) ↔
      G x ∈ range (fun t : I => annulusCylinderHomeomorph (t, 0))) :
    HasJointPLAnnularIsotopy G := by
  have hfix (x : Ann) (hx : depth 8 (x : P2) = -1 ∨ depth 8 (x : P2) = 1) : G x = x := by
    rcases hx with hx | hx
    · have hx' : x ∈ range (annulusRimPoint false) := by rw [range_annulusRimPoint]; exact hx
      obtain ⟨z, rfl⟩ := hx'
      exact hrims false z
    · have hx' : x ∈ range (annulusRimPoint true) := by rw [range_annulusRimPoint]; exact hx
      obtain ⟨z, rfl⟩ := hx'
      exact hrims true z
  obtain ⟨H, F, Fi, h0, hfixed, hc, hci, hF, hFi, hv, hiv, hcut⟩ :=
    exists_joint_PL_annular_radial_parameter_alignment G hG hfix hmem
  have hH : HasJointPLAnnularIsotopy (H 1) :=
    ⟨H, F, Fi, h0, rfl, hF, hFi, hv, hiv, hc, hci, fun t side z =>
      hfixed t _ (by rw [depth_annulusRimPoint]; cases side <;> simp)⟩
  have hcomposite : HasJointPLAnnularIsotopy (G.trans (H 1)) :=
    exists_joint_PL_annulus_isotopy_of_fixed_radial (G.trans (H 1))
      (hG.trans hH.isFinitePL)
      (fun side z => by change H 1 (G (annulusRimPoint side z)) = _; rw [hrims, hH.rims])
      hcut
  have h := hcomposite.trans hH.symm
  have heq : (G.trans (H 1)).trans (H 1).symm = G := by
    apply Homeomorph.ext
    intro x
    exact (H 1).symm_apply_apply (G x)
  exact heq ▸ h

theorem hasJointPLAnnularIsotopy_of_radial_straightening
    (G : Ann ≃ₜ Ann) (hG : G.IsFinitePL)
    (hrims : ∀ side z, G (annulusRimPoint side z) = annulusRimPoint side z)
    (hstraight : HasJointPLRadialStraightening
      ⟨fun t : I => G (annulusCylinderHomeomorph (t, 0)), by fun_prop⟩) :
    HasJointPLAnnularIsotopy G := by
  obtain ⟨H, F, Fi, h0, hfixed, hc, hci, hF, hFi, hv, hiv, hmem⟩ := hstraight
  have hH : HasJointPLAnnularIsotopy (H 1) :=
    ⟨H, F, Fi, h0, rfl, hF, hFi, hv, hiv, hc, hci, fun t side z =>
      hfixed t _ (by rw [depth_annulusRimPoint]; cases side <;> simp)⟩
  have hcut (x : Ann) : x ∈ range (fun t : I => annulusCylinderHomeomorph (t, 0)) ↔
      (G.trans (H 1)) x ∈ range (fun t : I => annulusCylinderHomeomorph (t, 0)) := by
    change _ ↔ H 1 (G x) ∈ _
    rw [← hmem (G x)]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, G.injective ht⟩
  have hcomposite := hasJointPLAnnularIsotopy_of_radial_invariance
    (G.trans (H 1)) (hG.trans hH.isFinitePL)
    (fun side z => by change H 1 (G (annulusRimPoint side z)) = _; rw [hrims, hH.rims]) hcut
  have h := hcomposite.trans hH.symm
  have heq : (G.trans (H 1)).trans (H 1).symm = G := by
    apply Homeomorph.ext
    intro x
    exact (H 1).symm_apply_apply (G x)
  exact heq ▸ h



theorem HasJointPLRadialStraightening.of_isotopy_image
    (gamma : C(I, Ann)) (G : Ann ≃ₜ Ann)
    (hG : HasJointPLAnnularIsotopy G)
    (hstraight : HasJointPLRadialStraightening
      ⟨fun t => G (gamma t), G.continuous.comp gamma.continuous⟩) :
    HasJointPLRadialStraightening gamma := by
  obtain ⟨K, Q, Qi, k0, kfixed, kc, kci, hQ, hQi, kv, kiv, hmem⟩ := hstraight
  have hK : HasJointPLAnnularIsotopy (K 1) :=
    ⟨K, Q, Qi, k0, rfl, hQ, hQi, kv, kiv, kc, kci, fun t side z =>
      kfixed t _ (by rw [depth_annulusRimPoint]; cases side <;> simp)⟩
  obtain ⟨H, F, Fi, h0, h1, hF, hFi, hv, hiv, hc, hci, hrims⟩ := hG.trans hK
  refine ⟨H, F, Fi, h0, ?_, hc, hci, hF, hFi, hv, hiv, ?_⟩
  · intro t x hx
    rcases hx with hx | hx
    · have hx' : x ∈ range (annulusRimPoint false) := by rw [range_annulusRimPoint]; exact hx
      obtain ⟨z, rfl⟩ := hx'
      exact hrims t false z
    · have hx' : x ∈ range (annulusRimPoint true) := by rw [range_annulusRimPoint]; exact hx
      obtain ⟨z, rfl⟩ := hx'
      exact hrims t true z
  · intro x
    rw [h1]
    change x ∈ range gamma ↔ K 1 (G x) ∈ _
    rw [← hmem (G x)]
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, rfl⟩
    · rintro ⟨t, ht⟩
      exact ⟨t, G.injective ht⟩

end PoincareConjecture.M76.Dehn
