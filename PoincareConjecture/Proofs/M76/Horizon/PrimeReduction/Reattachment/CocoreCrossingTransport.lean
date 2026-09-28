import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.RegularCocoreCrossings

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "P3" => ((ℝ × ℝ) × ℝ)

theorem cocore_crossing_charts_of_open_agreement
    {X : Type*} [TopologicalSpace X] {S T G : Set X}
    (Q : OpenPartialHomeomorph X V3) {J : Set V3} (hJQ : J ⊆ Q.target)
    (A : V3 →ᵃ[ℝ] ℝ) (t : ℝ) (hG : IsOpen G)
    (hTG : T ∩ Q.symm '' (Q.target ∩ {x | A x = t}) ⊆ G)
    (hagree : ∀ x ∈ G, x ∈ T ↔ x ∈ S)
    (hcross : ∀ w ∈ (Q '' (S ∩ Q.source) ∩ J) ∩ {x | A x = t},
      ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 P3,
        w ∈ B.source ∧ B.source ⊆ O ∩ interior J ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧
        LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, A x - t = (B x).1.1) :
    ∀ w ∈ (Q '' (T ∩ Q.source) ∩ J) ∩ {x | A x = t},
      ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 P3,
        w ∈ B.source ∧ B.source ⊆ O ∩ interior J ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧
        LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q.symm x ∈ T ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, A x - t = (B x).1.1 := by
  intro w hw O hO hwO
  have hwQ := hJQ hw.1.2
  have hwT : Q.symm w ∈ T := by
    obtain ⟨x,hx,hxw⟩ := hw.1.1
    rw [← hxw,Q.left_inv hx.2]
    exact hx.1
  have hwG := hTG ⟨hwT,⟨w,⟨hwQ,hw.2⟩,rfl⟩⟩
  have hwS : w ∈ (Q '' (S ∩ Q.source) ∩ J) ∩ {x | A x = t} :=
    ⟨⟨⟨Q.symm w,⟨(hagree _ hwG).mp hwT,Q.map_target hwQ⟩,Q.right_inv hwQ⟩,hw.1.2⟩,hw.2⟩
  let V := O ∩ (Q.target ∩ Q.symm ⁻¹' G)
  have hV : IsOpen V := hO.inter (Q.symm.isOpen_inter_preimage hG)
  obtain ⟨B,hwB,hBV,hB0,hB,hBinv,hBS,hBA⟩ := hcross w hwS V hV ⟨hwO,hwQ,hwG⟩
  refine ⟨B,hwB,fun _ hx => ⟨(hBV hx).1.1,(hBV hx).2⟩,hB0,hB,hBinv,?_,hBA⟩
  intro x hx
  exact (hagree _ (hBV hx).1.2.2).trans (hBS x hx)

end PoincareConjecture.M76
