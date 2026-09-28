import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.CocoreCrossingTransport

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem frontier_crossing_charts_of_open_agreement
    {X : Type*} [TopologicalSpace X] {S T F G : Set X}
    (Q : OpenPartialHomeomorph X V3) (hFQ : F ⊆ Q.source)
    (hG : IsOpen G) (hTG : T ∩ F ⊆ G)
    (hagree : ∀ x ∈ G, x ∈ T ↔ x ∈ S)
    (hcross : ∀ w ∈ Q '' (S ∩ F), ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 C3,
        w ∈ B.source ∧ B.source ⊆ O ∩ Q.target ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q.symm x ∈ S ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, Q.symm x ∈ F ↔ (B x).1.1 = 0) :
    ∀ w ∈ Q '' (T ∩ F), ∀ O : Set V3, IsOpen O → w ∈ O →
      ∃ B : OpenPartialHomeomorph V3 C3,
        w ∈ B.source ∧ B.source ⊆ O ∩ Q.target ∧ B w = 0 ∧
        LocallyPiecewiseAffineOn B B.source ∧ LocallyPiecewiseAffineOn B.symm B.target ∧
        (∀ x ∈ B.source, Q.symm x ∈ T ↔ (B x).2 = 0) ∧
        ∀ x ∈ B.source, Q.symm x ∈ F ↔ (B x).1.1 = 0 := by
  intro w hw O hO hwO
  obtain ⟨y,hy,rfl⟩ := hw
  have hyQ := hFQ hy.2
  have hyG := hTG hy
  have hyS : y ∈ S := (hagree y hyG).mp hy.1
  let V := O ∩ (Q.target ∩ Q.symm ⁻¹' G)
  have hV : IsOpen V := hO.inter (Q.symm.isOpen_inter_preimage hG)
  have hyV : Q y ∈ V := ⟨hwO,Q.map_source hyQ,by
    change Q.symm (Q y) ∈ G
    rwa [Q.left_inv hyQ]⟩
  obtain ⟨B,hyB,hBV,hB0,hB,hBi,hBS,hBF⟩ :=
    hcross (Q y) ⟨y,⟨hyS,hy.2⟩,rfl⟩ V hV hyV
  refine ⟨B,hyB,(fun x hx => ⟨(hBV hx).1.1,(hBV hx).2⟩),hB0,hB,hBi,?_,hBF⟩
  intro x hx
  exact (hagree _ (hBV hx).1.2.2).trans (hBS x hx)

end PoincareConjecture.M76
