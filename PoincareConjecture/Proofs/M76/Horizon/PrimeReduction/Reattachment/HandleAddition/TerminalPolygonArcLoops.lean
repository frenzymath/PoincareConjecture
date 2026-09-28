import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalTwoArcLoop
import PoincareConjecture.Proofs.M76.Mathlib.MarkedPolygonArcs


set_option autoImplicit false
open Set Metric Geometry
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "Q2" => sphere (0 : Fin 2 → ℝ) 1

theorem exists_terminal_polygon_arc_loops
    {X : Type*} [TopologicalSpace X] [T2Space X]
    {U : Set P2} {a b c d : P2} (hU : IsFinitePLBallPair ℝ U {a,b})
    (hab : a ≠ b) {n : ℕ} (P : Polygon P2 (n+3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hc : c ∈ P.boundary ℝ) (hd : d ∈ P.boundary ℝ) (hcd : c ≠ d)
    {f g : P2 → X} (hf : ContinuousOn f U) (hg : ContinuousOn g (P.boundary ℝ))
    (hfi : InjOn f U) (hgi : InjOn g (P.boundary ℝ))
    (h0 : f a = g c) (h1 : f b = g d)
    (hinter : f '' U ∩ g '' P.boundary ℝ = {f a,f b}) :
    ∃ V W : Set P2, IsFinitePLBallPair ℝ V {c,d} ∧ IsFinitePLBallPair ℝ W {c,d} ∧
      V ∪ W = P.boundary ℝ ∧ V ∩ W = {c,d} ∧
      ∃ gamma delta : C(Q2,X), Function.Injective gamma ∧ Function.Injective delta ∧
        range gamma = f '' U ∪ g '' V ∧ range delta = f '' U ∪ g '' W ∧
        range gamma ∩ range delta = f '' U := by
  obtain ⟨V,W,hV,hW,hcover,hVW⟩ := P.exists_arcs_at_marks hP hPi hc hd hcd
  have hVP : V ⊆ P.boundary ℝ := subset_union_left.trans hcover.subset
  have hWP : W ⊆ P.boundary ℝ := subset_union_right.trans hcover.subset
  have hcut {T : Set P2} (hT : IsFinitePLBallPair ℝ T {c,d}) (hTP : T ⊆ P.boundary ℝ) :
      f '' U ∩ g '' T = {f a,f b} := by
    apply Subset.antisymm
    · exact (inter_subset_inter_right _ (image_mono hTP)).trans hinter.subset
    · rintro x (rfl | rfl)
      · exact ⟨mem_image_of_mem f (hU.1 (Or.inl rfl)),⟨c,hT.1 (Or.inl rfl),h0.symm⟩⟩
      · exact ⟨mem_image_of_mem f (hU.1 (Or.inr rfl)),⟨d,hT.1 (Or.inr rfl),h1.symm⟩⟩
  obtain ⟨gamma,hgamma,hrange⟩ := exists_two_original_arc_loop hU hV hab hcd
    hf (hg.mono hVP) hfi (hgi.mono hVP) h0 h1 (hcut hV hVP)
  obtain ⟨delta,hdelta,hdrange⟩ := exists_two_original_arc_loop hU hW hab hcd
    hf (hg.mono hWP) hfi (hgi.mono hWP) h0 h1 (hcut hW hWP)
  refine ⟨V,W,hV,hW,hcover,hVW,gamma,delta,hgamma,hdelta,hrange,hdrange,?_⟩
  rw [hrange,hdrange]
  apply Subset.antisymm
  · rintro x ⟨hx | hx,hx' | hx'⟩
    · exact hx
    · exact hx
    · exact hx'
    · obtain ⟨v,hv,hvx⟩ := hx
      obtain ⟨w,hw,hwx⟩ := hx'
      have hvw := hgi (hVP hv) (hWP hw) (hvx.trans hwx.symm)
      have hend := hVW.subset ⟨hv,hvw ▸ hw⟩
      rcases hend with hv | hv
      · exact ⟨a,hU.1 (Or.inl rfl),h0.trans ((congrArg g hv.symm).trans hvx)⟩
      · exact ⟨b,hU.1 (Or.inr rfl),h1.trans ((congrArg g hv.symm).trans hvx)⟩
  · exact fun x hx => ⟨Or.inl hx,Or.inl hx⟩

end PoincareConjecture.M76
