import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcSides
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.PlanarJordanSimpleConnectivity



set_option autoImplicit false
open Set Bornology Metric
namespace PoincareConjecture.M76

theorem exists_jordan_side_avoiding_common_rim_disk
    {gamma delta : C(sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
      EuclideanSpace ℝ (Fin 2))}
    (hgamma : Function.Injective gamma) (hdelta : Function.Injective delta)
    {T W C0 C1 : Set (EuclideanSpace ℝ (Fin 2))}
    (hTc : IsPreconnected T)
    (hTgamma : Disjoint T (range gamma)) (hTdelta : Disjoint T (range delta))
    (hg : range gamma = W ∪ C0) (hd : range delta = W ∪ C1)
    (hC0 : C0 ⊆ closure T) (hC1 : C1 ⊆ closure T)
    (hdiff : range gamma ≠ range delta) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)),
      IsOpen U ∧ IsConnected U ∧ IsCompact (closure U) ∧
      IsSimplyConnected U ∧ interior (closure U) = U ∧
      (frontier U = range gamma ∨ frontier U = range delta) ∧
      Disjoint (closure U) T := by
  obtain ⟨U,U',hU,hU',hcU,hcU',hbU,hbU',hdisU,hcoverU,hfU,hfU',hKU⟩ :=
    Poincare.Topology.Plane.Jordan.exists_complementary_domains gamma.continuous hgamma
  obtain ⟨V,V',hV,hV',hcV,hcV',hbV,hbV',hdisV,hcoverV,hfV,hfV',hKV⟩ :=
    Poincare.Topology.Plane.Jordan.exists_complementary_domains delta.continuous hdelta
  have hclU : closure U = U'ᶜ :=
    closure_eq_compl_of_complementary_regions hcoverU.symm hdisU hfU
  have hclU' : closure U' = Uᶜ :=
    closure_eq_compl_of_complementary_regions
      (hcoverU.symm.trans (union_comm _ _)) hdisU.symm hfU'
  have hclV : closure V = V'ᶜ :=
    closure_eq_compl_of_complementary_regions hcoverV.symm hdisV hfV
  have hclV' : closure V' = Vᶜ :=
    closure_eq_compl_of_complementary_regions
      (hcoverV.symm.trans (union_comm _ _)) hdisV.symm hfV'
  have hrU : interior (closure U) = U := by rw [hclU,interior_compl,hclU',compl_compl]
  have hrV : interior (closure V) = V := by rw [hclV,interior_compl,hclV',compl_compl]
  have hoU : (closure U)ᶜ = U' := by rw [hclU,compl_compl]
  have hoV : (closure V)ᶜ = V' := by rw [hclV,compl_compl]
  have hchoice := exists_bounded_side_avoiding_common_rim_disk hU hV hbU hbV hrU hrV
    (hoU.symm ▸ hcU'.isConnected.isPreconnected)
    (hoV.symm ▸ hcV'.isConnected.isPreconnected)
    (hoU.symm ▸ hbU') (hoV.symm ▸ hbV') hTc
    (hfU.symm ▸ hTgamma) (hfV.symm ▸ hTdelta)
    (hfU.trans hg) (hfV.trans hd) hC0 hC1 (by rwa [hfU,hfV])
  rcases hchoice with hh | hh
  · exact ⟨U,hU,hcU.isConnected,hKU,
      isSimplyConnected_bounded_jordan_side hU hcU.isConnected hbU hcU'.isConnected
        hdisU hcoverU hfU',hrU,Or.inl hfU,hh⟩
  · exact ⟨V,hV,hcV.isConnected,hKV,
      isSimplyConnected_bounded_jordan_side hV hcV.isConnected hbV hcV'.isConnected
        hdisV hcoverV hfV',hrV,Or.inr hfV,hh⟩

end PoincareConjecture.M76
