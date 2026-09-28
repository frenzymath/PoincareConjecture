import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.CollarCutCarrier
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Collars.TwoSidedCollarFrontier

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem closure_interior_sphere_collar_cut
    {E X : Type*} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace X] [T2Space X]
    {A : Set E} {R : Set X} {c : E × ℝ → X}
    (hA : IsCompact A) (hR : IsCompact R) (hregular : closure (interior R) = R)
    (hc : Topology.IsEmbedding
      (fun z : (A ×ˢ Icc (-1 : ℝ) 1 : Set (E × ℝ)) => c z))
    {ε δ : ℝ} (hε : 0 < ε) (hεδ : ε < δ) (hδ : δ ≤ 1)
    (hinside : MapsTo c (A ×ˢ Icc (-δ) δ) (interior R))
    (hopen : IsOpen (c '' (A ×ˢ Ioo (-ε) ε))) :
    closure (interior (R \ c '' (A ×ˢ Ioo (-ε) ε))) =
      R \ c '' (A ×ˢ Ioo (-ε) ε) := by
  have hεone : ε ≤ 1 := hεδ.le.trans hδ
  have hcont : ContinuousOn c (A ×ˢ Icc (-1 : ℝ) 1) :=
    continuousOn_iff_continuous_domRestrict.mpr hc.continuous
  have hinj : InjOn c (A ×ˢ Icc (-1 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (hc.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hfull {z : E × ℝ} (hz : z ∈ A ×ˢ Icc (-δ) δ) :
      z ∈ A ×ˢ Icc (-1 : ℝ) 1 :=
    ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hthin {z : E × ℝ} (hz : z ∈ A ×ˢ Icc (-ε) ε) :
      z ∈ A ×ˢ Icc (-δ) δ :=
    ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hclosure := hcont.closure_image_collar_strip hA hε hεone
  have hclR : closure (c '' (A ×ˢ Ioo (-ε) ε)) ⊆ interior R := by
    rw [hclosure]
    rintro _ ⟨z, hz, rfl⟩
    exact hinside (hthin hz)
  obtain ⟨hQ, hint, _, hoverlap, _⟩ := compact_collar_cut_geometry hR hopen hclR
  rw [hclosure] at hint hoverlap
  have hclosed : IsClosed (c '' (A ×ˢ Icc (-ε) ε)) := by
    rw [← hclosure]
    exact isClosed_closure
  have hexterior {a b : ℝ} (ha : -δ ≤ a) (hb : b ≤ δ) (hab : a < b)
      (hout : b ≤ -ε ∨ ε ≤ a) :
      c '' (A ×ˢ Icc a b) ⊆ closure (interior (R \ c '' (A ×ˢ Ioo (-ε) ε))) := by
    have hclab : closure (A ×ˢ Ioo a b) = A ×ˢ Icc a b := by
      rw [closure_prod_eq, hA.isClosed.closure_eq, closure_Ioo hab.ne]
    have habδ {z : E × ℝ} (hz : z ∈ A ×ˢ Icc a b) :
        z ∈ A ×ˢ Icc (-δ) δ :=
      ⟨hz.1, ha.trans hz.2.1, hz.2.2.trans hb⟩
    have hcab : ContinuousOn c (closure (A ×ˢ Ioo a b)) := by
      rw [hclab]
      exact hcont.mono fun _ hz => hfull (habδ hz)
    have hsubset : c '' (A ×ˢ Ioo a b) ⊆ interior (R \ c '' (A ×ˢ Ioo (-ε) ε)) := by
      rw [hint]
      rintro _ ⟨z, hz, rfl⟩
      have hzδ := habδ (show z ∈ A ×ˢ Icc a b from ⟨hz.1, hz.2.1.le, hz.2.2.le⟩)
      refine ⟨hinside hzδ, ?_⟩
      rintro ⟨w, hw, hwz⟩
      have ht := congrArg Prod.snd (hinj (hfull (hthin hw)) (hfull hzδ) hwz)
      rcases hout with hout | hout
      · linarith [hw.2.1, hz.2.2]
      · linarith [hw.2.2, hz.2.1]
    have hdense := hcab.image_closure.trans (closure_mono hsubset)
    rwa [hclab] at hdense
  have hends : c '' (A ×ˢ {-ε}) ∪ c '' (A ×ˢ {ε}) ⊆
      closure (interior (R \ c '' (A ×ˢ Ioo (-ε) ε))) := by
    rintro _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    · apply hexterior (a := -δ) (b := -ε) le_rfl (by linarith) (by linarith) (Or.inl le_rfl)
      exact ⟨z, ⟨hz.1, by rw [show z.2 = -ε from hz.2]; constructor <;> linarith⟩, rfl⟩
    · apply hexterior (a := ε) (b := δ) (by linarith) le_rfl hεδ (Or.inr le_rfl)
      exact ⟨z, ⟨hz.1, by rw [show z.2 = ε from hz.2]; constructor <;> linarith⟩, rfl⟩
  apply Subset.antisymm
  · exact closure_minimal interior_subset hQ.isClosed
  · intro x hx
    by_cases hxC : x ∈ c '' (A ×ˢ Icc (-ε) ε)
    · apply hends
      rw [← hc.frontier_image_collar_strip hA hε hεone hopen]
      exact hoverlap.subset ⟨hxC, hx⟩
    · have hxcl : x ∈ closure (interior R) := hregular.symm.subset hx.1
      have heq : (c '' (A ×ˢ Icc (-ε) ε))ᶜ ∩ interior R =
          interior (R \ c '' (A ×ˢ Ioo (-ε) ε)) := by
        rw [hint]
        ext y
        exact and_comm
      rw [← heq]
      exact hclosed.isOpen_compl.inter_closure ⟨hxC, hxcl⟩

end PoincareConjecture.M76
