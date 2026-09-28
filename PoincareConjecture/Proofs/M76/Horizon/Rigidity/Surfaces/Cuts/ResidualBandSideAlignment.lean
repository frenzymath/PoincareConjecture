import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.ResidualBandCut
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallConnected









set_option autoImplicit false

open Set Geometry
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies

private theorem preconnected_subset_one_closed_piece
    {X : Type*} [TopologicalSpace X] {S U V : Set X}
    (hS : IsPreconnected S) (hU : IsClosed U) (hV : IsClosed V)
    (hcover : S ⊆ U ∪ V) (havoid : Disjoint S (U ∩ V)) :
    S ⊆ U ∨ S ⊆ V := by
  classical
  by_cases hSU : S ⊆ U
  · exact Or.inl hSU
  · right
    obtain ⟨x, hx, hxU⟩ := Set.not_subset.mp hSU
    have hxV : x ∈ V := (hcover hx).resolve_left hxU
    intro y hy
    by_contra hyV
    have hyU : y ∈ U := (hcover hy).resolve_right hyV
    obtain ⟨z, hzS, hzUV⟩ := (isPreconnected_closed_iff.mp hS) U V hU hV hcover
      ⟨y, hy, hyU⟩ ⟨x, hx, hxV⟩
    exact disjoint_left.mp havoid hzS hzUV



theorem closed_rim_halves_side_alignment
    {X : Type*} [TopologicalSpace X] {U V Pa Pb T W : Set X} {a b : X}
    (hU : IsClosed U) (hV : IsClosed V)
    (hUc : IsPreconnected U) (hVc : IsPreconnected V)
    (hPa : IsClosed Pa) (hPb : IsClosed Pb) (hPaPb : Disjoint Pa Pb)
    (hT : IsPreconnected T) (hW : IsPreconnected W)
    (hcover : U ∪ V = ((Pa ∪ Pb) ∪ T) ∪ W) (hinter : U ∩ V = {a, b})
    (ha : a ∈ Pa) (hb : b ∈ Pb)
    (haT : a ∉ T) (hbT : b ∉ T) (haW : a ∉ W) (hbW : b ∉ W) :
    (T ⊆ U ∧ W ⊆ V) ∨ (T ⊆ V ∧ W ⊆ U) := by
  have hTcover : T ⊆ U ∪ V := by
    rw [hcover]
    exact fun _ hx ↦ Or.inl (Or.inr hx)
  have hWcover : W ⊆ U ∪ V := by
    rw [hcover]
    exact subset_union_right
  have hTavoid : Disjoint T (U ∩ V) := by
    rw [hinter]
    apply disjoint_left.mpr
    rintro x hx (rfl | hxb)
    · exact haT hx
    · exact hbT (hxb ▸ hx)
  have hWavoid : Disjoint W (U ∩ V) := by
    rw [hinter]
    apply disjoint_left.mpr
    rintro x hx (rfl | hxb)
    · exact haW hx
    · exact hbW (hxb ▸ hx)
  have haUV : a ∈ U ∩ V := hinter.symm.subset (by simp)
  have hbUV : b ∈ U ∩ V := hinter.symm.subset (by simp)
  have not_primal_cover (S : Set X) (hc : IsPreconnected S) (haS : a ∈ S)
      (hbS : b ∈ S) : ¬ S ⊆ Pa ∪ Pb := by
    intro hS
    obtain ⟨z, hzS, hzPa, hzPb⟩ := (isPreconnected_closed_iff.mp hc) Pa Pb hPa hPb
      hS ⟨a, haS, ha⟩ ⟨b, hbS, hb⟩
    exact disjoint_left.mp hPaPb hzPa hzPb
  have not_both_U (hTU : T ⊆ U) (hWU : W ⊆ U) : False := by
    apply not_primal_cover V hVc haUV.2 hbUV.2
    intro x hxV
    have hx : x ∈ ((Pa ∪ Pb) ∪ T) ∪ W := hcover.subset (Or.inr hxV)
    rcases hx with (hx | hxT) | hxW
    · exact hx
    · exact (disjoint_left.mp hTavoid hxT ⟨hTU hxT, hxV⟩).elim
    · exact (disjoint_left.mp hWavoid hxW ⟨hWU hxW, hxV⟩).elim
  have not_both_V (hTV : T ⊆ V) (hWV : W ⊆ V) : False := by
    apply not_primal_cover U hUc haUV.1 hbUV.1
    intro x hxU
    have hx : x ∈ ((Pa ∪ Pb) ∪ T) ∪ W := hcover.subset (Or.inl hxU)
    rcases hx with (hx | hxT) | hxW
    · exact hx
    · exact (disjoint_left.mp hTavoid hxT ⟨hxU, hTV hxT⟩).elim
    · exact (disjoint_left.mp hWavoid hxW ⟨hxU, hWV hxW⟩).elim
  rcases preconnected_subset_one_closed_piece hT hU hV hTcover hTavoid with hTU | hTV
  · rcases preconnected_subset_one_closed_piece hW hU hV hWcover hWavoid with hWU | hWV
    · exact (not_both_U hTU hWU).elim
    · exact Or.inl ⟨hTU, hWV⟩
  · rcases preconnected_subset_one_closed_piece hW hU hV hWcover hWavoid with hWU | hWV
    · exact Or.inr ⟨hTV, hWU⟩
    · exact (not_both_V hTV hWV).elim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  [Fintype K.barycentricSubdivision.faces]

theorem residualBand_bridge_cut_side_alignment
    (hbound : ∀ s ∈ K.faces, s.card ≤ 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (hab : a ≠ b) (heq : e.val = {a, b})
    {t u : Finset E} (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (htc : t.card = 3) (huc : u.card = 3) (htu : t ≠ u)
    (het : e.val.map (Function.Embedding.subtype _) ⊆ t)
    (heu : e.val.map (Function.Embedding.subtype _) ⊆ u)
    {U V : Set E}
    (hU : IsFinitePLBallPair ℝ U {primalEdgeMark K e a, primalEdgeMark K e b})
    (hV : IsFinitePLBallPair ℝ V {primalEdgeMark K e a, primalEdgeMark K e b})
    (hUV : U ∪ V = residualBandRim K e)
    (hinter : U ∩ V = {primalEdgeMark K e a, primalEdgeMark K e b}) :
    (residualCofaceContact K e t ⊆ U ∧ residualCofaceContact K e u ⊆ V) ∨
      (residualCofaceContact K e t ⊆ V ∧ residualCofaceContact K e u ⊆ U) := by
  have hva : a ∈ e.val := by simp [heq]
  have hvb : b ∈ e.val := by simp [heq]
  have hPa := primalEdgeContact_exact_interval K hbound hcofaces e a hva ht hu htc huc htu het heu
  have hPb := primalEdgeContact_exact_interval K hbound hcofaces e b hvb ht hu htc huc htu het heu
  have hT := residualCofaceContact_exact_interval K hbound hcofaces e hab heq ht htc het
  have hW := residualCofaceContact_exact_interval K hbound hcofaces e hab heq hu huc heu
  have hedge : (e.val.map (Function.Embedding.subtype _)).card = 2 := by
    rw [Finset.card_map, e.property.2]
  have hinv : {s : Finset E | s ∈ K.faces ∧ s.card = 3 ∧
      e.val.map (Function.Embedding.subtype _) ⊆ s} = {t, u} := by
    symm
    apply Set.eq_of_subset_of_ncard_le
    · rintro s (rfl | hsu)
      · exact ⟨ht, htc, het⟩
      · exact hsu ▸ ⟨hu, huc, heu⟩
    · rw [Set.ncard_pair htu, hcofaces _ e.property.1 hedge]
    · exact Set.toFinite _
  have hm : e.val.map (Function.Embedding.subtype _) = {a.val, b.val} := by
    simp only [heq, Finset.map_insert, Finset.map_singleton, Function.Embedding.coe_subtype]
  rw [hm] at hinv
  have hcover := hUV.trans (residualBandRim_eq_four_contacts K hbound e heq hinv)
  exact closed_rim_halves_side_alignment hU.isCompact.isClosed hV.isCompact.isClosed
    hU.isConnected.isPreconnected hV.isConnected.isPreconnected
    hPa.isCompact.isClosed hPb.isCompact.isClosed
    (primalEdgeContact_disjoint K e e a b (Or.inr hab))
    hT.isConnected.isPreconnected hW.isConnected.isPreconnected hcover hinter
    (primalEdgeMark_mem_contact K e a hva) (primalEdgeMark_mem_contact K e b hvb)
    (primalEdgeMark_not_mem_cofaceContact K hbound e a hva ht htc het)
    (primalEdgeMark_not_mem_cofaceContact K hbound e b hvb ht htc het)
    (primalEdgeMark_not_mem_cofaceContact K hbound e a hva hu huc heu)
    (primalEdgeMark_not_mem_cofaceContact K hbound e b hvb hu huc heu)




theorem exists_residualBand_bridge_cut_aligned
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.faceLink {p}).space)
    (e : Edge K.vertexAbstractComplex.toPreAbstractSimplicialComplex)
    {a b : K.vertices} (hab : a ≠ b) (heq : e.val = {a, b})
    {t u : Finset E} (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (htc : t.card = 3) (huc : u.card = 3) (htu : t ≠ u)
    (het : e.val.map (Function.Embedding.subtype _) ⊆ t)
    (heu : e.val.map (Function.Embedding.subtype _) ⊆ u) :
    ∃ U V d₀ d₁ : Set E,
      IsFinitePLBallPair ℝ U {primalEdgeMark K e a, primalEdgeMark K e b} ∧
      IsFinitePLBallPair ℝ V {primalEdgeMark K e a, primalEdgeMark K e b} ∧
      U ∪ V = residualBandRim K e ∧
      U ∩ V = {primalEdgeMark K e a, primalEdgeMark K e b} ∧
      IsFinitePLBallPair (ℝ × ℝ) d₀ (U ∪ residualBridge K e a b) ∧
      IsFinitePLBallPair (ℝ × ℝ) d₁ (residualBridge K e a b ∪ V) ∧
      d₀ ∪ d₁ = residualBand K e ∧ d₀ ∩ d₁ = residualBridge K e a b ∧
      d₀ ∩ residualBandRim K e = U ∧ d₁ ∩ residualBandRim K e = V ∧
      residualCofaceContact K e t ⊆ U ∧ residualCofaceContact K e u ⊆ V := by
  have hbound : ∀ s ∈ K.faces, s.card ≤ 3 := by
    intro s hs
    obtain ⟨t, ht, hst, htc⟩ := hpure s hs
    exact (Finset.card_le_card hst).trans_eq htc
  obtain ⟨U, V, d₀, d₁, hU, hV, hUV, hUVint, hd₀, hd₁, hwhole, hcommon, hout₀, hout₁⟩ :=
    exists_residualBand_bridge_cut K hpure hcofaces hlinks e hab heq
  rcases residualBand_bridge_cut_side_alignment K hbound hcofaces e hab heq
    ht hu htc huc htu het heu hU hV hUV hUVint with ⟨hTU, hWV⟩ | ⟨hTV, hWU⟩
  · exact ⟨U, V, d₀, d₁, hU, hV, hUV, hUVint, hd₀, hd₁,
      hwhole, hcommon, hout₀, hout₁, hTU, hWV⟩
  · exact ⟨V, U, d₁, d₀, hV, hU, by rw [union_comm]; exact hUV,
      by rw [inter_comm]; exact hUVint,
      by simpa only [union_comm] using hd₁, by simpa only [union_comm] using hd₀,
      by rw [union_comm]; exact hwhole, by rw [inter_comm]; exact hcommon,
      hout₁, hout₀, hTV, hWU⟩

end PoincareConjecture.M76.OriginalTriangleCopies
