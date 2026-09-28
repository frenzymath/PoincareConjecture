import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.AnnularContactAlternatives

set_option autoImplicit false
open Set Geometry PLAnnularStrip
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem nested_enclosing_annular_source_partition
    {m n : ℕ} (P : Polygon P2 (m+3)) (Q : Polygon P2 (n+3))
    (hP : P.HasSimplicialEdges) (hPi : Function.Injective P)
    (hQ : Q.HasSimplicialEdges) (hQi : Function.Injective Q)
    (hPd : ∀ z ∈ P.boundary ℝ, -1 < depth 8 z ∧ depth 8 z < 1)
    (hQd : ∀ z ∈ Q.boundary ℝ, -1 < depth 8 z ∧ depth 8 z < 1)
    (hencl : Dehn.annulusSquare 8 1 ⊆ P.inside)
    (hnest : closure P.inside ⊆ Q.inside) :
    let I := Ann ∩ closure P.inside
    let M := closure Q.inside \ P.inside
    let O := Ann \ Q.inside
    IsCompact I ∧ IsCompact M ∧ IsCompact O ∧
      (I ∪ M) ∪ O = Ann ∧ I ∩ M = P.boundary ℝ ∧ M ∩ O = Q.boundary ℝ ∧
      Disjoint I O ∧
      (∀ z ∈ I, -1 < depth 8 z) ∧
      (∀ z ∈ M, -1 < depth 8 z ∧ depth 8 z < 1) ∧
      ∀ z ∈ O, depth 8 z < 1 := by
  intro I M O
  have hPc : IsCompact (closure P.inside) := (P.isFinitePLBallPair_closed_inside hP hPi).isCompact
  have hQc : IsCompact (closure Q.inside) := (Q.isFinitePLBallPair_closed_inside hQ hQi).isCompact
  have hPo := P.isOpen_inside hP hPi
  have hQo := Q.isOpen_inside hQ hQi
  have hPB : closure P.inside \ P.inside = P.boundary ℝ := by
    rw [←P.frontier_inside hP hPi, frontier, hPo.interior_eq]
  have hQB : closure Q.inside \ Q.inside = Q.boundary ℝ := by
    rw [←Q.frontier_inside hQ hQi, frontier, hQo.interior_eq]
  have hcAnn : IsCompact Ann :=
    (isCompact_Icc.prod isCompact_Icc).diff (isOpen_Ioo.prod isOpen_Ioo)
  have hPlo : ∀ z ∈ closure P.inside, -1 < depth 8 z := by
    intro z hz
    exact (_root_.Dehn.mem_interior_annulusSquare_iff 8 (-1) z).mp
      ((Dehn.Annuli.source_polygon_disk_or_enclosing P hP hPi hPd).2.1 hz)
  have hQlo : ∀ z ∈ closure Q.inside, -1 < depth 8 z := by
    intro z hz
    exact (_root_.Dehn.mem_interior_annulusSquare_iff 8 (-1) z).mp
      ((Dehn.Annuli.source_polygon_disk_or_enclosing Q hQ hQi hQd).2.1 hz)
  have hMd : ∀ z ∈ M, -1 < depth 8 z ∧ depth 8 z < 1 := by
    intro z hz
    refine ⟨hQlo z hz.1, lt_of_not_ge ?_⟩
    intro hh
    exact hz.2 (hencl ((_root_.Dehn.mem_annulusSquare_iff 8 1 z).mpr hh))
  have hMA : M ⊆ Ann := fun z hz => mem_squareAnnulus_iff_depth.mpr
    ⟨(hMd z hz).1.le, (hMd z hz).2.le⟩
  have hPA : P.boundary ℝ ⊆ Ann := fun z hz =>
    mem_squareAnnulus_iff_depth.mpr ⟨(hPd z hz).1.le,(hPd z hz).2.le⟩
  have hQA : Q.boundary ℝ ⊆ Ann := fun z hz =>
    mem_squareAnnulus_iff_depth.mpr ⟨(hQd z hz).1.le,(hQd z hz).2.le⟩
  refine ⟨hcAnn.inter_right isClosed_closure, hQc.diff hPo, hcAnn.diff hQo, ?_, ?_, ?_,
    disjoint_left.mpr (fun _ hx hy => hy.2 (hnest hx.2)),
    fun z hz => hPlo z hz.2, hMd, ?_⟩
  · apply Subset.antisymm
    · exact union_subset (union_subset inter_subset_left hMA) sdiff_subset
    · intro z hz
      by_cases hq : z ∈ Q.inside
      · by_cases hp : z ∈ P.inside
        · exact Or.inl (Or.inl ⟨hz,subset_closure hp⟩)
        · exact Or.inl (Or.inr ⟨subset_closure hq,hp⟩)
      · exact Or.inr ⟨hz,hq⟩
  · apply Subset.antisymm
    · exact fun z hz => hPB.subset ⟨hz.1.2,hz.2.2⟩
    · intro z hz
      obtain ⟨hzcl,hznot⟩ := hPB.symm.subset hz
      exact ⟨⟨hPA hz,hzcl⟩,subset_closure (hnest hzcl),hznot⟩
  · apply Subset.antisymm
    · exact fun z hz => hQB.subset ⟨hz.1.1,hz.2.2⟩
    · intro z hz
      obtain ⟨hzcl,hznot⟩ := hQB.symm.subset hz
      exact ⟨⟨hzcl,fun hp => hznot (hnest (subset_closure hp))⟩,hQA hz,hznot⟩
  · intro z hz
    apply lt_of_not_ge
    intro hh
    exact hz.2 (hnest (subset_closure (hencl
      ((_root_.Dehn.mem_annulusSquare_iff 8 1 z).mpr hh))))

end PoincareConjecture.M76
