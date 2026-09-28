import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Normalization.BoundaryComponentExcess
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.ConnectedRemainder









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76

theorem exists_nondisk_piece_of_nonzero_boundary_excess
    {E X γ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] [T2Space X] [Finite γ]
    {T F : Set E} {S : Set X} (C : γ → SimplicialComplex ℝ E) (g : E → X)
    (hC : ∀ c, (C c).faces.Finite ∧ IsConnected (C c).space ∧ (C c).space ⊆ T)
    (hdis : Pairwise fun c d => Disjoint (C c).space (C d).space)
    (hcover : (⋃ c, (C c).space) = T ∩ g ⁻¹' S)
    (hg : ContinuousOn g T) (hgi : InjOn g T) (hFT : F ⊆ T)
    (hF : IsClosed (g '' F)) (hne : boundaryComponentExcess S (g '' T) (g '' F) ≠ 0) :
    ∃ c, ¬ IsFinitePLBallPair (ℝ × ℝ) (C c).space ((C c).space ∩ F) ∧
      ((C c).space ∩ F).Nonempty := by
  classical
  by_contra hbad
  have hall (c) (hc : ((C c).space ∩ F).Nonempty) :
      IsFinitePLBallPair (ℝ × ℝ) (C c).space ((C c).space ∩ F) := by
    by_contra hn
    exact hbad ⟨c,hn,hc⟩
  let P := fun c => g '' (C c).space
  have hPclosed (c) : IsClosed (P c) :=
    (((C c).isCompact_space_of_finite (hC c).1).image_of_continuousOn
      (hg.mono (hC c).2.2)).isClosed
  have hPconn (c) : IsConnected (P c) := (hC c).2.1.image g (hg.mono (hC c).2.2)
  have hPdis : Pairwise fun c d => Disjoint (P c) (P d) := by
    intro c d hcd
    apply disjoint_left.mpr
    rintro _ ⟨x,hx,rfl⟩ ⟨y,hy,hyx⟩
    exact disjoint_left.mp (hdis hcd) hx (hgi ((hC d).2.2 hy) ((hC c).2.2 hx) hyx ▸ hy)
  have hPcover : (⋃ c, P c) = S ∩ g '' T := by
    dsimp only [P]
    rw [←image_iUnion,hcover,image_inter_preimage,inter_comm]
  have hfront (c) : IsPreconnected (P c ∩ g '' F) := by
    rw [show P c = g '' (C c).space from rfl,←hgi.image_inter (hC c).2.2 hFT]
    by_cases hc : ((C c).space ∩ F).Nonempty
    · exact (PrismBelt.finitePL_disk_boundary_isConnected (hall c hc)).isPreconnected.image
        g (hg.mono (inter_subset_left.trans (hC c).2.2))
    · simp only [not_nonempty_iff_eq_empty] at hc
      rw [hc,image_empty]
      exact isPreconnected_empty
  exact hne (boundaryComponentExcess_eq_zero_of_preconnected_frontiers P hPclosed hPconn
    hPdis hPcover hF (image_mono hFT) hfront)

end PoincareConjecture.M76
