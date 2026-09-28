import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicOppositePointed
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveChildren
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityPointedZero
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderDeformedSphere
import PoincareConjecture.Proofs.M76.Mathlib.SupportedCappedHeightSigns
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderNonisolatedZeroSigns
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderNonisolatedProfileSigns
import PoincareConjecture.Proofs.M76.Mathlib.SupportedNonisolatedHeightSigns
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderBranchingCollarsSuccessor











set_option autoImplicit false

open Set

namespace Geometry.AlexanderSectionProfile

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]











theorem exists_pointed_decreasing_deformations_with_level_bounds (W : AlexanderSectionProfile E)
    {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab W.carrier W.height q β)
    (Mneg : AlexanderCollarSlab W.carrier (-W.height) q γ)
    {m : ℕ} (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hpair : Pairwise (fun i k => (P i).boundary ℝ ∩ (P k).boundary ℝ ⊆ {q}))
    (hbranch : ¬ Pairwise (fun i k => Disjoint ((P i).boundary ℝ) ((P k).boundary ℝ)))
    (hfull : W.carrier ∩ {x | W.height x = 0} = ⋃ i, (P i).boundary ℝ)
    (hcount : alexanderCurveCount (fun i => (P i).boundary ℝ) = W.charge 0)
    (j : Fin m) (hqP : q ∈ (P j).boundary ℝ) {d s₀ s₁ U : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d ((P j).boundary ℝ))
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ ((P j).boundary ℝ))
    (hs₁ : IsFinitePLBallPair (ℝ × ℝ) s₁ ((P j).boundary ℝ))
    (hunion : s₀ ∪ s₁ = W.carrier) (hinter : s₀ ∩ s₁ = (P j).boundary ℝ)
    (hdplane : d ⊆ {x | W.height x = 0}) (hcap : d ∩ W.carrier = (P j).boundary ℝ)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hsection : W.carrier ∩ {x | W.height x = 0} = (P j).boundary ℝ ∪ N.space)
    (hdN : d ∩ N.space ⊆ {q}) (hU : IsOpen U) (hdU : d ⊆ U)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ s s' : Set E, ((s = s₀ ∧ s' = s₁) ∨ (s = s₁ ∧ s' = s₀)) ∧
      IsFinitePLBallPair (ℝ × ℝ) s ((P j).boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) s' ((P j).boundary ℝ) ∧
      s ∪ s' = W.carrier ∧ s ∩ s' = (P j).boundary ℝ ∧
      ∃ H G : E ≃ₜ E,
        (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H : E → E) L.space) ∧
        (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (G : E → E) L.space) ∧
        FinitePiecewiseAffineOn (H : E → E) (s ∪ d) ∧
        FinitePiecewiseAffineOn (G : E → E) (s' ∪ d) ∧
        IsFinitePLBallPair (ℝ × ℝ) (H '' d) (H '' (P j).boundary ℝ) ∧
        IsFinitePLBallPair (ℝ × ℝ) (G '' d) (G '' (P j).boundary ℝ) ∧
        (∀ x ∈ M.residual, H x = x) ∧ (∀ x ∈ Mneg.residual, G x = x) ∧
        (∀ x, x ∉ U → H x = x ∧ G x = x) ∧
        (∀ x, δ ≤ |W.height x| → H x = x ∧ G x = x) ∧
        (∀ x, W.height x ≤ W.height (H x) ∧ W.height (G x) ≤ W.height x) ∧
        ((H '' (s ∪ d)) ∩ {x | W.height x = 0} =
          (((s ∪ d) ∩ {x | W.height x = 0}) \ d) ∪ (d ∩ {q})) ∧
        ((G '' (s' ∪ d)) ∩ {x | W.height x = 0} =
          (((s' ∪ d) ∩ {x | W.height x = 0}) \ d) ∪ (d ∩ {q})) ∧
        Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) W.height q β) ∧
        Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) (-W.height) q γ) ∧
        Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) W.height q β) ∧
        Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) (-W.height) q γ) ∧
        ((∀ x ∈ W.carrier, W.height x ∈ Ioo (-γ) β → W.height x ≠ 0 →
            x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})) →
          (∀ x ∈ H '' (s ∪ d), W.height x ∈ Ioo (-γ) β → W.height x ≠ 0 →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height x < W.height y})) ∧
          (∀ x ∈ G '' (s' ∪ d), W.height x ∈ Ioo (-γ) β → W.height x ≠ 0 →
            x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height x < W.height y}))) ∧
        (∀ C : Set ℝ, C.Finite →
          (∀ c ∈ Ioo (-γ) β, c ≠ 0 → c ∉ C) →
          (∀ x ∈ W.carrier, W.height x ∉ C →
            x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})) →
          (insert 0 C).Finite ∧
          (∀ x ∈ H '' (s ∪ d), W.height x ∉ insert 0 C →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height x < W.height y})) ∧
          (∀ x ∈ G '' (s' ∪ d), W.height x ∉ insert 0 C →
            x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height x < W.height y}))) ∧
        (∀ c : ℝ, c ≠ 0 →
          (∃ F : (s ∩ {x | W.height x = c} : Set E) ≃ₜ
            ((H '' (s ∪ d)) ∩ {x | W.height x = c} : Set E), F.IsFinitePL) ∧
          (∃ F : (s' ∩ {x | W.height x = c} : Set E) ≃ₜ
            ((G '' (s' ∪ d)) ∩ {x | W.height x = c} : Set E), F.IsFinitePL)) ∧
        (∃ e : (H '' (s ∪ d) : Set E) ≃ₜ frontier (TriangularRoofModel.halfBall 1),
          e.IsFinitePL) ∧
        (∃ e : (G '' (s' ∪ d) : Set E) ≃ₜ frontier (TriangularRoofModel.halfBall 1),
          e.IsFinitePL) ∧
        ∃ L R : AlexanderSectionProfile E,
          L.carrier = H '' (s ∪ d) ∧ R.carrier = G '' (s' ∪ d) ∧
          L.height = W.height ∧ R.height = W.height ∧
          L.complexity + R.complexity < W.complexity ∧
          L.complexity < W.complexity ∧ R.complexity < W.complexity ∧
          (∀ c, L.charge c + R.charge c ≤ W.charge c) ∧
          Function.support L.charge ⊆ Function.support W.charge ∧
          Function.support R.charge ⊆ Function.support W.charge ∧
          L.charge 0 + R.charge 0 < W.charge 0 ∧
          (W.HasNonisolatedHeightSigns →
            (∀ x ∈ W.carrier, W.height x ∈ Ioo (-γ) β → W.height x ≠ 0 →
              x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
                x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})) →
            L.HasNonisolatedHeightSigns ∧ R.HasNonisolatedHeightSigns) ∧
          (W.HasBranchingCollars →
            (∀ c, W.charge c ≠ 0 → c ≠ 0 → δ < |c|) →
            L.HasBranchingCollars ∧ R.HasBranchingCollars) := by
  let ε := min δ (min β γ) / 2
  have hsmall : 0 < min δ (min β γ) := lt_min hδ (lt_min M.width_pos Mneg.width_pos)
  have hε : 0 < ε := half_pos hsmall
  have hεδ : ε ≤ δ := (half_lt_self hsmall).le.trans (min_le_left _ _)
  have hεβ : ε < β :=
    (half_lt_self hsmall).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεγ : ε < γ :=
    (half_lt_self hsmall).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, H, G,
      hglobalH, hglobalG, hPLH, hPLG, hballH, hballG, hfixRH, hfixRG,
      hfix, hslab, hraise, hzeroH, hzeroG, hpositiveH, hnegativeH,
      hpositiveG, hnegativeG, hsigns, hlevels⟩ :=
    M.exists_intrinsic_opposite_pointed_deformations_with_signs Mneg
      (P j) (hP j).2 (hP j).1 hqP hd hs₀ hs₁ hunion hinter hdplane hcap
      N hN hsection hdN hU hdU hε
  obtain ⟨a₀, a₁, hzero₀, hzero₁, hstrict⟩ :=
    Polygon.exists_decreasing_pointed_zero_presentations
      (Z := {x | W.height x = 0}) n P hP q hpair hbranch j hqP
      hs.isCompact.isClosed hs'.isCompact.isClosed hssinter
      (by simpa only [hss] using hcap) (by simpa only [hss] using hfull)
  rw [← hzeroH] at hzero₀
  rw [← hzeroG] at hzero₁
  have hcut : s ∩ s' ⊆ {x | W.height x = 0} :=
    hssinter.subset.trans (hd.1.trans hdplane)
  obtain ⟨L, R, hL, hR, hLA, hRA, hlt, hLzero, hRzero, hpoint, hsupportL, hsupportR⟩ :=
    W.exists_decreasing_children_with_level_bounds hs.isCompact.isClosed hs'.isCompact.isClosed
      hss hcut (fun c hc => Or.inr (hlevels c hc)) hzero₀ hzero₁
      (hstrict.trans_eq hcount)
  have hzeroStrict : L.charge 0 + R.charge 0 < W.charge 0 := by
    rw [hLzero, hRzero]
    exact hstrict.trans_eq hcount
  have hsd : s ∩ d = (P j).boundary ℝ := by
    apply Subset.antisymm
    · exact fun x hx => hcap.subset ⟨hx.2, hss.subset (Or.inl hx.1)⟩
    · exact fun x hx => ⟨hs.1 hx, hd.1 hx⟩
  have hs'd : s' ∩ d = (P j).boundary ℝ := by
    apply Subset.antisymm
    · exact fun x hx => hcap.subset ⟨hx.2, hss.subset (Or.inr hx.1)⟩
    · exact fun x hx => ⟨hs'.1 hx, hd.1 hx⟩
  have hmodelH := hs.exists_sphere_model_of_deformed_disk_union hd hsd H hglobalH
  have hmodelG := hs'.exists_sphere_model_of_deformed_disk_union hd hs'd G hglobalG
  have hbranching (hW : W.HasBranchingCollars)
      (hgap : ∀ c, W.charge c ≠ 0 → c ≠ 0 → δ < |c|) :
      L.HasBranchingCollars ∧ R.HasBranchingCollars := by
    have hscopy := hs
    have hs'copy := hs'
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Ks, hKs, hKss, _⟩, _⟩, _⟩ := hscopy
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Ks', hKs', hKs's, _⟩, _⟩, _⟩ := hs'copy
    have hsectionH : (H '' (s ∪ d)) ∩ {x | W.height x = 0} ⊆
        s ∩ {x | W.height x = 0} := by
      intro x hx
      refine ⟨?_, hx.2⟩
      rcases hzeroH.subset hx with hxold | hxq
      · exact hxold.1.1.resolve_right hxold.2
      · exact (mem_singleton_iff.mp hxq.2).symm ▸ hs.1 hqP
    have hsectionG : (G '' (s' ∪ d)) ∩ {x | W.height x = 0} ⊆
        s' ∩ {x | W.height x = 0} := by
      intro x hx
      refine ⟨?_, hx.2⟩
      rcases hzeroG.subset hx with hxold | hxq
      · exact hxold.1.1.resolve_right hxold.2
      · exact (mem_singleton_iff.mp hxq.2).symm ▸ hs'.1 hqP
    exact ⟨hW.of_supported_capped_cut L H hL hLA hsupportL hs.isCompact.isClosed
      hs'.isCompact.isClosed hss Ks hKs hKss hcut hdplane hδ hgap
      (fun x hx => (hslab x (hεδ.trans hx)).1) n P hP hfull hpair hsectionH
      (fun _ => ⟨hpositiveH, hnegativeH⟩),
      hW.of_supported_capped_cut R G hR hRA hsupportR hs'.isCompact.isClosed
        hs.isCompact.isClosed (by simpa only [union_comm] using hss) Ks' hKs' hKs's
        (by simpa only [inter_comm] using hcut) hdplane hδ hgap
        (fun x hx => (hslab x (hεδ.trans hx)).2) n P hP hfull hpair hsectionG
        (fun _ => ⟨hpositiveG, hnegativeG⟩)⟩
  have hhereditary (hW : W.HasNonisolatedHeightSigns)
      (hsource : ∀ x ∈ W.carrier, W.height x ∈ Ioo (-γ) β → W.height x ≠ 0 →
        x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
          x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})) :
      L.HasNonisolatedHeightSigns ∧ R.HasNonisolatedHeightSigns := by
    obtain ⟨hsignsH, hsignsG⟩ := hsigns hsource
    obtain ⟨MH⟩ := hpositiveH
    obtain ⟨MHneg⟩ := hnegativeH
    obtain ⟨MG⟩ := hpositiveG
    obtain ⟨MGneg⟩ := hnegativeG
    have hH := H.nonisolated_height_signs_of_supported_capped_cut
      (F := ∅) W.height W.height.continuous_of_finiteDimensional
      hs'.isCompact.isClosed hss hcut hdplane hε hεβ hεγ
      (fun x hx => (hslab x hx).1) hW
      (fun x hx hxzero hacc => MH.mem_both_zero_height_closures_of_nonisolated
        MHneg ⟨hx, hxzero⟩ hacc)
      (fun x hx hxA hxzero _ => hsignsH x hx hxA hxzero)
      (fun _ hx => hx.elim)
    have hG := G.nonisolated_height_signs_of_supported_capped_cut
      (F := ∅) W.height W.height.continuous_of_finiteDimensional
      hs.isCompact.isClosed (by simpa only [union_comm] using hss)
      (by simpa only [inter_comm] using hcut) hdplane hε hεβ hεγ
      (fun x hx => (hslab x hx).2) hW
      (fun x hx hxzero hacc => MG.mem_both_zero_height_closures_of_nonisolated
        MGneg ⟨hx, hxzero⟩ hacc)
      (fun x hx hxA hxzero _ => hsignsG x hx hxA hxzero)
      (fun _ hx => hx.elim)
    exact ⟨by simpa only [HasNonisolatedHeightSigns, hL, hLA] using hH,
      by simpa only [HasNonisolatedHeightSigns, hR, hRA] using hG⟩
  refine ⟨s, s', hlabels, hs, hs', hss, hssinter, H, G,
    hglobalH, hglobalG, hPLH, hPLG, hballH, hballG, hfixRH, hfixRG,
    hfix, (fun x hx => hslab x (hεδ.trans hx)), hraise, hzeroH, hzeroG,
    hpositiveH, hnegativeH, hpositiveG, hnegativeG, hsigns, ?_,
    hlevels, hmodelH, hmodelG,
    L, R, hL, hR, hLA, hRA, hlt, by omega, by omega,
    hpoint, hsupportL, hsupportR, hzeroStrict, hhereditary, hbranching⟩
  intro C hC hgap hsource
  obtain ⟨hsignsH, hsignsG⟩ := hsigns
    (fun x hx hxA hxzero => hsource x hx (hgap _ hxA hxzero))
  have hH := H.finite_exceptional_height_signs_of_supported_capped_cut
    (F := ∅) W.height W.height.continuous_of_finiteDimensional hs'.isCompact.isClosed
    hss hcut hdplane hε hεβ hεγ (fun x hx => (hslab x hx).1) hC finite_empty hsource
    (fun x hx hxA hxzero _ => hsignsH x hx hxA hxzero)
  have hG := G.finite_exceptional_height_signs_of_supported_capped_cut
    (F := ∅) W.height W.height.continuous_of_finiteDimensional hs.isCompact.isClosed
    (by simpa only [union_comm] using hss) (by simpa only [inter_comm] using hcut)
    hdplane hε hεβ hεγ (fun x hx => (hslab x hx).2) hC finite_empty hsource
    (fun x hx hxA hxzero _ => hsignsG x hx hxA hxzero)
  simpa only [image_empty, union_empty] using And.intro hH.1 (And.intro hH.2 hG.2)





theorem exists_pointed_decreasing_deformations (W : AlexanderSectionProfile E)
    {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab W.carrier W.height q β)
    (Mneg : AlexanderCollarSlab W.carrier (-W.height) q γ)
    {m : ℕ} (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hpair : Pairwise (fun i k => (P i).boundary ℝ ∩ (P k).boundary ℝ ⊆ {q}))
    (hbranch : ¬ Pairwise (fun i k => Disjoint ((P i).boundary ℝ) ((P k).boundary ℝ)))
    (hfull : W.carrier ∩ {x | W.height x = 0} = ⋃ i, (P i).boundary ℝ)
    (hcount : alexanderCurveCount (fun i => (P i).boundary ℝ) = W.charge 0)
    (j : Fin m) (hqP : q ∈ (P j).boundary ℝ) {d s₀ s₁ U : Set E}
    (hd : IsFinitePLBallPair (ℝ × ℝ) d ((P j).boundary ℝ))
    (hs₀ : IsFinitePLBallPair (ℝ × ℝ) s₀ ((P j).boundary ℝ))
    (hs₁ : IsFinitePLBallPair (ℝ × ℝ) s₁ ((P j).boundary ℝ))
    (hunion : s₀ ∪ s₁ = W.carrier) (hinter : s₀ ∩ s₁ = (P j).boundary ℝ)
    (hdplane : d ⊆ {x | W.height x = 0}) (hcap : d ∩ W.carrier = (P j).boundary ℝ)
    (N : SimplicialComplex ℝ E) (hN : N.faces.Finite)
    (hsection : W.carrier ∩ {x | W.height x = 0} = (P j).boundary ℝ ∪ N.space)
    (hdN : d ∩ N.space ⊆ {q}) (hU : IsOpen U) (hdU : d ⊆ U)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ s s' : Set E, ((s = s₀ ∧ s' = s₁) ∨ (s = s₁ ∧ s' = s₀)) ∧
      IsFinitePLBallPair (ℝ × ℝ) s ((P j).boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) s' ((P j).boundary ℝ) ∧
      s ∪ s' = W.carrier ∧ s ∩ s' = (P j).boundary ℝ ∧
      ∃ H G : E ≃ₜ E,
        (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (H : E → E) L.space) ∧
        (∀ (L : SimplicialComplex ℝ E), L.faces.Finite →
          FinitePiecewiseAffineOn (G : E → E) L.space) ∧
        FinitePiecewiseAffineOn (H : E → E) (s ∪ d) ∧
        FinitePiecewiseAffineOn (G : E → E) (s' ∪ d) ∧
        IsFinitePLBallPair (ℝ × ℝ) (H '' d) (H '' (P j).boundary ℝ) ∧
        IsFinitePLBallPair (ℝ × ℝ) (G '' d) (G '' (P j).boundary ℝ) ∧
        (∀ x ∈ M.residual, H x = x) ∧ (∀ x ∈ Mneg.residual, G x = x) ∧
        (∀ x, x ∉ U → H x = x ∧ G x = x) ∧
        (∀ x, δ ≤ |W.height x| → H x = x ∧ G x = x) ∧
        (∀ x, W.height x ≤ W.height (H x) ∧ W.height (G x) ≤ W.height x) ∧
        ((H '' (s ∪ d)) ∩ {x | W.height x = 0} =
          (((s ∪ d) ∩ {x | W.height x = 0}) \ d) ∪ (d ∩ {q})) ∧
        ((G '' (s' ∪ d)) ∩ {x | W.height x = 0} =
          (((s' ∪ d) ∩ {x | W.height x = 0}) \ d) ∪ (d ∩ {q})) ∧
        Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) W.height q β) ∧
        Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) (-W.height) q γ) ∧
        Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) W.height q β) ∧
        Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) (-W.height) q γ) ∧
        ((∀ x ∈ W.carrier, W.height x ∈ Ioo (-γ) β → W.height x ≠ 0 →
            x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})) →
          (∀ x ∈ H '' (s ∪ d), W.height x ∈ Ioo (-γ) β → W.height x ≠ 0 →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height x < W.height y})) ∧
          (∀ x ∈ G '' (s' ∪ d), W.height x ∈ Ioo (-γ) β → W.height x ≠ 0 →
            x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height x < W.height y}))) ∧
        (∀ C : Set ℝ, C.Finite →
          (∀ c ∈ Ioo (-γ) β, c ≠ 0 → c ∉ C) →
          (∀ x ∈ W.carrier, W.height x ∉ C →
            x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})) →
          (insert 0 C).Finite ∧
          (∀ x ∈ H '' (s ∪ d), W.height x ∉ insert 0 C →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height x < W.height y})) ∧
          (∀ x ∈ G '' (s' ∪ d), W.height x ∉ insert 0 C →
            x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height x < W.height y}))) ∧
        (∀ c : ℝ, c ≠ 0 →
          (∃ F : (s ∩ {x | W.height x = c} : Set E) ≃ₜ
            ((H '' (s ∪ d)) ∩ {x | W.height x = c} : Set E), F.IsFinitePL) ∧
          (∃ F : (s' ∩ {x | W.height x = c} : Set E) ≃ₜ
            ((G '' (s' ∪ d)) ∩ {x | W.height x = c} : Set E), F.IsFinitePL)) ∧
        (∃ e : (H '' (s ∪ d) : Set E) ≃ₜ frontier (TriangularRoofModel.halfBall 1),
          e.IsFinitePL) ∧
        (∃ e : (G '' (s' ∪ d) : Set E) ≃ₜ frontier (TriangularRoofModel.halfBall 1),
          e.IsFinitePL) ∧
        ∃ L R : AlexanderSectionProfile E,
          L.carrier = H '' (s ∪ d) ∧ R.carrier = G '' (s' ∪ d) ∧
          L.height = W.height ∧ R.height = W.height ∧
          L.complexity + R.complexity < W.complexity ∧
          L.complexity < W.complexity ∧ R.complexity < W.complexity := by
  obtain ⟨s, s', hlabels, hs, hs', hss, hssinter, H, G,
      hglobalH, hglobalG, hPLH, hPLG, hballH, hballG, hfixRH, hfixRG,
      hfix, hslab, hraise, hzeroH, hzeroG, hpositiveH, hnegativeH,
      hpositiveG, hnegativeG, hsigns, hglobalSigns, hlevels, hmodelH, hmodelG,
      L, R, hL, hR, hLA, hRA, hlt, hLlt, hRlt, _⟩ :=
    W.exists_pointed_decreasing_deformations_with_level_bounds M Mneg
      n P hP hpair hbranch hfull hcount j hqP hd hs₀ hs₁ hunion hinter
      hdplane hcap N hN hsection hdN hU hdU hδ
  exact ⟨s, s', hlabels, hs, hs', hss, hssinter, H, G,
    hglobalH, hglobalG, hPLH, hPLG, hballH, hballG, hfixRH, hfixRG,
    hfix, hslab, hraise, hzeroH, hzeroG, hpositiveH, hnegativeH,
    hpositiveG, hnegativeG, hsigns, hglobalSigns, hlevels, hmodelH, hmodelG,
    L, R, hL, hR, hLA, hRA, hlt, hLlt, hRlt⟩

end Geometry.AlexanderSectionProfile
