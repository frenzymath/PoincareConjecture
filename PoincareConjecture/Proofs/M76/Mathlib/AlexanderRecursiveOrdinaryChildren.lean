import PoincareConjecture.Proofs.M76.Mathlib.IntrinsicOppositeOrdinaryGeometry
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveChildren
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderComplexityOrdinaryZero
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











theorem exists_ordinary_decreasing_deformations_with_level_bounds (W : AlexanderSectionProfile E)
    {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab W.carrier W.height q β)
    (Mneg : AlexanderCollarSlab W.carrier (-W.height) q γ)
    (hregular : ∀ c ∈ Ioo (0 : ℝ) β,
      HasDisjointPolygonPresentation (W.carrier ∩ {x | W.height x = c}))
    (hregularNeg : ∀ c ∈ Ioo (0 : ℝ) γ,
      HasDisjointPolygonPresentation (W.carrier ∩ {x | (-W.height) x = c}))
    (hsource : ∀ x ∈ W.carrier, W.height x ∈ Ioo (-γ) β → W.height x ≠ 0 →
      x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
        x ∈ closure (W.carrier ∩ {y | W.height x < W.height y}))
    {m : ℕ} (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hpair : Pairwise (fun i k => (P i).boundary ℝ ∩ (P k).boundary ℝ ⊆ {q}))
    (hbranch : ¬ Pairwise (fun i k => Disjoint ((P i).boundary ℝ) ((P k).boundary ℝ)))
    (hfull : W.carrier ∩ {x | W.height x = 0} = ⋃ i, (P i).boundary ℝ)
    (hcount : alexanderCurveCount (fun i => (P i).boundary ℝ) = W.charge 0)
    (j : Fin m) (hqP : q ∉ (P j).boundary ℝ) {d s₀ s₁ U : Set E}
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
          (((s ∪ d) ∩ {x | W.height x = 0}) \ d)) ∧
        ((G '' (s' ∪ d)) ∩ {x | W.height x = 0} =
          (((s' ∪ d) ∩ {x | W.height x = 0}) \ d)) ∧
        (q ∈ s →
          Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) W.height q β) ∧
          Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) (-W.height) q γ)) ∧
        (q ∈ s' →
          Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) W.height q β) ∧
          Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) (-W.height) q γ)) ∧
        (∃ t : ℝ, t ∈ Ioo 0 β ∧ ∃ p : E, p ∈ d \ (P j).boundary ℝ ∧
          (H '' d) ∩ {x | W.height x = t * (2 / 3)} = {H p} ∧
          (∀ c : ℝ, c < t * (2 / 3) ∨ t < c →
            (H '' d) ∩ {x | W.height x = c} = ∅) ∧
          (∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
            IsFinitePLBallPair (ℝ × ℝ) ((H '' d) ∩ {x | W.height x ≤ t * a})
              ((H '' d) ∩ {x | W.height x = t * a})) ∧
          (∀ c ∈ Ioo (0 : ℝ) t, c ≠ t * (2 / 3) →
            HasDisjointPolygonPresentation ((H '' (s ∪ d)) ∩ {x | W.height x = c})) ∧
          (∀ x ∈ H '' (s ∪ d), W.height x ∈ Ioo (-γ) β →
            W.height x ≠ 0 → x ≠ H p →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height x < W.height y})) ∧
          ∀ C : Set ℝ, C.Finite →
            (∀ x ∈ W.carrier, W.height x ∉ C →
              x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
                x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})) →
            (insert 0 (insert (W.height (H p)) C)).Finite ∧
              ∀ x ∈ H '' (s ∪ d), W.height x ∉ insert 0 (insert (W.height (H p)) C) →
                x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height y < W.height x}) ∧
                  x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height x < W.height y})) ∧
        (∃ u : ℝ, u ∈ Ioo 0 γ ∧ ∃ p : E, p ∈ d \ (P j).boundary ℝ ∧
          (G '' d) ∩ {x | (-W.height) x = u * (2 / 3)} = {G p} ∧
          (∀ c : ℝ, c < u * (2 / 3) ∨ u < c →
            (G '' d) ∩ {x | (-W.height) x = c} = ∅) ∧
          (∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
            IsFinitePLBallPair (ℝ × ℝ) ((G '' d) ∩ {x | (-W.height) x ≤ u * a})
              ((G '' d) ∩ {x | (-W.height) x = u * a})) ∧
          (∀ c ∈ Ioo (0 : ℝ) u, c ≠ u * (2 / 3) →
            HasDisjointPolygonPresentation ((G '' (s' ∪ d)) ∩ {x | (-W.height) x = c})) ∧
          (∀ x ∈ G '' (s' ∪ d), W.height x ∈ Ioo (-γ) β →
            W.height x ≠ 0 → x ≠ G p →
            x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height x < W.height y})) ∧
          ∀ C : Set ℝ, C.Finite →
            (∀ x ∈ W.carrier, W.height x ∉ C →
              x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
                x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})) →
            (insert 0 (insert (W.height (G p)) C)).Finite ∧
              ∀ x ∈ G '' (s' ∪ d), W.height x ∉ insert 0 (insert (W.height (G p)) C) →
                x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height y < W.height x}) ∧
                  x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height x < W.height y})) ∧
        (∀ c : ℝ, c ≠ 0 →
          (HasAlexanderCurvePresentation ((H '' (s ∪ d)) ∩ {x | W.height x = c}) 0 ∧
            HasAlexanderCurvePresentation ((G '' (s' ∪ d)) ∩ {x | W.height x = c}) 0) ∨
          ((∃ F : (s ∩ {x | W.height x = c} : Set E) ≃ₜ
            ((H '' (s ∪ d)) ∩ {x | W.height x = c} : Set E), F.IsFinitePL) ∧
           (∃ F : (s' ∩ {x | W.height x = c} : Set E) ≃ₜ
            ((G '' (s' ∪ d)) ∩ {x | W.height x = c} : Set E), F.IsFinitePL))) ∧
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
          (q ∉ s → L.charge 0 = 0) ∧ (q ∉ s' → R.charge 0 = 0) ∧
          (W.HasNonisolatedHeightSigns →
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
      hfix, hslab, hnegativeH, hpositiveG, hraise, hzeroH, hzeroG, hsuccessorH, hsuccessorG,
      hbirthH, hbirthG, hlevels⟩ :=
    M.exists_intrinsic_opposite_ordinary_deformations_with_signs Mneg
      hregular hregularNeg hsource (P j) (hP j).2 (hP j).1 hqP
      hd hs₀ hs₁ hunion hinter hdplane hcap N hN hsection hdN hU hdU hε
  have hdP (i : Fin m) (hij : i ≠ j) : Disjoint d ((P i).boundary ℝ) := by
    apply disjoint_left.mpr
    intro x hxd hxi
    have hxS : x ∈ W.carrier :=
      (hfull.symm.subset (mem_iUnion.mpr ⟨i, hxi⟩)).1
    have hxb : x ∈ (P j).boundary ℝ := hcap.subset ⟨hxd, hxS⟩
    have hxq : x = q := hpair hij.symm ⟨hxb, hxi⟩
    exact hqP (hxq ▸ hxb)
  obtain ⟨a₀, a₁, hzero₀, hzero₁, hstrict, hvanish₀, hvanish₁⟩ :=
    Polygon.exists_decreasing_ordinary_zero_presentations_with_residue_free_charges
      (Z := {x | W.height x = 0}) n P hP
      (subsingleton_singleton (a := q)) hpair hbranch j
      hs.isCompact.isClosed hs'.isCompact.isClosed hssinter hd.1
      (by simpa only [hss] using hfull) hdP
  rw [← hzeroH] at hzero₀
  rw [← hzeroG] at hzero₁
  have hcut : s ∩ s' ⊆ {x | W.height x = 0} :=
    hssinter.subset.trans (hd.1.trans hdplane)
  obtain ⟨L, R, hL, hR, hLA, hRA, hlt, hLzero, hRzero, hpoint, hsupportL, hsupportR⟩ :=
    W.exists_decreasing_children_with_level_bounds hs.isCompact.isClosed hs'.isCompact.isClosed
      hss hcut hlevels hzero₀ hzero₁ (hstrict.trans_eq hcount)
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
  obtain ⟨t, ht, p, hp, hsingleH, hemptyH, hsubH, hregularH, hsignsH⟩ := hbirthH
  obtain ⟨u, hu, r, hr, hsingleG, hemptyG, hsubG, hregularG, hsignsG⟩ := hbirthG
  have hzeroSubsetH : (H '' (s ∪ d)) ∩ {x | W.height x = 0} ⊆
      (s ∩ {x | W.height x = 0}) \ d := by
    intro x hx
    have h := hzeroH.subset hx
    exact ⟨⟨h.1.1.resolve_right h.2, h.1.2⟩, h.2⟩
  have hzeroSubsetG : (G '' (s' ∪ d)) ∩ {x | (-W.height) x = 0} ⊆
      (s' ∩ {x | (-W.height) x = 0}) \ d := by
    simp only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero]
    intro x hx
    have h := hzeroG.subset hx
    exact ⟨⟨h.1.1.resolve_right h.2, h.1.2⟩, h.2⟩
  have hisolatedH := H.not_mem_closure_punctured_level_of_cap_singleton W.height
    hs.isCompact.isClosed (by simpa only [inter_comm] using hsd.subset) hp hsingleH
  have hisolatedG := G.not_mem_closure_punctured_level_of_cap_singleton (-W.height)
    hs'.isCompact.isClosed (by simpa only [inter_comm] using hs'd.subset) hr hsingleG
  have hbranching (hW : W.HasBranchingCollars)
      (hgap : ∀ c, W.charge c ≠ 0 → c ≠ 0 → δ < |c|) :
      L.HasBranchingCollars ∧ R.HasBranchingCollars := by
    have hscopy := hs
    have hs'copy := hs'
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Ks, hKs, hKss, _⟩, _⟩, _⟩ := hscopy
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨Ks', hKs', hKs's, _⟩, _⟩, _⟩ := hs'copy
    have hsectionG : (G '' (s' ∪ d)) ∩ {x | W.height x = 0} ⊆
        s' ∩ {x | W.height x = 0} := by
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using
        hzeroSubsetG.trans sdiff_subset
    exact ⟨hW.of_supported_capped_cut L H hL hLA hsupportL hs.isCompact.isClosed
      hs'.isCompact.isClosed hss Ks hKs hKss hcut hdplane hδ hgap
      (fun x hx => (hslab x (hεδ.trans hx)).1) n P hP hfull hpair
      (hzeroSubsetH.trans sdiff_subset) hsuccessorH,
      hW.of_supported_capped_cut R G hR hRA hsupportR hs'.isCompact.isClosed
        hs.isCompact.isClosed (by simpa only [union_comm] using hss) Ks' hKs' hKs's
        (by simpa only [inter_comm] using hcut) hdplane hδ hgap
        (fun x hx => (hslab x (hεδ.trans hx)).2) n P hP hfull hpair hsectionG hsuccessorG⟩
  have hhereditary (hW : W.HasNonisolatedHeightSigns) :
      L.HasNonisolatedHeightSigns ∧ R.HasNonisolatedHeightSigns := by
    have hzeroSignsH := H.nonisolated_zero_height_signs_of_raising_deleted_cut W.height
      hs'.isCompact.isClosed hss (hssinter.subset.trans hd.1)
      (fun x => (hraise x).1) hnegativeH hzeroSubsetH hW
    have hsourceNeg : ∀ x ∈ W.carrier,
        x ∈ closure ((W.carrier ∩ {y | (-W.height) y = (-W.height) x}) \ {x}) →
        x ∈ closure (W.carrier ∩ {y | (-W.height) y < (-W.height) x}) ∧
          x ∈ closure (W.carrier ∩ {y | (-W.height) x < (-W.height) y}) := by
      intro x hx hacc
      have hacc' : x ∈ closure ((W.carrier ∩ {y | W.height y = W.height x}) \ {x}) := by
        simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_inj] using hacc
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_neg_iff] using (hW x hx hacc').symm
    have hzeroSignsGNeg := G.nonisolated_zero_height_signs_of_raising_deleted_cut (-W.height)
      hs.isCompact.isClosed (by simpa only [union_comm] using hss)
      (by simpa only [inter_comm] using hssinter.subset.trans hd.1)
      (fun x => by simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_le_neg_iff] using
        (hraise x).2)
      (fun x hx hxA => hpositiveG x hx (by
        simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_lt_zero] using hxA))
      hzeroSubsetG hsourceNeg
    have hzeroSignsG : ∀ x ∈ G '' (s' ∪ d), W.height x = 0 →
        x ∈ closure (((G '' (s' ∪ d)) ∩ {y | W.height y = 0}) \ {x}) →
        x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height y < 0}) ∧
          x ∈ closure ((G '' (s' ∪ d)) ∩ {y | 0 < W.height y}) := by
      intro x hx hxzero hacc
      have hxzero' : (-W.height) x = 0 := by
        simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hxzero
      have hacc' : x ∈ closure (((G '' (s' ∪ d)) ∩ {y | (-W.height) y = 0}) \ {x}) := by
        simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_eq_zero] using hacc
      simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_pos, neg_lt_zero] using
        (hzeroSignsGNeg x hx hxzero' hacc').symm
    have hH := H.nonisolated_height_signs_of_supported_capped_cut
      (F := {H p}) W.height W.height.continuous_of_finiteDimensional
      hs'.isCompact.isClosed hss hcut hdplane hε hεβ hεγ
      (fun x hx => (hslab x hx).1) hW hzeroSignsH hsignsH
      (fun x hx => (mem_singleton_iff.mp hx).symm ▸ hisolatedH)
    have hG := G.nonisolated_height_signs_of_supported_capped_cut
      (F := {G r}) W.height W.height.continuous_of_finiteDimensional
      hs.isCompact.isClosed (by simpa only [union_comm] using hss)
      (by simpa only [inter_comm] using hcut) hdplane hε hεβ hεγ
      (fun x hx => (hslab x hx).2) hW hzeroSignsG hsignsG
      (fun x hx => (mem_singleton_iff.mp hx).symm ▸ (by
        simpa only [AffineMap.coe_neg, Pi.neg_apply, neg_inj] using hisolatedG))
    exact ⟨by simpa only [HasNonisolatedHeightSigns, hL, hLA] using hH,
      by simpa only [HasNonisolatedHeightSigns, hR, hRA] using hG⟩
  refine ⟨s, s', hlabels, hs, hs', hss, hssinter, H, G,
    hglobalH, hglobalG, hPLH, hPLG, hballH, hballG, hfixRH, hfixRG,
    hfix, (fun x hx => hslab x (hεδ.trans hx)), hraise, hzeroH, hzeroG,
    hsuccessorH, hsuccessorG,
    ⟨t, ht, p, hp, hsingleH, hemptyH, hsubH, hregularH, hsignsH, ?_⟩,
    ⟨u, hu, r, hr, hsingleG, hemptyG, hsubG, hregularG, hsignsG, ?_⟩,
    hlevels, hmodelH, hmodelG,
    L, R, hL, hR, hLA, hRA, hlt, by omega, by omega,
    hpoint, hsupportL, hsupportR, hzeroStrict,
    (fun hq => hLzero.trans (hvanish₀ (disjoint_singleton_left.mpr hq))),
    (fun hq => hRzero.trans (hvanish₁ (disjoint_singleton_left.mpr hq))),
    hhereditary, hbranching⟩
  · intro C hC hglobal
    have hH := H.finite_exceptional_height_signs_of_supported_capped_cut
      (F := {H p}) W.height W.height.continuous_of_finiteDimensional
      hs'.isCompact.isClosed hss hcut hdplane hε hεβ hεγ
      (fun x hx => (hslab x hx).1) hC (finite_singleton _) hglobal
      (fun x hx hxA hxzero hxp => hsignsH x hx hxA hxzero hxp)
    simpa only [image_singleton, union_singleton] using hH
  · intro C hC hglobal
    have hG := G.finite_exceptional_height_signs_of_supported_capped_cut
      (F := {G r}) W.height W.height.continuous_of_finiteDimensional
      hs.isCompact.isClosed (by simpa only [union_comm] using hss)
      (by simpa only [inter_comm] using hcut) hdplane hε hεβ hεγ
      (fun x hx => (hslab x hx).2) hC (finite_singleton _) hglobal
      (fun x hx hxA hxzero hxr => hsignsG x hx hxA hxzero hxr)
    simpa only [image_singleton, union_singleton] using hG





theorem exists_ordinary_decreasing_deformations (W : AlexanderSectionProfile E)
    {q : E} {β γ : ℝ}
    (M : AlexanderCollarSlab W.carrier W.height q β)
    (Mneg : AlexanderCollarSlab W.carrier (-W.height) q γ)
    (hregular : ∀ c ∈ Ioo (0 : ℝ) β,
      HasDisjointPolygonPresentation (W.carrier ∩ {x | W.height x = c}))
    (hregularNeg : ∀ c ∈ Ioo (0 : ℝ) γ,
      HasDisjointPolygonPresentation (W.carrier ∩ {x | (-W.height) x = c}))
    (hsource : ∀ x ∈ W.carrier, W.height x ∈ Ioo (-γ) β → W.height x ≠ 0 →
      x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
        x ∈ closure (W.carrier ∩ {y | W.height x < W.height y}))
    {m : ℕ} (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    (hpair : Pairwise (fun i k => (P i).boundary ℝ ∩ (P k).boundary ℝ ⊆ {q}))
    (hbranch : ¬ Pairwise (fun i k => Disjoint ((P i).boundary ℝ) ((P k).boundary ℝ)))
    (hfull : W.carrier ∩ {x | W.height x = 0} = ⋃ i, (P i).boundary ℝ)
    (hcount : alexanderCurveCount (fun i => (P i).boundary ℝ) = W.charge 0)
    (j : Fin m) (hqP : q ∉ (P j).boundary ℝ) {d s₀ s₁ U : Set E}
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
          (((s ∪ d) ∩ {x | W.height x = 0}) \ d)) ∧
        ((G '' (s' ∪ d)) ∩ {x | W.height x = 0} =
          (((s' ∪ d) ∩ {x | W.height x = 0}) \ d)) ∧
        (q ∈ s →
          Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) W.height q β) ∧
          Nonempty (AlexanderCollarSlab (H '' (s ∪ d)) (-W.height) q γ)) ∧
        (q ∈ s' →
          Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) W.height q β) ∧
          Nonempty (AlexanderCollarSlab (G '' (s' ∪ d)) (-W.height) q γ)) ∧
        (∃ t : ℝ, t ∈ Ioo 0 β ∧ ∃ p : E, p ∈ d \ (P j).boundary ℝ ∧
          (H '' d) ∩ {x | W.height x = t * (2 / 3)} = {H p} ∧
          (∀ c : ℝ, c < t * (2 / 3) ∨ t < c →
            (H '' d) ∩ {x | W.height x = c} = ∅) ∧
          (∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
            IsFinitePLBallPair (ℝ × ℝ) ((H '' d) ∩ {x | W.height x ≤ t * a})
              ((H '' d) ∩ {x | W.height x = t * a})) ∧
          (∀ c ∈ Ioo (0 : ℝ) t, c ≠ t * (2 / 3) →
            HasDisjointPolygonPresentation ((H '' (s ∪ d)) ∩ {x | W.height x = c})) ∧
          (∀ x ∈ H '' (s ∪ d), W.height x ∈ Ioo (-γ) β →
            W.height x ≠ 0 → x ≠ H p →
            x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height x < W.height y})) ∧
          ∀ C : Set ℝ, C.Finite →
            (∀ x ∈ W.carrier, W.height x ∉ C →
              x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
                x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})) →
            (insert 0 (insert (W.height (H p)) C)).Finite ∧
              ∀ x ∈ H '' (s ∪ d), W.height x ∉ insert 0 (insert (W.height (H p)) C) →
                x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height y < W.height x}) ∧
                  x ∈ closure ((H '' (s ∪ d)) ∩ {y | W.height x < W.height y})) ∧
        (∃ u : ℝ, u ∈ Ioo 0 γ ∧ ∃ p : E, p ∈ d \ (P j).boundary ℝ ∧
          (G '' d) ∩ {x | (-W.height) x = u * (2 / 3)} = {G p} ∧
          (∀ c : ℝ, c < u * (2 / 3) ∨ u < c →
            (G '' d) ∩ {x | (-W.height) x = c} = ∅) ∧
          (∀ a : ℝ, a ∈ Ioc (2 / 3) 1 →
            IsFinitePLBallPair (ℝ × ℝ) ((G '' d) ∩ {x | (-W.height) x ≤ u * a})
              ((G '' d) ∩ {x | (-W.height) x = u * a})) ∧
          (∀ c ∈ Ioo (0 : ℝ) u, c ≠ u * (2 / 3) →
            HasDisjointPolygonPresentation ((G '' (s' ∪ d)) ∩ {x | (-W.height) x = c})) ∧
          (∀ x ∈ G '' (s' ∪ d), W.height x ∈ Ioo (-γ) β →
            W.height x ≠ 0 → x ≠ G p →
            x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height y < W.height x}) ∧
              x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height x < W.height y})) ∧
          ∀ C : Set ℝ, C.Finite →
            (∀ x ∈ W.carrier, W.height x ∉ C →
              x ∈ closure (W.carrier ∩ {y | W.height y < W.height x}) ∧
                x ∈ closure (W.carrier ∩ {y | W.height x < W.height y})) →
            (insert 0 (insert (W.height (G p)) C)).Finite ∧
              ∀ x ∈ G '' (s' ∪ d), W.height x ∉ insert 0 (insert (W.height (G p)) C) →
                x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height y < W.height x}) ∧
                  x ∈ closure ((G '' (s' ∪ d)) ∩ {y | W.height x < W.height y})) ∧
        (∀ c : ℝ, c ≠ 0 →
          (HasAlexanderCurvePresentation ((H '' (s ∪ d)) ∩ {x | W.height x = c}) 0 ∧
            HasAlexanderCurvePresentation ((G '' (s' ∪ d)) ∩ {x | W.height x = c}) 0) ∨
          ((∃ F : (s ∩ {x | W.height x = c} : Set E) ≃ₜ
            ((H '' (s ∪ d)) ∩ {x | W.height x = c} : Set E), F.IsFinitePL) ∧
           (∃ F : (s' ∩ {x | W.height x = c} : Set E) ≃ₜ
            ((G '' (s' ∪ d)) ∩ {x | W.height x = c} : Set E), F.IsFinitePL))) ∧
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
      hfix, hslab, hraise, hzeroH, hzeroG, hsuccessorH, hsuccessorG,
      hbirthH, hbirthG, hlevels, hmodelH, hmodelG,
      L, R, hL, hR, hLA, hRA, hlt, hLlt, hRlt, _⟩ :=
    W.exists_ordinary_decreasing_deformations_with_level_bounds M Mneg
      hregular hregularNeg hsource n P hP hpair hbranch hfull hcount j hqP
      hd hs₀ hs₁ hunion hinter hdplane hcap N hN hsection hdN hU hdU hδ
  exact ⟨s, s', hlabels, hs, hs', hss, hssinter, H, G,
    hglobalH, hglobalG, hPLH, hPLG, hballH, hballG, hfixRH, hfixRG,
    hfix, hslab, hraise, hzeroH, hzeroG, hsuccessorH, hsuccessorG,
    hbirthH, hbirthG, hlevels, hmodelH, hmodelG,
    L, R, hL, hR, hLA, hRA, hlt, hLlt, hRlt⟩

end Geometry.AlexanderSectionProfile
