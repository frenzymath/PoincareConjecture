import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.BranchInnerSupport
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryProtectedEdges
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.InteriorBranchCharts










set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex Topology unitInterval
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}



theorem OriginalGeneralPositionData.exists_interior_crossed_charts_with_closed_support
    {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    {old : StageMarkedDisk t R Fmark base Jgroup}
    (data : OriginalGeneralPositionData step old)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark)) :
    ∀ a b : D, a ≠ b → (a : V2) ∉ Rim →
      step.projection (step.inclusion (data.initial.map a)) =
        step.projection (step.inclusion (data.initial.map b)) →
      ∀ U : Set s.Carrier, IsOpen U →
        step.projection (step.inclusion (data.initial.map a)) ∈ U →
        ∀ ε : ℝ, 0 < ε →
        ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
          (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
          (J K K₀ : SimplicialComplex ℝ V3)
          (H : PLCarrierMotion J.space K₀.space ε)
          (G : I → t.Carrier ≃ₜ t.Carrier)
          (new : StageMarkedDisk t R Fmark base Jgroup) (ρ : ℝ),
          data.initial.map a ∈ w.left.source ∧ data.initial.map b ∈ w.right.source ∧
          step.projection (step.inclusion (data.initial.map a)) ∈ Q.source ∧
          Q (step.projection (step.inclusion (data.initial.map a))) = 0 ∧
          Q.source ⊆ U ∩ interior (s.projection ⁻¹' R) ∧ Q.source ⊆ w.target ∧
          (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
          J.faces.Finite ∧ K.faces.Finite ∧ J.space ⊆ Q.target ∧
          (0 : V3) ∈ interior J.space ∧ 0 < ρ ∧
          closedBall (0 : V3) ρ ⊆ interior J.space ∧
          K.space = (w.right.trans Q) ''
            (data.initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space ∧
          K₀.space = K.space \ ball (0 : V3) ρ ∧
          IsCompact ((w.right.trans Q).symm '' closedBall (0 : V3) ρ) ∧
          (w.right.trans Q).symm '' closedBall (0 : V3) ρ ⊆
            (w.right.trans Q).symm '' interior J.space ∧
          IsCompact ((w.right.trans Q).symm '' closedBall (0 : V3) ρ ∪
            G 1 '' ((w.right.trans Q).symm '' closedBall (0 : V3) ρ)) ∧
          (w.right.trans Q).symm '' closedBall (0 : V3) ρ ∪
            G 1 '' ((w.right.trans Q).symm '' closedBall (0 : V3) ρ) ⊆
              (w.right.trans Q).symm '' interior J.space ∧
          step.projection (step.inclusion (data.initial.map a)) ∈
            (step.projection ∘ step.inclusion) ''
              ((w.right.trans Q).symm '' closedBall (0 : V3) ρ) ∧
          (∀ u, EqOn (G u) id (data.initial.map '' D \
            (w.right.trans Q).symm '' closedBall (0 : V3) ρ)) ∧
          Continuous (fun z : I × t.Carrier ↦ G z.1 z.2) ∧
          Continuous (fun z : I × t.Carrier ↦ (G z.1).symm z.2) ∧
          (∀ x, G 0 x = x) ∧
          (∀ u, EqOn (G u)
            ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
              (w.right.trans Q).source) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' K₀.space)) ∧
          (∀ u, EqOn (G u) id w.left.source) ∧
          (∀ u, EqOn (G u) id (frontier (t.projection ⁻¹' R))) ∧
          (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R) ∧
          (∀ u k l, (t.charts k).symm.trans
            ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
          (∀ x, new.map x = G 1 (data.initial.map x)) ∧ new.rim = data.initial.rim ∧
          HEq new.basepath data.initial.basepath ∧
          (∀ x : Rim, new.map x = data.initial.map x) ∧
          (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩ J.space =
            H.map 1 '' K.space ∧
          (∀ y ∈ Q.source,
            y ∈ (step.projection ∘ step.inclusion) '' (new.map '' D ∩ w.left.source) ↔
              (c (Q y)).2 = 0) ∧
          (∀ z ∈ H.map 1 '' K.space, z ∈ interior J.space → (c z).2 = 0 →
            ∀ W : Set s.Carrier, IsOpen W → Q.symm z ∈ W →
              ∃ T : OpenPartialHomeomorph s.Carrier V3,
                Q.symm z ∈ T.source ∧ T (Q.symm z) = 0 ∧
                T.source ⊆ W ∩ (Q.source ∩ interior (s.projection ⁻¹' R)) ∧
                (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
                (step.projection ∘ step.inclusion) ⁻¹' T.source =
                  (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
                    (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
                (∀ y ∈ T.source,
                  y ∈ (step.projection ∘ step.inclusion) ''
                    (new.map '' D ∩ w.left.source) ↔ (c (T y)).2 = 0) ∧
                ∀ y ∈ T.source,
                  y ∈ (step.projection ∘ step.inclusion) ''
                    (new.map '' D ∩ w.right.source) ↔ (c (T y)).1.1 = 0) ∧
          ∃ (Z : SimplicialComplex ℝ (V2 × V2)) (E : SimplicialComplex ℝ V2)
            (first : Z.space ≃ₜ E.space),
            Z.faces.Finite ∧ E.faces.Finite ∧
            Z.space = {z | z.1 ∈ D ∧ z.2 ∈ D ∧
              step.projection (step.inclusion (new.map z.1)) =
                step.projection (step.inclusion (new.map z.2)) ∧ z.1 ≠ z.2} ∧
            E.space = {x | x ∈ D ∧ ∃ y ∈ D, x ≠ y ∧
              step.projection (step.inclusion (new.map x)) =
                step.projection (step.inclusion (new.map y))} ∧
            first.IsFinitePL ∧ first.symm.IsFinitePL ∧
            ∀ z : Z.space, (first z : V2) = z.val.1 := by
  classical
  intro a b hab haint hpair U hU haU ε hε
  obtain ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQU, hQw, hQPL, _hbranches, hJ, hJQ, hzeroJ,
    hρ, _hball, hclosed, hPs, hP₀s, hK, hKs, _hR₀, _hR₀J, _hKR, hqK, hqi, _hK₀K,
    hK₀s, hparam, _hwhole, _hL, _hLs, _hδ, _hmargin, _holdcharts,
    happroach, hmotions⟩ :=
    data.exists_protected_edge_crossed_charts_with_closed_support he hF hopen
      a b hab haint hpair U hU haU
  obtain ⟨H, hHK, _hsigns, _hzeroVertices, hfaces, _hposition,
    Kamb, Knew, _hKamb, _hKambs, _hKN, _hKnews, _hK₀N, _hqnew, _hqin,
    _hincidence, _hnewlinks, G, new, hG, hGinv, hGzero, hformula,
    hGout, hGprotected, hGleft, hGfront, hGregion, hGPL, hnewmap,
    hrim, hnewpath, hrimpoint, hnewimage, hleft, hvertexcharts, hedgecharts, relation⟩ :=
    hmotions ε hε
  let ell : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
  obtain ⟨A, _hA, hAs, hcases⟩ := exists_protected_motion_interior_contact_cases
    J K K₀ hK hK₀s q hqK hqi hparam ell H hHK
      (fun face hf hz ↦ (hfaces face hf).mp hz)
      (fun z hz hzJ hz0 ↦ (happroach z hz hzJ hz0).1)
  let H₀ : PLCarrierMotion J.space K₀.space ε :=
    { H with fixed_protected := fun u x hx ↦ H.fixed_protected u x (hK₀s.subset hx) }
  have hH₀ (u : I) : H₀.map u = H.map u := rfl
  have hKold : K.space = (w.right.trans Q) ''
      (data.initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space := hKs.trans hPs
  have hcollar : K₀.space = K.space \ ball (0 : V3) ρ := by
    rw [hK₀s, hP₀s, hKs]
  have hJT : J.space ⊆ (w.right.trans Q).target := by
    intro z hz
    exact ⟨hJQ hz, w.right_target.symm ▸ hQw (Q.map_target (hJQ hz))⟩
  have hprotected : ∀ u, EqOn (G u) id ((w.right.trans Q).symm '' K₀.space) := by
    simpa only [hK₀s] using hGprotected
  obtain ⟨hcompact, hunionCompact, hunionSupport, hdiskfix⟩ :=
    branch_disk_change_support_with_endpoint
    (w.right.trans Q) (data.initial.map '' D) J.space K.space K₀.space ρ
    hclosed hJT hKold hcollar H₀ G hformula hGout hprotected
  have hsupport : (w.right.trans Q).symm '' closedBall (0 : V3) ρ ⊆
      (w.right.trans Q).symm '' interior J.space :=
    subset_union_left.trans hunionSupport
  have hbT : data.initial.map b ∈ (w.right.trans Q).source := by
    refine ⟨hb, ?_⟩
    change w.right (data.initial.map b) ∈ Q.source
    rw [congrFun w.right_eq]
    change step.projection (step.inclusion (data.initial.map b)) ∈ Q.source
    exact hpair ▸ haQ
  have hTb : (w.right.trans Q) (data.initial.map b) = 0 := by
    change Q (w.right (data.initial.map b)) = 0
    rw [congrFun w.right_eq]
    change Q (step.projection (step.inclusion (data.initial.map b))) = 0
    rw [← hpair, hQzero]
  have hbSupport : data.initial.map b ∈
      (w.right.trans Q).symm '' closedBall (0 : V3) ρ := by
    refine ⟨0, mem_closedBall_self hρ.le, ?_⟩
    rw [← hTb]
    exact (w.right.trans Q).left_inv hbT
  have hcenter : step.projection (step.inclusion (data.initial.map a)) ∈
      (step.projection ∘ step.inclusion) ''
        ((w.right.trans Q).symm '' closedBall (0 : V3) ρ) :=
    ⟨data.initial.map b, hbSupport, hpair.symm⟩
  refine ⟨w, c, Q, J, K, K₀, H₀, G, new, ρ,
    ha, hb, haQ, hQzero, hQU, hQw, hQPL, hJ, hK, hJQ, hzeroJ,
    hρ, hclosed, hKold, hcollar, hcompact, hsupport,
    hunionCompact, hunionSupport, hcenter, hdiskfix,
    hG, hGinv, hGzero, ?_, hGout, ?_, hGleft, hGfront, hGregion,
    hGPL, hnewmap, hrim, hnewpath, hrimpoint, ?_, hleft, ?_, relation⟩
  · simpa only [hH₀] using hformula
  · simpa only [hK₀s] using hGprotected
  · rw [hH₀, hKs]
    exact hnewimage
  · intro z hz hzJ hz0 W hW hzW
    rw [hH₀] at hz
    rcases hcases z (hAs.symm.subset hz) hzJ hz0 with hv | he | hfree
    · obtain ⟨T, hzT, hTz, hTs, hTPL, hwhole, hTL, hTR⟩ :=
        hvertexcharts z hv hzJ hz0 W hW hzW
      obtain ⟨B, hBs, hBzero, hBPL, hheight, hfirst⟩ :=
        exists_swapped_crossing_chart s.charts c T hTPL
      refine ⟨B, hBs.symm ▸ hzT, hBzero _ hTz, hBs.subset.trans hTs, hBPL, ?_, ?_, ?_⟩
      · rwa [hBs]
      · intro y hy
        rw [hheight]
        exact hTL y (hBs.subset hy)
      · intro y hy
        rw [hfirst]
        exact hTR y (hBs.subset hy)
    · obtain ⟨edge, hedge, he2, hezero, hzedge⟩ := he
      exact hedgecharts edge hedge he2 hezero z hzedge hzJ W hW hzW
    · let O := interior J.space ∩ (Q.target ∩ Q.symm ⁻¹' W)
      have hO : IsOpen O := isOpen_interior.inter (Q.symm.isOpen_inter_preimage hW)
      obtain ⟨T, hzT, hTs, hTz, hTPL, _hTinv, hTK, hheight⟩ :=
        hfree O hO ⟨hzJ, hJQ (interior_subset hzJ), hzW⟩
      apply exists_two_branch_chart_of_carrier_chart s.charts
        (step.projection ∘ step.inclusion) w (new.map '' D) Q c J.space A.space
        (interior (s.projection ⁻¹' R)) W (fun y hy ↦ (hQU hy).2) hQw hQPL hJQ hleft
        ?_ hzJ T hzT hTz hTs hTPL hTK hheight
      rw [hAs, hKs]
      exact hnewimage


theorem OriginalGeneralPositionData.exists_interior_crossed_charts
    {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    {old : StageMarkedDisk t R Fmark base Jgroup}
    (data : OriginalGeneralPositionData step old)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark)) :
    ∀ a b : D, a ≠ b → (a : V2) ∉ Rim →
      step.projection (step.inclusion (data.initial.map a)) =
        step.projection (step.inclusion (data.initial.map b)) →
      ∀ U : Set s.Carrier, IsOpen U →
        step.projection (step.inclusion (data.initial.map a)) ∈ U →
        ∀ ε : ℝ, 0 < ε →
        ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
          (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
          (J K K₀ : SimplicialComplex ℝ V3)
          (H : PLCarrierMotion J.space K₀.space ε)
          (G : I → t.Carrier ≃ₜ t.Carrier)
          (new : StageMarkedDisk t R Fmark base Jgroup),
          data.initial.map a ∈ w.left.source ∧ data.initial.map b ∈ w.right.source ∧
          step.projection (step.inclusion (data.initial.map a)) ∈ Q.source ∧
          Q (step.projection (step.inclusion (data.initial.map a))) = 0 ∧
          Q.source ⊆ U ∩ interior (s.projection ⁻¹' R) ∧ Q.source ⊆ w.target ∧
          (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
          J.faces.Finite ∧ K.faces.Finite ∧ J.space ⊆ Q.target ∧
          (0 : V3) ∈ interior J.space ∧
          Continuous (fun z : I × t.Carrier ↦ G z.1 z.2) ∧
          Continuous (fun z : I × t.Carrier ↦ (G z.1).symm z.2) ∧
          (∀ x, G 0 x = x) ∧
          (∀ u, EqOn (G u)
            ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
              (w.right.trans Q).source) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
          (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' K₀.space)) ∧
          (∀ u, EqOn (G u) id w.left.source) ∧
          (∀ u, EqOn (G u) id (frontier (t.projection ⁻¹' R))) ∧
          (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R) ∧
          (∀ u k l, (t.charts k).symm.trans
            ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
          (∀ x, new.map x = G 1 (data.initial.map x)) ∧ new.rim = data.initial.rim ∧
          HEq new.basepath data.initial.basepath ∧
          (∀ x : Rim, new.map x = data.initial.map x) ∧
          (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩ J.space =
            H.map 1 '' K.space ∧
          (∀ y ∈ Q.source,
            y ∈ (step.projection ∘ step.inclusion) '' (new.map '' D ∩ w.left.source) ↔
              (c (Q y)).2 = 0) ∧
          (∀ z ∈ H.map 1 '' K.space, z ∈ interior J.space → (c z).2 = 0 →
            ∀ W : Set s.Carrier, IsOpen W → Q.symm z ∈ W →
              ∃ T : OpenPartialHomeomorph s.Carrier V3,
                Q.symm z ∈ T.source ∧ T (Q.symm z) = 0 ∧
                T.source ⊆ W ∩ (Q.source ∩ interior (s.projection ⁻¹' R)) ∧
                (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
                (step.projection ∘ step.inclusion) ⁻¹' T.source =
                  (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
                    (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
                (∀ y ∈ T.source,
                  y ∈ (step.projection ∘ step.inclusion) ''
                    (new.map '' D ∩ w.left.source) ↔ (c (T y)).2 = 0) ∧
                ∀ y ∈ T.source,
                  y ∈ (step.projection ∘ step.inclusion) ''
                    (new.map '' D ∩ w.right.source) ↔ (c (T y)).1.1 = 0) ∧
          ∃ (Z : SimplicialComplex ℝ (V2 × V2)) (E : SimplicialComplex ℝ V2)
            (first : Z.space ≃ₜ E.space),
            Z.faces.Finite ∧ E.faces.Finite ∧
            Z.space = {z | z.1 ∈ D ∧ z.2 ∈ D ∧
              step.projection (step.inclusion (new.map z.1)) =
                step.projection (step.inclusion (new.map z.2)) ∧ z.1 ≠ z.2} ∧
            E.space = {x | x ∈ D ∧ ∃ y ∈ D, x ≠ y ∧
              step.projection (step.inclusion (new.map x)) =
                step.projection (step.inclusion (new.map y))} ∧
            first.IsFinitePL ∧ first.symm.IsFinitePL ∧
            ∀ z : Z.space, (first z : V2) = z.val.1 := by
  classical
  intro a b hab haint hpair U hU haU ε hε
  obtain ⟨w, c, Q, J, K, K₀, H, G, new, ρ, h⟩ :=
    data.exists_interior_crossed_charts_with_closed_support he hF hopen
      a b hab haint hpair U hU haU ε hε
  refine ⟨w, c, Q, J, K, K₀, H, G, new, ?_⟩
  rcases h with ⟨ha, hb, haQ, hQzero, hQU, hQw, hQPL, hJ, hK, hJQ, hzeroJ,
    _hρ, _hclosed, _hKold, _hcollar, _hcompact, _hsupport,
    _hunionCompact, _hunionSupport, _hcenter, _hdiskfix, hrest⟩
  exact ⟨ha, hb, haQ, hQzero, hQU, hQw, hQPL, hJ, hK, hJQ, hzeroJ, hrest⟩

end Geometry.OriginalPLTower
