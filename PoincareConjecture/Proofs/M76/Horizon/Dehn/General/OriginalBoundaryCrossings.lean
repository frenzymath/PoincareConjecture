import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.FixedBoundaryCrossings
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.BoundaryInteriorContacts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.BranchInnerSupport









set_option autoImplicit false

open Set Metric Geometry Topology unitInterval
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

set_option maxHeartbeats 1600000 in
theorem OriginalGeneralPositionData.exists_boundary_operation_crossed_charts
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (old : StageMarkedDisk t R Fmark base Jgroup)
    (data : OriginalGeneralPositionData step old) :
    let initial := data.initial
    ∀ a b : D, a ≠ b → (a : V2) ∈ Rim →
        step.projection (step.inclusion (initial.map a)) =
          step.projection (step.inclusion (initial.map b)) →
        ∀ U : Set s.Carrier, IsOpen U →
          step.projection (step.inclusion (initial.map a)) ∈ U →
          ∀ ε : ℝ, 0 < ε →
          ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
            (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
            (J C₀ B K : SimplicialComplex ℝ V3) (q : V3 → V2)
            (H : PLCarrierMotion J.space C₀.space ε)
            (G : I → t.Carrier ≃ₜ t.Carrier)
            (new : StageMarkedDisk t R Fmark base Jgroup)
            (eta : initial.rim.Homotopy new.rim),
            initial.map a ∈ w.left.source ∧ initial.map b ∈ w.right.source ∧
            step.projection (step.inclusion (initial.map a)) ∈ Q.source ∧
            Q (step.projection (step.inclusion (initial.map a))) = 0 ∧
            Q.source ⊆ U ∩ w.target ∧ J.faces.Finite ∧ J.space ⊆ Q.target ∧
            (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
            (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
              (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
            (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
              (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
            Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
            Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
            (∀ x, G 0 x = x) ∧
            (∀ u, EqOn (G u)
              ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
                (w.right.trans Q).source) ∧
            (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
            (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' C₀.space)) ∧
            (∀ u, EqOn (G u) id w.left.source) ∧
            (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R ∧
              (G u) ⁻¹' frontier (t.projection ⁻¹' R) = frontier (t.projection ⁻¹' R) ∧
              (G u) ⁻¹' (t.projection ⁻¹' Fmark) = t.projection ⁻¹' Fmark) ∧
            (∀ u k l, (t.charts k).symm.trans
              ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
            (∀ x, new.map x = G 1 (initial.map x)) ∧
            new.basepath = initial.basepath.trans (eta.evalAt squareRimBase) ∧
            B.faces.Finite ∧ K.faces.Finite ∧ K ≤ B ∧
            B.space = (w.right.trans Q) ''
              (new.map '' D ∩ (w.right.trans Q).source) ∩ J.space ∧
            K.space = (w.right.trans Q) ''
              (new.map '' Rim ∩ (w.right.trans Q).source) ∩ J.space ∧
            K.space = B.space ∩ {z | (c z).1.1 = 0} ∧
            B.AffineOnFaces q ∧ InjOn q B.space ∧ MapsTo q B.space D ∧
            (∀ z ∈ B.space, z ∈ K.space ↔ q z ∈ Rim) ∧
            (∀ v ∈ K.vertices, (c v).2 ≠ 0) ∧
            (∀ z ∈ K.space, z ∈ interior J.space → (c z).2 = 0 →
              ∀ W : Set s.Carrier, IsOpen W → Q.symm z ∈ W →
                ∃ T : OpenPartialHomeomorph s.Carrier V3,
                  Q.symm z ∈ T.source ∧ T (Q.symm z) = 0 ∧ T.source ⊆ W ∩ Q.source ∧
                  (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
                  (step.projection ∘ step.inclusion) ⁻¹' T.source =
                    (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
                      (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
                  (∀ y ∈ T.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ (c (T y)).2) ∧
                  (∀ y ∈ T.source,
                    y ∈ frontier (s.projection ⁻¹' R) ↔ (c (T y)).2 = 0) ∧
                  (∀ y ∈ T.source,
                    y ∈ (step.projection ∘ step.inclusion) ''
                      (new.map '' D ∩ w.left.source) ↔
                        0 ≤ (c (T y)).2 ∧ (c (T y)).1.1 = 0) ∧
                  ∀ y ∈ T.source,
                    y ∈ (step.projection ∘ step.inclusion) ''
                      (new.map '' D ∩ w.right.source) ↔
                        0 ≤ (c (T y)).2 ∧ (c (T y)).1.2 = 0) ∧
            (∀ z ∈ B.space, z ∈ interior J.space → 0 < (c z).1.1 → (c z).2 = 0 →
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
                      (new.map '' D ∩ w.left.source) ↔ (c (T y)).1.1 = 0) ∧
                  ∀ y ∈ T.source,
                    y ∈ (step.projection ∘ step.inclusion) ''
                      (new.map '' D ∩ w.right.source) ↔ (c (T y)).2 = 0) ∧
            (∃ Small : Set t.Carrier,
              IsCompact Small ∧ IsCompact (Small ∪ G 1 '' Small) ∧
              Small ∪ G 1 '' Small ⊆ (w.right.trans Q).symm '' interior J.space ∧
              step.projection (step.inclusion (initial.map a)) ∈
                (step.projection ∘ step.inclusion) '' Small ∧
              ∀ u, EqOn (G u) id (initial.map '' D \ Small)) ∧
            Nonempty (BoundaryMotionHistory initial.map (w.right.trans Q) c J C₀ B q ε H) ∧
            (∀ y ∈ Q.source, y ∈ s.projection ⁻¹' R ↔ 0 ≤ (c (Q y)).1.1) ∧
            (∀ y ∈ Q.source,
              y ∈ (step.projection ∘ step.inclusion) '' (initial.map '' D ∩ w.left.source) ↔
                0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0) ∧
            (∀ y ∈ Q.source,
              y ∈ (step.projection ∘ step.inclusion) '' (new.map '' D ∩ w.left.source) ↔
                0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0) ∧
            (∀ y ∈ Q.source,
              y ∈ (fun z : V2 × V2 ↦
                step.projection (step.inclusion (initial.map z.1))) '' data.exceptional →
              y = step.projection (step.inclusion (initial.map a))) ∧
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
  dsimp only
  intro a b hab haRim hpair U hU haU ε hε
  obtain ⟨w, c, Q, J, C₀, B, K, q, H, G, new, eta, ha, hb, haQ, hQzero,
    hQU, hJ, hJQ, hQPL, hbranches, hwhole, hG, hGinv, hGzero, hformula,
    hGout, hGprotected, hGleft, hGregion, hGPL, hnewmap, hpath,
    hB, hK, hKB, hBs, hKs, hKzero, hqB, hqi, hqD, hqrim, hvertices, hcross,
    ⟨history⟩, hregion, holdplane, hnewplane, hbad, relation⟩ :=
    OriginalGeneralPositionData.exists_boundary_crossed_charts_with_history step he hF hopen old
      data a b hab haRim hpair U hU haU ε hε
  have hJT : J.space ⊆ (w.right.trans Q).target := by
    intro z hz
    refine ⟨hJQ hz, ?_⟩
    exact w.right_target.symm.subset ((hQU (Q.map_target (hJQ hz))).2)
  let Small := (w.right.trans Q).symm '' closedBall (0 : V3) history.radius
  obtain ⟨hSmall, hSmallEnd, hSmallInner, hSmallFix⟩ :=
    branch_disk_change_support_with_endpoint (w.right.trans Q) (data.initial.map '' D)
      J.space history.sheet.space C₀.space history.radius history.closed_support hJT
      history.sheet_space history.protected_space H G hformula hGout hGprotected
  have hcenter : step.projection (step.inclusion (data.initial.map a)) ∈
      (step.projection ∘ step.inclusion) '' Small := by
    have hzeroBall : (0 : V3) ∈ closedBall (0 : V3) history.radius :=
      mem_closedBall_self history.radius_pos.le
    have hzeroT := hJT (interior_subset (history.closed_support hzeroBall))
    refine ⟨(w.right.trans Q).symm 0, ⟨0, hzeroBall, rfl⟩, ?_⟩
    have hzeroQ : (0 : V3) ∈ Q.target := hQzero ▸ Q.map_source haQ
    have hzW : Q.symm 0 ∈ w.right.target := hzeroT.2
    change (step.projection ∘ step.inclusion) (w.right.symm (Q.symm 0)) = _
    rw [← congrFun w.right_eq _, w.right.right_inv hzW, ← hQzero, Q.left_inv haQ]
  refine ⟨w, c, Q, J, C₀, B, K, q, H, G, new, eta, ha, hb, haQ, hQzero,
    hQU, hJ, hJQ, hQPL, hbranches, hwhole, hG, hGinv, hGzero, hformula,
    hGout, hGprotected, hGleft, hGregion, hGPL, hnewmap, hpath,
    hB, hK, hKB, hBs, hKs, hKzero, hqB, hqi, hqD, hqrim, hvertices, hcross,
    ?_, ⟨Small, hSmall, hSmallEnd, hSmallInner, hcenter, hSmallFix⟩,
    ⟨history⟩, hregion, holdplane, hnewplane, hbad, relation⟩
  intro z hzB hzJ hzR hz0 W hW hzW
  let positive : Set V3 := {x | 0 < (c x).1.1}
  have hpositive : IsOpen positive := isOpen_lt continuous_const (by fun_prop)
  let O := (interior J.space ∩ (Q.target ∩ Q.symm ⁻¹' W)) ∩ positive
  have hO : IsOpen O :=
    (isOpen_interior.inter (Q.symm.isOpen_inter_preimage hW)).inter hpositive
  have hzO : z ∈ O := ⟨⟨hzJ, hJQ (interior_subset hzJ), hzW⟩, hzR⟩
  obtain ⟨T, hzT, hTs, hTz, hTPL, hflat, hTK⟩ :=
    data.boundary_interior_contact_chart step a w c Q J C₀ B q ε H history
      hJQ hQPL hQzero holdplane hbad z hzB hzJ hzR hz0 O hO hzO
  have hpositiveRegion : Q.source ∩ Q ⁻¹' positive ⊆ interior (s.projection ⁻¹' R) := by
    apply interior_maximal _ (Q.isOpen_inter_preimage hpositive)
    intro y hy
    exact (hregion y hy.1).mpr (le_of_lt hy.2)
  apply exists_two_branch_chart_of_local_carrier_chart s.charts
    (step.projection ∘ step.inclusion) w (new.map '' D) Q c J.space B.space
    (interior (s.projection ⁻¹' R)) W (fun _ hy => (hQU hy).2) hQPL hJQ hBs.symm
    hzJ T hzT hTz (fun _ hx => (hTs hx).1) hTPL
  · intro y hy hyT
    exact hpositiveRegion ⟨hy, (hTs hyT).2⟩
  · intro y hy hyT
    rw [hnewplane y hy]
    have hp : 0 ≤ (c (Q y)).1.1 := le_of_lt (hTs hyT).2
    simp only [hp, true_and]
    exact hflat (Q y) hyT
  · exact hTK

end Geometry.OriginalPLTower
