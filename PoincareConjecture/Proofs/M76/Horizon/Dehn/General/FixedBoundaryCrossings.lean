import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.BoundaryOperationCofaces
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryOldGerms
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.VerticalTriangleGerm
import PoincareConjecture.Proofs.M76.Mathlib.HeightPlaneAffineCoordinates
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmptyInteriorFaceDimension

import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.OriginalGeneralPositionData

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex Topology unitInterval
open scoped Topology
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

theorem OriginalGeneralPositionData.exists_boundary_crossed_charts_with_history
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
  let initial := data.initial
  let As := data.A
  let E₀ := data.exceptional
  have hAsKs := data.boundary_subcomplex
  have hAsRim := data.boundary_space
  have hZ₀s := data.relation_space
  have hE₀ := data.exceptional_finite
  have hE₀s := data.exceptional_eq
  let p := step.projection ∘ step.inclusion
  let lower := p ∘ initial.map
  let bad := (fun z : V2 × V2 => lower z.1) '' E₀
  have hbad : bad.Finite := hE₀.image _
  have hrimPair (x y : D) (hxy : x ≠ y) (hx : (x : V2) ∈ Rim)
      (heq : lower x = lower y) : ((x : V2), (y : V2)) ∈ E₀ := by
    obtain ⟨face, hface, hxface⟩ := mem_space_iff.mp (hAsRim.symm.subset hx)
    have hcard : face.card ≤ 2 := by
      have hint : interior As.space = ∅ := by rw [hAsRim, interior_sphere']
      simpa using As.face_card_le_of_interior_space_eq_empty hint hface
    apply hE₀s.symm.subset
    refine ⟨hZ₀s.symm.subset ⟨x.property, y.property, heq, ?_⟩,
      face, hAsKs hface, hcard, Or.inl hxface⟩
    exact fun h => hxy (Subtype.ext h)
  intro a b hab haRim hpair U hU haU ε hε
  let W₀ := U \ (bad \ {lower a})
  have hW₀ : IsOpen W₀ := hU.sdiff (hbad.subset sdiff_subset).isClosed
  have haW₀ : lower a ∈ W₀ := ⟨haU, fun h => h.2 rfl⟩
  obtain ⟨w, c, Q, J, B₀, P, C₀, K₀, K₁, B, K, q, ρ, H, G, new, eta,
    ha, hb, haQ, hQzero, hQW, hQPL, hbranches, hregion, hfront,
    hJ, hJQ, hzeroJ, hρ, _hball, hPr, hPzero, hC₀s, _hK₀s, hK₁s,
    _hKfaces, hKvertices, hzero, hwhole, hG, hGinv, hGzero, _hformula,
    hGout, _hGprotected, hGleft, hGregion, hGPL, hnewmap, hpath,
    holdplane, hnewplane, hB, hK, hKB, hBs, hKs, hKzero, hqB, hqi,
    hqD, hqrim, hcofaces, history, relation⟩ :=
    step.exists_boundary_rim_cofaces_with_history he hF hopen initial a b hab haRim hpair
      hW₀ haW₀ hε
  have hbadQ (y : s.Carrier) (hy : y ∈ Q.source) (hybad : y ∈ bad) :
      y = lower a := by
    by_contra hn
    exact (hQW hy).1.2 ⟨hybad, hn⟩
  have hprotected (v : V3) (hv : v ∈ K₁.vertices) : (c v).2 ≠ 0 := by
    intro hvzero
    have hvK₁ := hK₁s.subset (K₁.vertices_subset_space hv)
    have hvP := hvK₁.1
    have hvJ := (hPr.subset hvP).2
    have hv0 : v ≠ 0 := by
      intro heq
      rcases hvK₁.2 with hC | hfront
      · exact (hC₀s.subset hC).2 (heq.symm ▸ mem_ball_self hρ)
      · exact hfront.2 (heq.symm ▸ hzeroJ)
    let y := Q.symm v
    have hyQ : y ∈ Q.source := Q.map_target (hJQ hvJ)
    have hQy : Q y = v := Q.right_inv (hJQ hvJ)
    obtain ⟨xr, ⟨⟨ur, hur, hru⟩, hxr⟩, hrv⟩ := (hPr.subset hvP).1
    have hyr : p xr = y := by
      have hxQ : p xr ∈ Q.source := by
        have h : w.right xr ∈ Q.source := hxr.2
        rw [congrFun w.right_eq xr] at h
        exact h
      apply Q.injOn hxQ hyQ
      change Q (w.right xr) = v at hrv
      rw [congrFun w.right_eq xr] at hrv
      exact hrv.trans hQy.symm
    have hyplane : y ∈ p '' (initial.map '' D ∩ w.left.source) :=
      (holdplane y hyQ).mpr ⟨by
          have hvh : (c v).1.1 = 0 := (hPzero.subset hvP).2
          rw [hQy]
          exact le_of_eq hvh.symm,
        by rw [hQy]; exact hvzero⟩
    obtain ⟨xl, ⟨⟨ul, hul, hlu⟩, hxl⟩, hly⟩ := hyplane
    have hurD : ur ∈ D := sphere_subset_closedBall hur
    let ar : D := ⟨ur, hurD⟩
    let al : D := ⟨ul, hul⟩
    have hral : ar ≠ al := by
      intro heq
      have he : xr = xl :=
        hru.symm.trans ((congrArg initial.map (congrArg Subtype.val heq)).trans hlu)
      exact w.disjoint.ne_of_mem hxl hxr.1 he.symm
    have hlower : lower ar = y := (congrArg p hru).trans hyr
    have hlower' : lower al = y := (congrArg p hlu).trans hly
    have hybad : y ∈ bad :=
      ⟨((ar : V2), (al : V2)), hrimPair ar al hral hur (hlower.trans hlower'.symm), hlower⟩
    have hycenter : y = lower a := by
      by_contra hn
      exact (hQW hyQ).1.2 ⟨hybad, hn⟩
    exact hv0 (hQy.symm.trans ((congrArg Q hycenter).trans hQzero))
  have hvertices (v : V3) (hv : v ∈ K.vertices) : (c v).2 ≠ 0 := by
    obtain ⟨u, hu, rfl⟩ := hKvertices.subset hv
    intro hz
    obtain ⟨hu₁, hu0⟩ := (hzero u hu).mp hz
    exact hprotected u hu₁ hu0
  have hqK : K.AffineOnFaces q := fun face hface => hqB face (hKB hface)
  have hqKi : InjOn q K.space := hqi.mono (space_subset_of_le hKB)
  have hqKRim : q '' K.space ⊆ Rim := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hqrim x (space_subset_of_le hKB hx)).mp hx
  have hKcard (face : Finset V3) (hface : face ∈ K.faces) : face.card ≤ 2 := by
    have hint : interior (q '' K.space) = ∅ := by
      apply Set.subset_empty_iff.mp
      simpa only [interior_sphere'] using interior_mono hqKRim
    simpa using hqK.face_card_le_of_injOn_of_empty_interior hqKi hint hface
  let height : V3 →L[ℝ] ℝ := (ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap)
  let ell : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
  have hBpositive (z : V3) (hz : z ∈ B.space) : 0 ≤ height z := by
    obtain ⟨⟨u, ⟨⟨x, hx, hxu⟩, huT⟩, huz⟩, _⟩ := hBs.subset hz
    have huQ : p u ∈ Q.source := by
      have h : w.right u ∈ Q.source := huT.2
      rw [congrFun w.right_eq u] at h
      exact h
    have huR : p u ∈ s.projection ⁻¹' R := by
      change s.projection (step.projection (step.inclusion u)) ∈ R
      rw [← step.original_eq]
      exact hxu ▸ new.inside hx
    have hh := (hregion (p u) huQ).mp huR
    change Q (w.right u) = z at huz
    rw [congrFun w.right_eq u] at huz
    exact huz ▸ hh
  refine ⟨w, c, Q, J, C₀, B, K, q, H, G, new, eta, ha, hb, haQ, hQzero,
    (fun _ hy => ⟨(hQW hy).1.1, (hQW hy).2⟩), hJ, hJQ, hQPL, hbranches,
    hwhole, hG, hGinv, hGzero, _hformula, hGout, _hGprotected,
    hGleft, hGregion, hGPL, hnewmap, hpath,
    hB, hK, hKB, hBs, hKs, hKzero, hqB, hqi, hqD, hqrim, hvertices, ?_, history, hregion, holdplane, hnewplane, hbadQ, relation⟩
  intro z hzK hzJ hz0 W hW hzW
  have hzh : height z = 0 := (hKzero.subset hzK).2
  have hze : ell z = 0 := hz0
  obtain ⟨edge, hedge, hzeint⟩ := K.exists_face_intrinsicInterior_of_finite hK hzK
  have he2 : edge.card = 2 := by
    have hlo := Finset.card_pos.mpr (K.nonempty_of_mem_faces hedge)
    have hhi := hKcard edge hedge
    by_contra hn
    have hone : edge.card = 1 := by omega
    obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hone
    have hzv : z = v := by
      simpa only [Finset.coe_singleton, convexHull_singleton, mem_singleton_iff] using
        intrinsicInterior_subset hzeint
    exact hvertices v hedge (hzv ▸ hz0)
  obtain ⟨face, hface, hef, hf3, _hexhaust, hgerm⟩ :=
    hcofaces edge hedge he2 z hzeint hzJ
  obtain ⟨u, v, _huv, heuv, hu, hv⟩ :
      ∃ u v : V3, u ≠ v ∧ edge = {u, v} ∧ ell u < 0 ∧ 0 < ell v := by
    obtain ⟨u, v, huv, heuv⟩ := Finset.card_eq_two.mp he2
    have huK : u ∈ K.vertices := K.face_subset_vertices hedge
      (heuv.symm ▸ Finset.mem_insert_self _ _)
    have hvK : v ∈ K.vertices := K.face_subset_vertices hedge
      (heuv.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    obtain ⟨wt, hwt, _, hval⟩ :=
      (K.indep hedge).exists_positive_weights_of_mem_intrinsicInterior hzeint
    have hwu := hwt u (heuv.symm ▸ Finset.mem_insert_self _ _)
    have hwv := hwt v (heuv.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have hbalance : wt u * ell u + wt v * ell v = 0 := by
      simpa only [heuv, Finset.sum_pair huv, map_add, map_smul, smul_eq_mul, hze]
        using congrArg ell hval
    rcases lt_or_gt_of_ne (show ell u ≠ 0 from hvertices u huK) with hu | hu
    · have hv : 0 < ell v := by
        by_contra hn
        have h₁ := mul_neg_of_pos_of_neg hwu hu
        have h₂ := mul_nonpos_of_nonneg_of_nonpos hwv.le (not_lt.mp hn)
        linarith
      exact ⟨u, v, huv, heuv, hu, hv⟩
    · have hv : ell v < 0 := by
        by_contra hn
        have h₁ := mul_pos hwu hu
        have h₂ := mul_nonneg hwv.le (not_lt.mp hn)
        linarith
      exact ⟨v, u, huv.symm, heuv.trans (Finset.pair_comm _ _), hv, hu⟩
  have hue : u ∈ edge := heuv.symm ▸ Finset.mem_insert_self _ _
  have hve : v ∈ edge := heuv.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have huf : u ∈ face := hef hue
  have hvf : v ∈ face := hef hve
  have huh : height u = 0 := (hKzero.subset (K.subset_space hedge hue)).2
  have hvh : height v = 0 := (hKzero.subset (K.subset_space hedge hve)).2
  obtain ⟨w₃, _hw₃e, hw₃face⟩ := Finset.exists_eq_insert_iff.mpr ⟨hef, by omega⟩
  have hw₃f : w₃ ∈ face := hw₃face ▸ Finset.mem_insert_self _ _
  have hw₃h : 0 < height w₃ := by
    have hnonneg := hBpositive w₃ (B.subset_space hface hw₃f)
    apply lt_of_le_of_ne hnonneg
    intro heq
    have hzeroHull : convexHull ℝ (face : Set V3) ⊆ {x | height x = 0} := by
      apply convexHull_min ?_ ((convex_singleton (0 : ℝ)).linear_preimage height.toLinearMap)
      intro x hx
      rw [← hw₃face, heuv] at hx
      change x ∈ (insert w₃ ({u, v} : Finset V3)) at hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact heq.symm
      · exact huh
      · exact hvh
    have hne : (convexHull ℝ (face : Set V3)).Nonempty :=
      convexHull_nonempty_iff.mpr (B.nonempty_of_mem_faces hface).to_set
    obtain ⟨x, hx⟩ := hne.intrinsicInterior (convex_convexHull ℝ _)
    have hxK : x ∈ K.space := hKzero.symm.subset
      ⟨B.convexHull_subset_space hface (intrinsicInterior_subset hx),
        hzeroHull (intrinsicInterior_subset hx)⟩
    obtain ⟨other, hother, hxother⟩ := mem_space_iff.mp hxK
    have hsub := B.subset_of_mem_intrinsicInterior_face hface (hKB hother) hx hxother
    have hlo := Finset.card_le_card hsub
    have hhi := hKcard other hother
    omega
  let plane := affineSpan ℝ (face : Set V3)
  have hzplane : z ∈ plane := convexHull_subset_affineSpan (s := (face : Set V3))
    (convexHull_mono hef (intrinsicInterior_subset hzeint))
  have huplane : u ∈ plane := subset_affineSpan ℝ _ huf
  have hvplane : v ∈ plane := subset_affineSpan ℝ _ hvf
  have hwplane : w₃ ∈ plane := subset_affineSpan ℝ _ hw₃f
  have hdim : Module.finrank ℝ plane.direction = 2 :=
    B.finrank_faceDirection_of_card hface hf3
  obtain ⟨F, hFzero, hFell', hFplane⟩ := plane.exists_centered_height_plane_coordinates
    (by simp) hdim ell.toLinearMap.toAffineMap
    ⟨u, huplane, z, hzplane, by change ell u ≠ ell z; rw [hze]; exact hu.ne⟩ hzplane
  have hFell (x : C3) : ell (F x) = x.1.1 := by
    have h := hFell' x
    change ell (F x) = ell z + x.1.1 at h
    simpa only [hze, zero_add] using h
  let ellH : C3 →ₗ[ℝ] ℝ := height.toLinearMap.comp F.toAffineEquiv.linear.toLinearMap
  have hHvalue (x : C3) : ellH x = height (F x) := by
    have hlin := F.toAffineEquiv.toAffineMap.linearMap_vsub x 0
    change F.toAffineEquiv.linear (x - 0) = F x - F 0 at hlin
    rw [sub_zero, hFzero] at hlin
    change height (F.toAffineEquiv.linear x) = height (F x)
    rw [hlin, map_sub, hzh, sub_zero]
  let α := ellH ((1, 0), 0)
  let β := ellH ((0, 1), 0)
  let γ := ellH ((0, 0), 1)
  have hlinear (x : C3) : ellH x = α * x.1.1 + β * x.1.2 + γ * x.2 := by
    have hx : x = x.1.1 • (((1, 0), 0) : C3) +
        x.1.2 • (((0, 1), 0) : C3) + x.2 • (((0, 0), 1) : C3) := by
      ext <;> simp
    conv_lhs => rw [hx]
    rw [map_add, map_add, map_smul, map_smul, map_smul]
    change x.1.1 * α + x.1.2 * β + x.2 * γ = _
    ring
  have hFuplane : (F.symm u).2 = 0 := (hFplane _).mp (by simpa using huplane)
  have hFwplane : (F.symm w₃).2 = 0 := (hFplane _).mp (by simpa using hwplane)
  have hFuell : (F.symm u).1.1 = ell u := by simpa using (hFell (F.symm u)).symm
  have hβ : β ≠ 0 := by
    intro hb₀
    have hu₀ : ellH (F.symm u) = 0 := by rw [hHvalue, F.apply_symm_apply, huh]
    have hαu : α * ell u = 0 := by
      simpa only [hlinear, hb₀, hFuplane, hFuell, zero_mul, mul_zero, add_zero] using hu₀
    have hα : α = 0 := (mul_eq_zero.mp hαu).resolve_right hu.ne
    have hw₀ : height w₃ = 0 := calc
      height w₃ = ellH (F.symm w₃) := by
        rw [hHvalue, F.apply_symm_apply]
      _ = 0 := by rw [hlinear, hα, hb₀, hFwplane]; ring
    exact hw₃h.ne' hw₀
  let X := (LinearMap.fst ℝ ℝ ℝ).comp (LinearMap.fst ℝ (ℝ × ℝ) ℝ)
  let Z := LinearMap.snd ℝ (ℝ × ℝ) ℝ
  let L := (Z.prod ellH).prod X
  let eL : C3 ≃ₗ[ℝ] C3 :=
    { L with
      invFun := fun x => ((x.2, (x.1.2 - α * x.2 - γ * x.1.1) / β), x.1.1)
      left_inv := by
        intro x
        change ((x.1.1, (ellH x - α * x.1.1 - γ * x.2) / β), x.2) = x
        rw [hlinear]
        ext <;> dsimp
        field_simp [hβ]
        ring
      right_inv := by
        intro x
        change ((x.1.1, ellH ((x.2,
          (x.1.2 - α * x.2 - γ * x.1.1) / β), x.1.1)), x.2) = x
        rw [hlinear]
        ext <;> dsimp
        field_simp [hβ]
        ring }
  let A := F.symm.trans eL.toAffineEquiv.toContinuousAffineEquiv
  have hAzero : A z = 0 := by
    change eL (F.symm z) = 0
    rw [← hFzero, F.symm_apply_apply, map_zero]
  have hAplane (x : V3) : (A x).1.1 = 0 ↔ x ∈ plane := by
    change (F.symm x).2 = 0 ↔ x ∈ plane
    simpa only [F.apply_symm_apply] using (hFplane (F.symm x)).symm
  have hAheight (x : V3) : (A x).1.2 = height x := by
    change ellH (F.symm x) = height x
    rw [hHvalue, F.apply_symm_apply]
  have hAell (x : V3) : (A x).2 = ell x := by
    change (F.symm x).1.1 = ell x
    simpa only [F.apply_symm_apply] using (hFell (F.symm x)).symm
  have hAu : A u = ((0, 0), ell u) :=
    Prod.ext (Prod.ext ((hAplane u).mpr huplane) ((hAheight u).trans huh)) (hAell u)
  have hAv : A v = ((0, 0), ell v) :=
    Prod.ext (Prod.ext ((hAplane v).mpr hvplane) ((hAheight v).trans hvh)) (hAell v)
  have hAw : A w₃ = ((0, height w₃), ell w₃) :=
    Prod.ext (Prod.ext ((hAplane w₃).mpr hwplane) (hAheight w₃)) (hAell w₃)
  have hAhull : A '' convexHull ℝ (face : Set V3) =
      convexHull ℝ ({((0, 0), ell u), ((0, 0), ell v),
        ((0, height w₃), ell w₃)} : Set C3) := by
    change A.toAffineEquiv.toAffineMap '' convexHull ℝ (face : Set V3) = _
    rw [A.toAffineEquiv.toAffineMap.image_convexHull]
    change convexHull ℝ (A '' (face : Set V3)) = _
    rw [← hw₃face, heuv]
    simp only [Finset.coe_insert, Finset.coe_singleton, image_insert_eq,
      image_singleton, hAu, hAv, hAw]
    congr 1
    ext x
    simp [or_comm, or_assoc]
  have hwout : ((0, height w₃) : ℝ × ℝ) ≠ 0 := by
    intro heq
    exact hw₃h.ne' (congrArg Prod.snd heq)
  obtain ⟨N, hN, hzeroN, htriangle⟩ := exists_open_vertical_triangle_germ hwout hu hv (ell w₃)
  let O := interior J.space ∩ (Q.target ∩ Q.symm ⁻¹' W)
  have hO : IsOpen O := isOpen_interior.inter (Q.symm.isOpen_inter_preimage hW)
  have hzO : z ∈ O := ⟨hzJ, hJQ (interior_subset hzJ), hzW⟩
  obtain ⟨V, hV, hzV, hVO, hBface⟩ := hgerm O hO hzO
  let N₀ := V ∩ A ⁻¹' N
  have hN₀ : IsOpen N₀ := hV.inter (hN.preimage A.continuous)
  have hzN₀ : z ∈ N₀ := ⟨hzV, by change A z ∈ N; rw [hAzero]; exact hzeroN⟩
  have hlocal (x : V3) (hx : x ∈ N₀) :
      x ∈ B.space ↔ 0 ≤ height x ∧ (A x).1.1 = 0 := by
    rw [hBface x hx.1, ← A.injective.mem_set_image, hAhull]
    change A x ∈ convexHull ℝ ({(0, ell u), (0, ell v),
      ((0, height w₃), ell w₃)} : Set C3) ↔ _
    rw [htriangle _ hx.2]
    constructor
    · rintro ⟨u, hu, heq⟩
      have hf := congrArg Prod.fst heq
      have hs := congrArg Prod.snd heq
      refine ⟨?_, ?_⟩
      · rw [← hAheight x, hs]
        exact mul_nonneg hu hw₃h.le
      · simpa using hf
    · rintro ⟨hh, hx0⟩
      refine ⟨height x / height w₃, div_nonneg hh hw₃h.le, ?_⟩
      apply Prod.ext
      · simpa using hx0
      · change (A x).1.2 = height x / height w₃ * height w₃
        rw [hAheight, div_mul_cancel₀ _ hw₃h.ne']
  let perm : C3 ≃ₗ[ℝ] C3 :=
    { toFun := fun x => ((x.2, x.1.1), x.1.2)
      invFun := fun x => ((x.1.2, x.2), x.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let coord := (A.trans perm.toAffineEquiv.toContinuousAffineEquiv).trans
    c.symm.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv
  let T := Q.trans (coord.toHomeomorph.toOpenPartialHomeomorph.restrOpen N₀ hN₀)
  have hzT : Q.symm z ∈ T.source := by
    refine ⟨Q.map_target (hJQ (interior_subset hzJ)), mem_univ _, ?_⟩
    change Q (Q.symm z) ∈ N₀
    rw [Q.right_inv (hJQ (interior_subset hzJ))]
    exact hzN₀
  have hvalue (y : s.Carrier) : c (T y) = ((ell (Q y), (A (Q y)).1.1), height (Q y)) := by
    change c (c.symm (perm (A (Q y)))) = _
    rw [c.apply_symm_apply]
    change (((A (Q y)).2, (A (Q y)).1.1), (A (Q y)).1.2) = _
    rw [hAell, hAheight]
  have hsource (y : s.Carrier) (hy : y ∈ T.source) : y ∈ W ∩ Q.source := by
    have hxO := (hVO hy.2.2.1).1
    have hyW := hxO.2.2
    change Q.symm (Q y) ∈ W at hyW
    rw [Q.left_inv hy.1] at hyW
    exact ⟨hyW, hy.1⟩
  have hTPL (k : s.Index) : (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact ((locallyPiecewiseAffineOn_affine coord.toContinuousAffineMap isOpen_univ).comp
      (hQPL k).1).mono ((s.charts k).symm.trans T).open_source
        (fun x hx => ⟨⟨hx.1, hx.2.1⟩, mem_univ _⟩)
  refine ⟨T, hzT, ?_, hsource, hTPL, ?_, ?_, ?_, ?_, ?_⟩
  · change c.symm (perm (A (Q (Q.symm z)))) = 0
    rw [Q.right_inv (hJQ (interior_subset hzJ)), hAzero, map_zero, map_zero]
  · ext x
    constructor
    · intro hx
      rcases w.whole_preimage.subset ((hQW hx.1).2) with hl | hr
      · exact Or.inl ⟨hl, hx⟩
      · exact Or.inr ⟨hr, hx⟩
    · exact fun hx => hx.elim And.right And.right
  · intro y hy
    rw [hvalue]
    exact hregion y hy.1
  · intro y hy
    rw [hvalue]
    exact hfront y hy.1
  · intro y hy
    rw [hvalue]
    exact hnewplane y hy.1
  · intro y hy
    have hyJ := interior_subset (hVO hy.2.2.1).2
    have hright : y ∈ p '' (new.map '' D ∩ w.right.source) ↔ Q y ∈ B.space := by
      rw [hBs]
      constructor
      · rintro ⟨x, ⟨hxD, hxw⟩, hxy⟩
        refine ⟨⟨x, ⟨hxD, hxw, ?_⟩, ?_⟩, hyJ⟩
        · change w.right x ∈ Q.source
          rw [congrFun w.right_eq x]
          change p x ∈ Q.source
          rw [hxy]
          exact hy.1
        · change Q (w.right x) = Q y
          rw [congrFun w.right_eq x]
          exact congrArg Q hxy
      · rintro ⟨⟨x, ⟨hxD, hxT⟩, hxy⟩, _⟩
        refine ⟨x, ⟨hxD, hxT.1⟩, ?_⟩
        have hxQ : p x ∈ Q.source := by
          have h : w.right x ∈ Q.source := hxT.2
          rw [congrFun w.right_eq x] at h
          exact h
        apply Q.injOn hxQ hy.1
        change Q (w.right x) = Q y at hxy
        rw [congrFun w.right_eq x] at hxy
        exact hxy
    rw [hright, hvalue]
    exact hlocal (Q y) hy.2.2

theorem OriginalGeneralPositionData.exists_boundary_crossed_charts
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
  dsimp only
  intro a b hab haRim hpair U hU haU ε hε
  obtain ⟨w, c, Q, J, C₀, B, K, q, H, G, new, eta, ha, hb, haQ, hQzero,
    hQU, hJ, hJQ, hQPL, hbranches, hwhole, hG, hGinv, hGzero, hformula,
    hGout, hGprotected, hGleft, hGregion, hGPL, hnewmap, hpath,
    hB, hK, hKB, hBs, hKs, hKzero, hqB, hqi, hqD, hqrim, hvertices, hcross,
    _history, _hregion, _holdplane, _hnewplane, _hbad, relation⟩ :=
    OriginalGeneralPositionData.exists_boundary_crossed_charts_with_history step he hF hopen old
      data a b hab haRim hpair U hU haU ε hε
  exact ⟨w, c, Q, J, C₀, B, K, q, H, G, new, eta, ha, hb, haQ, hQzero,
    hQU, hJ, hJQ, hQPL, hbranches, hwhole, hG, hGinv, hGzero, hformula,
    hGout, hGprotected, hGleft, hGregion, hGPL, hnewmap, hpath,
    hB, hK, hKB, hBs, hKs, hKzero, hqB, hqi, hqD, hqrim, hvertices, hcross, relation⟩

end Geometry.OriginalPLTower
