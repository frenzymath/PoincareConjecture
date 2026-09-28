import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.OriginalGeneralPositionData
import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.Mathlib.LocalCrossingLink
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryStep

set_option autoImplicit false

open Set Metric Geometry Topology Filter unitInterval
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

theorem OriginalGeneralPositionData.exists_protected_link_sections_with_closed_support
    {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    {old : StageMarkedDisk t R Fmark base Jgroup}
    (data : OriginalGeneralPositionData step old)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (_hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark)) :
  ∀ a b : D, a ≠ b → (a : V2) ∉ Rim →
    step.projection (step.inclusion (data.initial.map a)) =
      step.projection (step.inclusion (data.initial.map b)) →
    ∀ U : Set s.Carrier, IsOpen U →
      step.projection (step.inclusion (data.initial.map a)) ∈ U →
      ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
        (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
        (J P P₀ R₀ K K₀ L : SimplicialComplex ℝ V3)
        (q : V3 → ℝ × ℝ) (ρ δ : ℝ),
        data.initial.map a ∈ w.left.source ∧ data.initial.map b ∈ w.right.source ∧
        step.projection (step.inclusion (data.initial.map a)) ∈ Q.source ∧
        Q (step.projection (step.inclusion (data.initial.map a))) = 0 ∧
        Q.source ⊆ U ∩ interior (s.projection ⁻¹' R) ∧ Q.source ⊆ w.target ∧
        (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
        (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
          (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ Q.source,
          y ∈ (step.projection ∘ step.inclusion) '' (data.initial.map '' D ∩ w.left.source) ↔
            (c (Q y)).2 = 0) ∧
        J.faces.Finite ∧ J.space ⊆ Q.target ∧ (0 : V3) ∈ interior J.space ∧
        0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
        closedBall (0 : V3) ρ ⊆ interior J.space ∧
        P.space = (w.right.trans Q) ''
          (data.initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space ∧
        P₀.space = P.space \ ball (0 : V3) ρ ∧
        R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ K ≤ R₀ ∧ K.space = P.space ∧
        K.AffineOnFaces q ∧ InjOn q K.space ∧ K₀ ≤ K ∧ K₀.space = P₀.space ∧
        (∀ z ∈ P.space, z ∈ interior J.space → q z ∈ interior (q '' P.space)) ∧
        (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
          (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
        (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
          ∃ T : OpenPartialHomeomorph V3 C3,
            (0 : V3) ∈ T.source ∧ T 0 = 0 ∧
            LocallyPiecewiseAffineOn T.symm T.target ∧
            (∀ z ∈ T.source, z ∈ (fun x : V3 => -v + x) '' K.space ↔
              (T z).1.1 = 0) ∧
            ∀ z ∈ T.source, (c z).2 = 0 ↔ (T z).2 = 0) ∧
        (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
          v ∈ closure (K.space ∩ {z | 0 < (c z).2}) ∧
          v ∈ closure (K.space ∩ {z | (c z).2 < 0})) ∧
        (∀ v ∈ K₀.vertices, v ∈ interior J.space → (c v).2 = 0 →
          ((K.link v).space ∩ {z | (c z).2 = 0}).ncard = 2 ∧
          (∃ z ∈ (K.link v).space, 0 < (c z).2) ∧
          ∃ z ∈ (K.link v).space, (c z).2 < 0) ∧
        (∀ v ∈ K.vertices, v ∈ interior J.space →
          ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
            T.HasSimplicialEdges ∧ T.boundary ℝ = (K.link v).space) ∧
        L.faces.Finite ∧ L.space = J.space ∩ {z | (c z).2 = 0} ∧
        0 < δ ∧ (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → δ ≤ |(c v).2|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space P₀.space ε,
          R₀.AffineOnFaces (H.map 1) ∧
          (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → ∀ u,
            (0 < (c (H.map u v)).2 ↔ 0 < (c v).2) ∧
            ((c (H.map u v)).2 < 0 ↔ (c v).2 < 0)) ∧
          (∀ v ∈ K.vertices,
            (c (H.map 1 v)).2 = 0 ↔ v ∈ K₀.vertices ∧ (c v).2 = 0) ∧
          (∀ face ∈ K.faces, (∀ v ∈ face, (c (H.map 1 v)).2 = 0) ↔
            face ∈ K₀.faces ∧ ∀ v ∈ face, (c v).2 = 0) ∧
          (∀ face ∈ K.faces, face ∉ K₀.faces → ∀ other ∈ L.faces,
            affineSpan ℝ (H.map 1 '' (face : Set V3) ∪ (other : Set V3)) = ⊤ ∨
              Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (face : Set V3))))
                (convexHull ℝ (other : Set V3))) ∧
          ∃ Kamb Knew : SimplicialComplex ℝ V3,
            Kamb.faces.Finite ∧ Kamb.space = J.space ∧ Knew ≤ Kamb ∧
            Knew.space = H.map 1 '' P.space ∧ K₀ ≤ Knew ∧
            Knew.AffineOnFaces (q ∘ (H.map 1).symm) ∧
            InjOn (q ∘ (H.map 1).symm) Knew.space ∧
            (∀ v ∈ K.vertices,
              (Knew.link (H.map 1 v)).space = H.map 1 '' (K.link v).space ∧
              (Knew.closedStar (H.map 1 v)).space = H.map 1 '' (K.closedStar v).space) ∧
            (∀ v ∈ K.vertices, v ∈ interior J.space →
              ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
                T.HasSimplicialEdges ∧ T.boundary ℝ = (Knew.link (H.map 1 v)).space) ∧
          ∃ (G : I → t.Carrier ≃ₜ t.Carrier)
            (new : StageMarkedDisk t R Fmark base Jgroup),
            Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
            Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
            (∀ x, G 0 x = x) ∧
            (∀ u, EqOn (G u)
              ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
                (w.right.trans Q).source) ∧
            (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
            (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' P₀.space)) ∧
            (∀ u, EqOn (G u) id w.left.source) ∧
            (∀ u, EqOn (G u) id (frontier (t.projection ⁻¹' R))) ∧
            (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R) ∧
            (∀ u k l, (t.charts k).symm.trans
              ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
            (∀ x, new.map x = G 1 (data.initial.map x)) ∧ new.rim = data.initial.rim ∧
            HEq new.basepath data.initial.basepath ∧
            (∀ x : Rim, new.map x = data.initial.map x) ∧
            (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩ J.space =
              H.map 1 '' P.space ∧
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
  let initial := data.initial
  let E := data.exceptional
  have hE := data.exceptional_finite
  have hcross := data.crossings
  let p := step.projection ∘ step.inclusion
  let lower := p ∘ initial.map
  let bad := (fun z : V2 × V2 => lower z.1) '' E
  have hbad : bad.Finite := hE.image _
  intro a b hab haint hpair U hU haU
  let W := U \ (bad \ {lower a})
  have hW : IsOpen W := hU.sdiff (hbad.subset sdiff_subset).isClosed
  have haW : lower a ∈ W := ⟨haU, fun h => h.2 rfl⟩
  obtain ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, hQW, hQw, hQPL, hbranches, hplane,
    hJ, _hcv, hJQ, hzeroJ, hρ, hball, hclosed, _hP, _hP₀, hPs, hP₀s,
    _hbB, _hzeroP, _hq, hqi, hqint, hR₀, hR₀J, hKR, hKs, hqK,
    hK₀K, hK₀s, hL, hLs, hlinks, hwhole, hδ, hmargin, hmotions⟩ :=
    step.exists_original_protected_branch_operation_with_closed_support
      he hF initial a b hab haint hpair hW haW
  have hK : K.faces.Finite := hR₀.subset hKR
  have old_chart (v : V3) (hvP₀ : v ∈ P₀.space) (hvJ : v ∈ interior J.space)
      (hvzero : (c v).2 = 0) :
      ∃ T : OpenPartialHomeomorph V3 C3,
        (0 : V3) ∈ T.source ∧ T 0 = 0 ∧ LocallyPiecewiseAffineOn T.symm T.target ∧
        (∀ z ∈ T.source, z ∈ (fun x : V3 => -v + x) '' K.space ↔ (T z).1.1 = 0) ∧
        ∀ z ∈ T.source, (c z).2 = 0 ↔ (T z).2 = 0 := by
    have hvP : v ∈ P.space := (hP₀s.subset hvP₀).1
    have hv0 : v ≠ 0 := by
      intro heq
      exact (hP₀s.subset hvP₀).2 (heq.symm ▸ mem_ball_self hρ)
    let y := Q.symm v
    have hyQ : y ∈ Q.source := Q.map_target (hJQ (interior_subset hvJ))
    have hQy : Q y = v := Q.right_inv (hJQ (interior_subset hvJ))
    obtain ⟨xr, ⟨⟨ur, hur, hru⟩, hxr⟩, hrv⟩ := (hPs.subset hvP).1
    have hyr : p xr = y := by
      have hxrQ : w.right xr ∈ Q.source := hxr.2
      rw [congrFun w.right_eq xr] at hxrQ
      apply Q.injOn hxrQ hyQ
      change Q (w.right xr) = v at hrv
      rw [congrFun w.right_eq xr] at hrv
      exact hrv.trans hQy.symm
    have hleft : y ∈ p '' (initial.map '' D ∩ w.left.source) :=
      (hplane y hyQ).mpr (by rw [hQy]; exact hvzero)
    obtain ⟨xl, ⟨⟨ul, hul, hlu⟩, hxl⟩, hly⟩ := hleft
    let al : D := ⟨ul, hul⟩
    let ar : D := ⟨ur, hur⟩
    have hlar : al ≠ ar := by
      intro heq
      have he : xl = xr :=
        hlu.symm.trans ((congrArg initial.map (congrArg Subtype.val heq)).trans hru)
      exact w.disjoint.ne_of_mem hxl hxr.1 he
    have hlower : lower al = y := (congrArg p hlu).trans hly
    have hupper : lower ar = y := (congrArg p hru).trans hyr
    have hnotE : ((al : V2), (ar : V2)) ∉ E := by
      intro hmem
      have hybad : y ∈ bad := ⟨((al : V2), (ar : V2)), hmem, hlower⟩
      have hyW := (hQW hyQ).1
      have hycenter : y = lower a := by
        by_contra hn
        exact hyW.2 ⟨hybad, hn⟩
      exact hv0 (hQy.symm.trans ((congrArg Q hycenter).trans hQzero))
    obtain ⟨a', b', w', c', T, horder, ha', hb', hyT, _hTinside, hTzero,
      hTPL, _hTbranches, _hTwhole, hTleft, hTright⟩ :=
      hcross al ar hlar (hlower.trans hupper.symm) hnotE Q.source Q.open_source
        (by change lower al ∈ Q.source; rw [hlower]; exact hyQ)
    have hyT' : y ∈ T.source := by
      change lower al ∈ T.source at hyT
      exact hlower ▸ hyT
    have hTy : T y = 0 := by
      change T (lower al) = 0 at hTzero
      simpa only [hlower] using hTzero
    obtain ⟨left, right, coord, hleftpoint, hrightpoint, hleq, hreq,
      hleftplane, hrightplane⟩ :
        ∃ (left right : OpenPartialHomeomorph t.Carrier s.Carrier)
          (coord : V3 ≃L[ℝ] C3),
          xl ∈ left.source ∧ xr ∈ right.source ∧
          (left : t.Carrier → s.Carrier) = p ∧
          (right : t.Carrier → s.Carrier) = p ∧
          (∀ x ∈ T.source, x ∈ p '' (initial.map '' D ∩ left.source) ↔
            (coord (T x)).2 = 0) ∧
          ∀ x ∈ T.source, x ∈ p '' (initial.map '' D ∩ right.source) ↔
            (coord (T x)).1.1 = 0 := by
      rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨w'.left, w'.right, c', hlu ▸ ha', hru ▸ hb',
          w'.left_eq, w'.right_eq, hTleft, hTright⟩
      · let perm : C3 ≃ₗ[ℝ] C3 :=
          { toFun := fun z => ((z.2, z.1.2), z.1.1)
            invFun := fun z => ((z.2, z.1.2), z.1.1)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        exact ⟨w'.right, w'.left, c'.trans perm.toContinuousLinearEquiv,
          hlu ▸ hb', hru ▸ ha', w'.right_eq, w'.left_eq, hTright, hTleft⟩
    let V := (w.left.target ∩ w.left.symm ⁻¹' left.source) ∩
      (w.right.target ∩ w.right.symm ⁻¹' right.source)
    have hV : IsOpen V := (w.left.symm.isOpen_inter_preimage left.open_source).inter
      (w.right.symm.isOpen_inter_preimage right.open_source)
    have hyV : y ∈ V := by
      have hly' : w.left xl = y := by rw [congrFun w.left_eq xl]; exact hly
      have hry' : w.right xr = y := by rw [congrFun w.right_eq xr]; exact hyr
      refine ⟨⟨hly' ▸ w.left.map_source hxl, ?_⟩,
        ⟨hry' ▸ w.right.map_source hxr.1, ?_⟩⟩
      · change w.left.symm y ∈ left.source
        rw [← hly', w.left.left_inv hxl]
        exact hleftpoint
      · change w.right.symm y ∈ right.source
        rw [← hry', w.right.left_inv hxr.1]
        exact hrightpoint
    have same_image (A B : OpenPartialHomeomorph t.Carrier s.Carrier)
        (hA : (A : t.Carrier → s.Carrier) = p)
        (hB : (B : t.Carrier → s.Carrier) = p) (x : s.Carrier)
        (hx : x ∈ A.target ∩ A.symm ⁻¹' B.source) :
        (x ∈ p '' (initial.map '' D ∩ A.source) ↔
          x ∈ p '' (initial.map '' D ∩ B.source)) := by
      have hp : p (A.symm x) = x := by rw [← hA]; exact A.right_inv hx.1
      have hAx := A.map_target hx.1
      constructor
      · rintro ⟨u, ⟨hu, huA⟩, hux⟩
        have heu : u = A.symm x := A.injOn huA hAx (by rw [hA]; exact hux.trans hp.symm)
        exact ⟨u, ⟨hu, heu.symm ▸ hx.2⟩, hux⟩
      · rintro ⟨u, ⟨hu, huB⟩, hux⟩
        have heu : u = A.symm x := B.injOn huB hx.2 (by rw [hB]; exact hux.trans hp.symm)
        exact ⟨u, ⟨hu, heu.symm ▸ hAx⟩, hux⟩
    obtain ⟨i, hyi⟩ := s.cover y
    let A := (s.charts i).symm.trans Q
    let B := (s.charts i).symm.trans T
    let F := A.symm.trans B
    have hF : F ∈ piecewiseAffineGroupoid V3 :=
      (piecewiseAffineGroupoid V3).trans ((piecewiseAffineGroupoid V3).symm (hQPL i)) (hTPL i)
    have hviA : v ∈ A.target := ⟨hJQ (interior_subset hvJ), hyi⟩
    have hviB : A.symm v ∈ B.source := by
      refine ⟨(s.charts i).map_source hyi, ?_⟩
      change (s.charts i).symm ((s.charts i) y) ∈ T.source
      rw [(s.charts i).left_inv hyi]
      exact hyT'
    have hvF : v ∈ F.source := ⟨hviA, hviB⟩
    have hFvalue (z : V3) (hz : z ∈ F.source) : F z = T (Q.symm z) := by
      change T ((s.charts i).symm ((s.charts i) (Q.symm z))) = T (Q.symm z)
      rw [(s.charts i).left_inv hz.1.2]
    let shift : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-v)
    have hshift : shift v = 0 := by change -v + v = 0; exact neg_add_cancel v
    have hshiftinv : shift.symm 0 = v := by rw [← hshift, shift.symm_apply_apply]
    let Dcoord := coord.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv
    let H₀ := shift.symm.toHomeomorph.toOpenPartialHomeomorph.trans
      (F.trans Dcoord.toHomeomorph.toOpenPartialHomeomorph)
    let O := shift '' (interior J.space ∩ (Q.target ∩ Q.symm ⁻¹' V))
    have hO : IsOpen O := shift.toHomeomorph.isOpenMap _
      (isOpen_interior.inter (Q.symm.isOpen_inter_preimage hV))
    let H := H₀.restrOpen O hO
    have hzeroH : (0 : V3) ∈ H.source := by
      refine ⟨⟨mem_univ _, ?_, mem_univ _⟩, ?_⟩
      · change shift.symm 0 ∈ F.source
        rw [hshiftinv]
        exact hvF
      · exact ⟨v, ⟨hvJ, hJQ (interior_subset hvJ), hyV⟩, hshift⟩
    have hHcenter : H 0 = 0 := by
      change Dcoord (F (shift.symm 0)) = 0
      rw [hshiftinv, hFvalue v hvF, hTy]
      exact map_zero coord
    have hHinv : LocallyPiecewiseAffineOn H.symm H.target := by
      have hfirst := hF.2.comp
        (locallyPiecewiseAffineOn_affine Dcoord.symm.toContinuousAffineMap isOpen_univ)
      have hsecond := (locallyPiecewiseAffineOn_affine
        shift.toContinuousAffineMap isOpen_univ).comp hfirst
      apply hsecond.mono H.open_target
      intro z hz
      exact ⟨⟨mem_univ _, hz.1.1.2⟩, mem_univ _⟩
    have hshiftK := K.affineOnFaces_affine shift.toContinuousAffineMap
    let Kshift := hshiftK.embeddedImage shift.injective.injOn
    have hKshifts : Kshift.space = shift '' K.space :=
      hshiftK.embeddedImage_space shift.injective.injOn
    let height : V3 →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
    have hheight (z : V3) : height (shift z) = (c z).2 := by
      change (c (-v + z)).2 = (c z).2
      rw [map_add, map_neg]
      change -(c v).2 + (c z).2 = (c z).2
      rw [hvzero, neg_zero, zero_add]
    have hparts (z : V3) (hz : z ∈ H.source) :
        (z ∈ Kshift.space ↔ (H z).1.1 = 0) ∧
          (height z = 0 ↔ (H z).2 = 0) := by
      let x := shift.symm z
      let y' := Q.symm x
      have hxF : x ∈ F.source := hz.1.2.1
      have hxJ : x ∈ interior J.space := by
        obtain ⟨a, ha, haz⟩ := hz.2
        change shift.symm z ∈ interior J.space
        rw [← haz, shift.symm_apply_apply]
        exact ha.1
      have hy'V : y' ∈ V := by
        obtain ⟨a, ha, haz⟩ := hz.2
        change Q.symm (shift.symm z) ∈ V
        rw [← haz, shift.symm_apply_apply]
        exact ha.2.2
      have hy'Q : y' ∈ Q.source := Q.map_target (hJQ (interior_subset hxJ))
      have hy'T : y' ∈ T.source := by
        have h := hxF.2.2
        change (s.charts i).symm ((s.charts i) y') ∈ T.source at h
        rwa [(s.charts i).left_inv hxF.1.2] at h
      have hQy' : Q y' = x := Q.right_inv (hJQ (interior_subset hxJ))
      have hrightimage : x ∈ K.space ↔
          y' ∈ p '' (initial.map '' D ∩ w.right.source) := by
        rw [hKs, hPs]
        constructor
        · rintro ⟨⟨u, ⟨hu, huT⟩, hux⟩, _⟩
          refine ⟨u, ⟨hu, huT.1⟩, ?_⟩
          have huQ : w.right u ∈ Q.source := huT.2
          rw [congrFun w.right_eq u] at huQ
          apply Q.injOn huQ hy'Q
          change Q (w.right u) = x at hux
          rw [congrFun w.right_eq u] at hux
          exact hux.trans hQy'.symm
        · rintro ⟨u, ⟨hu, huw⟩, huy⟩
          refine ⟨⟨u, ⟨hu, huw, ?_⟩, ?_⟩, interior_subset hxJ⟩
          · change w.right u ∈ Q.source
            rw [congrFun w.right_eq u]
            change p u ∈ Q.source
            rw [huy]
            exact hy'Q
          · change Q (w.right u) = x
            rw [congrFun w.right_eq u]
            change Q (p u) = x
            rw [huy, hQy']
      have hzeroimage : (c x).2 = 0 ↔
          y' ∈ p '' (initial.map '' D ∩ w.left.source) := by
        simpa only [hQy'] using (hplane y' hy'Q).symm
      have hback : z ∈ Kshift.space ↔ x ∈ K.space := by
        rw [hKshifts]
        constructor
        · rintro ⟨u, hu, huz⟩
          change shift.symm z ∈ K.space
          rwa [← huz, shift.symm_apply_apply]
        · intro h
          exact ⟨x, h, shift.apply_symm_apply z⟩
      have hheightback : height z = (c x).2 := by
        have hh := hheight x
        change height (shift (shift.symm z)) = (c x).2 at hh
        simpa only [shift.apply_symm_apply] using hh
      have hHval : H z = coord (T y') := by
        change Dcoord (F x) = coord (T y')
        rw [hFvalue x hxF]
        rfl
      constructor
      · rw [hback, hrightimage, same_image w.right right w.right_eq hreq y' hy'V.2,
          hrightplane y' hy'T, hHval]
      · rw [hheightback, hzeroimage, same_image w.left left w.left_eq hleq y' hy'V.1,
          hleftplane y' hy'T, hHval]
    refine ⟨H, hzeroH, hHcenter, hHinv, ?_, fun z hz => (hparts z hz).2⟩
    intro z hz
    change z ∈ shift '' K.space ↔ (H z).1.1 = 0
    rw [← hKshifts]
    exact (hparts z hz).1
  have happroach (v : V3) (hvP₀ : v ∈ P₀.space) (hvJ : v ∈ interior J.space)
      (hvzero : (c v).2 = 0) :
      v ∈ closure (K.space ∩ {z | 0 < (c z).2}) ∧
      v ∈ closure (K.space ∩ {z | (c z).2 < 0}) := by
    obtain ⟨H, hzeroH, hHcenter, _hHinv, hsheet, hflat⟩ := old_chart v hvP₀ hvJ hvzero
    let shift : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-v)
    have hshift : shift v = 0 := by change -v + v = 0; exact neg_add_cancel v
    have hshiftK := K.affineOnFaces_affine shift.toContinuousAffineMap
    let Kshift := hshiftK.embeddedImage shift.injective.injOn
    have hKshifts : Kshift.space = shift '' K.space :=
      hshiftK.embeddedImage_space shift.injective.injOn
    let height : V3 →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
    have hheight (z : V3) : height (shift z) = (c z).2 := by
      change (c (-v + z)).2 = (c z).2
      rw [map_add, map_neg]
      change -(c v).2 + (c z).2 = (c z).2
      rw [hvzero, neg_zero, zero_add]
    have hsigns := signed_approach_of_crossing_chart Kshift height
      (c.symm ((0, 0), 1)) (by change (c (c.symm ((0, 0), 1))).2 = 1; rw [c.apply_symm_apply])
      H hzeroH hHcenter hflat (fun z hz => by rw [hKshifts]; exact hsheet z hz)
    have pull (test : ℝ → Prop)
        (hcl : (0 : V3) ∈ closure (Kshift.space ∩ {x | test (height x)})) :
        v ∈ closure (K.space ∩ {x | test ((c x).2)}) := by
      apply _root_.mem_closure_iff.mpr
      intro O hO hvO
      obtain ⟨z, hzO, hzK, hzt⟩ := _root_.mem_closure_iff.mp hcl (shift '' O)
        (shift.toHomeomorph.isOpenMap _ hO) ⟨v, hvO, hshift⟩
      obtain ⟨x, hxO, rfl⟩ := hzO
      have hxK : x ∈ K.space := shift.injective.mem_set_image.mp (hKshifts.subset hzK)
      have hxTest : test ((c x).2) := by
        rw [← hheight x]
        exact hzt
      exact ⟨x, hxO, hxK, hxTest⟩
    exact ⟨pull (fun x => 0 < x) hsigns.1, pull (fun x => x < 0) hsigns.2⟩
  have hcount (v : V3) (hv : v ∈ K₀.vertices) (hvJ : v ∈ interior J.space)
      (hvzero : (c v).2 = 0) :
      ((K.link v).space ∩ {z | (c z).2 = 0}).ncard = 2 ∧
      (∃ z ∈ (K.link v).space, 0 < (c z).2) ∧
      ∃ z ∈ (K.link v).space, (c z).2 < 0 := by
    have hvK : v ∈ K.vertices := hK₀K hv
    have hvP₀ : v ∈ P₀.space := hK₀s.subset (K₀.vertices_subset_space hv)
    obtain ⟨H, hzeroH, hHcenter, hHinv, hsheet, hflat⟩ := old_chart v hvP₀ hvJ hvzero
    let shift : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-v)
    have hshift : shift v = 0 := by change -v + v = 0; exact neg_add_cancel v
    have hshiftK := K.affineOnFaces_affine shift.toContinuousAffineMap
    let Kshift := hshiftK.embeddedImage shift.injective.injOn
    have hKshift : Kshift.faces.Finite := hshiftK.embeddedImage_finite shift.injective.injOn hK
    have hKshifts : Kshift.space = shift '' K.space :=
      hshiftK.embeddedImage_space shift.injective.injOn
    have hzeroKshift : (0 : V3) ∈ Kshift.vertices := by
      rw [hshiftK.embeddedImage_vertices shift.injective.injOn]
      exact ⟨v, hvK, hshift⟩
    let height : V3 →L[ℝ] ℝ :=
      (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
    have hheight (z : V3) : height (shift z) = (c z).2 := by
      change (c (-v + z)).2 = (c z).2
      rw [map_add, map_neg]
      change -(c v).2 + (c z).2 = (c z).2
      rw [hvzero, neg_zero, zero_add]
    have hparts (z : V3) (hz : z ∈ H.source) :
        (z ∈ Kshift.space ↔ (H z).1.1 = 0) ∧ (height z = 0 ↔ (H z).2 = 0) := by
      refine ⟨?_, hflat z hz⟩
      rw [hKshifts]
      exact hsheet z hz
    have hzeroCount := link_zero_ncard_of_crossing_chart Kshift hKshift hzeroKshift
      height.toLinearMap
      H hzeroH hHcenter hHinv (fun z hz => and_congr (hparts z hz).1 (hparts z hz).2)
    have hsurface := signed_approach_of_crossing_chart Kshift height
      (c.symm ((0, 0), 1)) (by change (c (c.symm ((0, 0), 1))).2 = 1; rw [c.apply_symm_apply])
      H hzeroH hHcenter (fun z hz => (hparts z hz).2) (fun z hz => (hparts z hz).1)
    have hsigns := Kshift.exists_both_link_signs_of_surface_accumulation
      hKshift hzeroKshift height.toLinearMap hsurface.1 hsurface.2
    have hlink : (Kshift.link 0).space = shift '' (K.link v).space := by
      have h := hshiftK.embeddedImage_link_space shift.injective.injOn hvK
      change (Kshift.link (shift v)).space = shift '' (K.link v).space at h
      simpa only [hshift] using h
    have hzeros : shift '' ((K.link v).space ∩ {z | (c z).2 = 0}) =
        (Kshift.link 0).space ∩ {z | height z = 0} := by
      rw [hlink]
      ext x
      constructor
      · rintro ⟨z, ⟨hz, hz0⟩, rfl⟩
        exact ⟨mem_image_of_mem shift hz, (hheight z).trans hz0⟩
      · rintro ⟨⟨z, hz, rfl⟩, hz0⟩
        exact ⟨z, ⟨hz, (hheight z).symm.trans hz0⟩, rfl⟩
    change ((Kshift.link 0).space ∩ {z | height z = 0}).ncard = 2 at hzeroCount
    rw [← hzeros, shift.injective.injOn.ncard_image] at hzeroCount
    obtain ⟨⟨u, hu, hupos⟩, v', hv', hvneg⟩ := hsigns
    obtain ⟨u', hu', rfl⟩ := hlink.subset hu
    obtain ⟨v'', hv'', rfl⟩ := hlink.subset hv'
    exact ⟨hzeroCount, ⟨u', hu', by
      calc
        0 < height (shift u') := hupos
        _ = (c u').2 := hheight u'⟩,
      v'', hv'', by
        calc
          (c v'').2 = height (shift v'') := (hheight v'').symm
          _ < 0 := hvneg⟩
  refine ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ,
    ha, hb, haQ, hQzero, fun x hx => ⟨(hQW hx).1.1, (hQW hx).2⟩,
    hQw, hQPL, hbranches, hplane, hJ, hJQ, hzeroJ, hρ, hball, hclosed, hPs, hP₀s, hR₀, hR₀J,
    hKR, hKs, hqK, hqi.mono hKs.subset, hK₀K, hK₀s, hqint, hwhole,
    old_chart, happroach, hcount, hlinks,
    hL, hLs, hδ, hmargin, hmotions⟩

theorem OriginalGeneralPositionData.exists_protected_link_sections
    {s t : Stage e S f r C} {step : Step s t} {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    {old : StageMarkedDisk t R Fmark base Jgroup}
    (data : OriginalGeneralPositionData step old)
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (_hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark)) :
  ∀ a b : D, a ≠ b → (a : V2) ∉ Rim →
    step.projection (step.inclusion (data.initial.map a)) =
      step.projection (step.inclusion (data.initial.map b)) →
    ∀ U : Set s.Carrier, IsOpen U →
      step.projection (step.inclusion (data.initial.map a)) ∈ U →
      ∃ (w : TwoBranchWindow (step.projection ∘ step.inclusion))
        (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
        (J P P₀ R₀ K K₀ L : SimplicialComplex ℝ V3)
        (q : V3 → ℝ × ℝ) (ρ δ : ℝ),
        data.initial.map a ∈ w.left.source ∧ data.initial.map b ∈ w.right.source ∧
        step.projection (step.inclusion (data.initial.map a)) ∈ Q.source ∧
        Q (step.projection (step.inclusion (data.initial.map a))) = 0 ∧
        Q.source ⊆ U ∩ interior (s.projection ⁻¹' R) ∧ Q.source ⊆ w.target ∧
        (∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3) ∧
        (∀ k, (t.charts k).symm.trans (w.left.trans Q) ∈ piecewiseAffineGroupoid V3 ∧
          (t.charts k).symm.trans (w.right.trans Q) ∈ piecewiseAffineGroupoid V3) ∧
        (∀ y ∈ Q.source,
          y ∈ (step.projection ∘ step.inclusion) '' (data.initial.map '' D ∩ w.left.source) ↔
            (c (Q y)).2 = 0) ∧
        J.faces.Finite ∧ J.space ⊆ Q.target ∧ (0 : V3) ∈ interior J.space ∧
        0 < ρ ∧ ball (0 : V3) ρ ⊆ interior J.space ∧
        P.space = (w.right.trans Q) ''
          (data.initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space ∧
        P₀.space = P.space \ ball (0 : V3) ρ ∧
        R₀.faces.Finite ∧ R₀.IsSubdivision J ∧ K ≤ R₀ ∧ K.space = P.space ∧
        K.AffineOnFaces q ∧ InjOn q K.space ∧ K₀ ≤ K ∧ K₀.space = P₀.space ∧
        (∀ z ∈ P.space, z ∈ interior J.space → q z ∈ interior (q '' P.space)) ∧
        (step.projection ∘ step.inclusion) ⁻¹' (Q.symm '' J.space) =
          (w.left.trans Q).symm '' J.space ∪ (w.right.trans Q).symm '' J.space ∧
        (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
          ∃ T : OpenPartialHomeomorph V3 C3,
            (0 : V3) ∈ T.source ∧ T 0 = 0 ∧
            LocallyPiecewiseAffineOn T.symm T.target ∧
            (∀ z ∈ T.source, z ∈ (fun x : V3 => -v + x) '' K.space ↔
              (T z).1.1 = 0) ∧
            ∀ z ∈ T.source, (c z).2 = 0 ↔ (T z).2 = 0) ∧
        (∀ v ∈ P₀.space, v ∈ interior J.space → (c v).2 = 0 →
          v ∈ closure (K.space ∩ {z | 0 < (c z).2}) ∧
          v ∈ closure (K.space ∩ {z | (c z).2 < 0})) ∧
        (∀ v ∈ K₀.vertices, v ∈ interior J.space → (c v).2 = 0 →
          ((K.link v).space ∩ {z | (c z).2 = 0}).ncard = 2 ∧
          (∃ z ∈ (K.link v).space, 0 < (c z).2) ∧
          ∃ z ∈ (K.link v).space, (c z).2 < 0) ∧
        (∀ v ∈ K.vertices, v ∈ interior J.space →
          ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
            T.HasSimplicialEdges ∧ T.boundary ℝ = (K.link v).space) ∧
        L.faces.Finite ∧ L.space = J.space ∩ {z | (c z).2 = 0} ∧
        0 < δ ∧ (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → δ ≤ |(c v).2|) ∧
        ∀ ε : ℝ, 0 < ε → ∃ H : PLCarrierMotion J.space P₀.space ε,
          R₀.AffineOnFaces (H.map 1) ∧
          (∀ v ∈ R₀.vertices, (c v).2 ≠ 0 → ∀ u,
            (0 < (c (H.map u v)).2 ↔ 0 < (c v).2) ∧
            ((c (H.map u v)).2 < 0 ↔ (c v).2 < 0)) ∧
          (∀ v ∈ K.vertices,
            (c (H.map 1 v)).2 = 0 ↔ v ∈ K₀.vertices ∧ (c v).2 = 0) ∧
          (∀ face ∈ K.faces, (∀ v ∈ face, (c (H.map 1 v)).2 = 0) ↔
            face ∈ K₀.faces ∧ ∀ v ∈ face, (c v).2 = 0) ∧
          (∀ face ∈ K.faces, face ∉ K₀.faces → ∀ other ∈ L.faces,
            affineSpan ℝ (H.map 1 '' (face : Set V3) ∪ (other : Set V3)) = ⊤ ∨
              Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (face : Set V3))))
                (convexHull ℝ (other : Set V3))) ∧
          ∃ Kamb Knew : SimplicialComplex ℝ V3,
            Kamb.faces.Finite ∧ Kamb.space = J.space ∧ Knew ≤ Kamb ∧
            Knew.space = H.map 1 '' P.space ∧ K₀ ≤ Knew ∧
            Knew.AffineOnFaces (q ∘ (H.map 1).symm) ∧
            InjOn (q ∘ (H.map 1).symm) Knew.space ∧
            (∀ v ∈ K.vertices,
              (Knew.link (H.map 1 v)).space = H.map 1 '' (K.link v).space ∧
              (Knew.closedStar (H.map 1 v)).space = H.map 1 '' (K.closedStar v).space) ∧
            (∀ v ∈ K.vertices, v ∈ interior J.space →
              ∃ (n : ℕ) (T : Polygon V3 (n + 3)), Function.Injective T ∧
                T.HasSimplicialEdges ∧ T.boundary ℝ = (Knew.link (H.map 1 v)).space) ∧
          ∃ (G : I → t.Carrier ≃ₜ t.Carrier)
            (new : StageMarkedDisk t R Fmark base Jgroup),
            Continuous (fun z : I × t.Carrier => G z.1 z.2) ∧
            Continuous (fun z : I × t.Carrier => (G z.1).symm z.2) ∧
            (∀ x, G 0 x = x) ∧
            (∀ u, EqOn (G u)
              ((w.right.trans Q).symm ∘ H.map u ∘ (w.right.trans Q))
                (w.right.trans Q).source) ∧
            (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' J.space)ᶜ) ∧
            (∀ u, EqOn (G u) id ((w.right.trans Q).symm '' P₀.space)) ∧
            (∀ u, EqOn (G u) id w.left.source) ∧
            (∀ u, EqOn (G u) id (frontier (t.projection ⁻¹' R))) ∧
            (∀ u, (G u) ⁻¹' (t.projection ⁻¹' R) = t.projection ⁻¹' R) ∧
            (∀ u k l, (t.charts k).symm.trans
              ((G u).toOpenPartialHomeomorph.trans (t.charts l)) ∈ piecewiseAffineGroupoid V3) ∧
            (∀ x, new.map x = G 1 (data.initial.map x)) ∧ new.rim = data.initial.rim ∧
            HEq new.basepath data.initial.basepath ∧
            (∀ x : Rim, new.map x = data.initial.map x) ∧
            (w.right.trans Q) '' (new.map '' D ∩ (w.right.trans Q).source) ∩ J.space =
              H.map 1 '' P.space ∧
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
  intro a b hab haint hpair U hU haU
  obtain ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ, h⟩ :=
    data.exists_protected_link_sections_with_closed_support he hF _hopen
      a b hab haint hpair U hU haU
  refine ⟨w, c, Q, J, P, P₀, R₀, K, K₀, L, q, ρ, δ, ?_⟩
  rcases h with ⟨ha, hb, haQ, hQzero, hQU, hQw, hQPL, hbranches, hplane,
    hJ, hJQ, hzeroJ, hρ, hball, _hclosed, hrest⟩
  exact ⟨ha, hb, haQ, hQzero, hQU, hQw, hQPL, hbranches, hplane,
    hJ, hJQ, hzeroJ, hρ, hball, hrest⟩

end Geometry.OriginalPLTower
