import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryHistory
import PoincareConjecture.Proofs.M76.Dehn.OriginalMarkedFaceAssembly
import PoincareConjecture.Proofs.M76.Dehn.OriginalHistoryDoubleGraph

set_option autoImplicit false

open Set Metric Geometry Topology
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

set_option maxHeartbeats 800000 in

theorem Step.exists_original_old_crossing_assembly
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    (he : PoincareConjecture.M76.PLDomain e R) (hF : Fmark ⊆ frontier R)
    (hopen : IsOpen ((Subtype.val : frontier R → M) ⁻¹' Fmark))
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    (old : StageMarkedDisk t R Fmark base Jgroup) :
    ∃ (new : StageMarkedDisk t R Fmark base Jgroup)
      (eta : old.rim.Homotopy new.rim) (K A : SimplicialComplex ℝ V2),
      new.basepath = old.basepath.trans (eta.evalAt squareRimBase) ∧
      K.faces.Finite ∧ K.space = D ∧ A.faces.Finite ∧ A ≤ K ∧ A.space = Rim ∧
      ∃ (n : ℕ) (order : Fin n → K.faces) (P : ℕ → SimplicialComplex ℝ V2)
        (boundary : Fin n → Bool)
        (Q : Fin n → OpenPartialHomeomorph t.Carrier V3)
        (B : Fin n → OpenPartialHomeomorph s.Carrier V3)
        (J : Fin n → SimplicialComplex ℝ V3) (U : K.faces → Set t.Carrier)
        (states : ℕ → FaceDiskState t K U R Fmark)
        (motions : ∀ i : Fin n, FaceMotionData step K (P i.val) (P (i.val + 1))
          (states i.val).map (Q i) (B i) (J i) U R Fmark (boundary i)),
        Function.Bijective order ∧
        (∀ i k, (order k).val ⊂ (order i).val → k < i) ∧
        (∀ i k, k < i → (order i).val ∈ A.faces → (order k).val ∈ A.faces) ∧
        (∀ k, P k ≤ K ∧
          (P k).faces = {a | ∃ i : Fin n, i.val < k ∧ (order i).val = a}) ∧
        (∀ i : Fin n, (P (i.val + 1)).space = (P i.val).space ∪
          convexHull ℝ ((order i).val : Set V2)) ∧
        (∀ i, boundary i = true ↔ (order i).val ∈ A.faces) ∧
        (∀ i k, (t.charts k).symm.trans (Q i) ∈ piecewiseAffineGroupoid V3) ∧
        (∀ i k, (s.charts k).symm.trans (B i) ∈ piecewiseAffineGroupoid V3) ∧
        (∀ i z, Q i z = B i (step.projection (step.inclusion z))) ∧
        (∀ i, MapsTo (step.projection ∘ step.inclusion) (Q i).source (B i).source) ∧
        (∀ i, U (order i) ⊆ (Q i).source) ∧
        (states 0).map = old.map ∧ new.map = (states n).map ∧
        (∀ i : Fin n, (states (i.val + 1)).map =
          (motions i).ambient 1 ∘ (states i.val).map) ∧
        (∀ i k, i ≤ k → k ≤ n → EqOn (states k).map (states i).map (P i).space) ∧
        (∀ a : K.faces, InjOn ((step.projection ∘ step.inclusion) ∘ new.map)
          (convexHull ℝ (a.val : Set V2))) ∧
        ∃ (Z : SimplicialComplex ℝ (V2 × V2)) (G : SimplicialComplex ℝ V2)
          (first : Z.space ≃ₜ G.space) (E : Set (V2 × V2)),
          Z.faces.Finite ∧ G.faces.Finite ∧
          Z.space = {z | z.1 ∈ D ∧ z.2 ∈ D ∧
            step.projection (step.inclusion (new.map z.1)) =
              step.projection (step.inclusion (new.map z.2)) ∧ z.1 ≠ z.2} ∧
          G.space = {x | x ∈ D ∧ ∃ y ∈ D, x ≠ y ∧
            step.projection (step.inclusion (new.map x)) =
              step.projection (step.inclusion (new.map y))} ∧
          (∀ a ∈ Z.faces, a.card ≤ 2) ∧ (∀ a ∈ G.faces, a.card ≤ 2) ∧
          first.IsFinitePL ∧ first.symm.IsFinitePL ∧
          (∀ z : Z.space, (first z : V2) = z.val.1) ∧ E.Finite ∧
          E = {z | z ∈ Z.space ∧ ∃ a ∈ K.faces, a.card ≤ 2 ∧
            (z.1 ∈ convexHull ℝ (a : Set V2) ∨ z.2 ∈ convexHull ℝ (a : Set V2))} ∧
          ∀ a b : D, a ≠ b →
            step.projection (step.inclusion (new.map a)) =
              step.projection (step.inclusion (new.map b)) →
            ((a : V2), (b : V2)) ∉ E →
            ∀ W : Set s.Carrier, IsOpen W →
              step.projection (step.inclusion (new.map a)) ∈ W →
              ∃ (a' b' : D) (w : TwoBranchWindow (step.projection ∘ step.inclusion))
                (c : V3 ≃L[ℝ] C3) (T : OpenPartialHomeomorph s.Carrier V3),
                ((a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a)) ∧
                new.map a' ∈ w.left.source ∧ new.map b' ∈ w.right.source ∧
                step.projection (step.inclusion (new.map a)) ∈ T.source ∧
                T.source ⊆ W ∩ (interior (s.projection ⁻¹' R) ∩ w.target) ∧
                T (step.projection (step.inclusion (new.map a))) = 0 ∧
                (∀ k, (s.charts k).symm.trans T ∈ piecewiseAffineGroupoid V3) ∧
                (∀ k, (t.charts k).symm.trans (w.left.trans T) ∈
                  piecewiseAffineGroupoid V3 ∧
                  (t.charts k).symm.trans (w.right.trans T) ∈ piecewiseAffineGroupoid V3) ∧
                (step.projection ∘ step.inclusion) ⁻¹' T.source =
                  (w.left.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∪
                    (w.right.source ∩ (step.projection ∘ step.inclusion) ⁻¹' T.source) ∧
                (∀ y ∈ T.source,
                  y ∈ (step.projection ∘ step.inclusion) ''
                    (new.map '' D ∩ w.left.source) ↔ (c (T y)).2 = 0) ∧
                ∀ y ∈ T.source,
                  y ∈ (step.projection ∘ step.inclusion) ''
                    (new.map '' D ∩ w.right.source) ↔ (c (T y)).1.1 = 0 := by
  classical
  obtain ⟨_, K, A, _, _, hK, hKs, hA, hAK, hAs, _,
    n, order, horder, hbefore, hphase, P, hP, _, _, _,
    boundary, Q, B, J, U, hboundary, hPsucc, _, hcharts, _, hUbox,
    states, hstates0, hsteps, hstable, hcell,
    _, rim', eta, _, _, _, _, _, _, hrim', hout'⟩ :=
    step.exists_original_marked_face_assembly he hF hopen old.piecewiseAffine old.embedding
      old.inside old.whole_boundary_iff old.rim old.boundary_values old.basepath Jgroup old.outside
  choose motions htransitions using fun i : Fin n => hsteps i.val i.isLt
  have hP' : ∀ k, P k ≤ K ∧
      (P k).faces = {a | ∃ i : Fin n, i.val < k ∧ (order i).val = a} := fun k => (hP k).2
  have hQ := fun i => (hcharts i).2.1
  have hB := fun i => (hcharts i).2.2.1
  have hval := fun i => (hcharts i).2.2.2.2.1
  have hmaps := fun i => (hcharts i).2.2.2.2.2.1
  have hUQ : ∀ i, U (order i) ⊆ (Q i).source := fun i _ hx => (hUbox i hx).1
  let new : StageMarkedDisk t R Fmark base Jgroup := {
    map := (states n).map
    rim := rim'
    piecewiseAffine := by simpa only [hKs] using (states n).original_PL
    embedding := (states n).embedding.comp (Homeomorph.setCongr hKs.symm).isEmbedding
    inside := by simpa only [hKs] using (states n).region
    boundary_values := hrim'
    whole_boundary_iff := fun x => (states n).proper x (hKs.symm.subset x.property)
    basepath := old.basepath.trans (eta.evalAt squareRimBase)
    outside := hout' }
  obtain ⟨Z, G, first, hZ, hG, hZs, hGs, hZcard, hGcard, hfirst, hfirstinv, hfirstval⟩ :=
    step.exists_finite_history_double_graph hK A hAs order horder hbefore hphase
      P hP' hPsucc boundary hboundary Q B J hQ hB hval hmaps U hUQ
      states motions htransitions hstable hcell
  let E : Set (V2 × V2) := {z | z ∈ Z.space ∧ ∃ a ∈ K.faces, a.card ≤ 2 ∧
    (z.1 ∈ convexHull ℝ (a : Set V2) ∨ z.2 ∈ convexHull ℝ (a : Set V2))}
  have hE : E.Finite := by
    apply (step.finite_history_original_edge_pairs hK A hAs order horder hbefore hphase
      P hP' hPsucc boundary hboundary Q B J hQ hval hmaps U hUQ
      states motions htransitions hstable hcell).subset
    intro z hz
    have hz' := hZs.subset hz.1
    exact ⟨hz'.1, hz'.2.1, hz'.2.2.2, hz'.2.2.1, hz.2⟩
  refine ⟨new, eta, K, A, rfl, hK, hKs, hA, hAK, hAs,
    n, order, P, boundary, Q, B, J, U, states, motions,
    horder, hbefore, hphase, hP', hPsucc, hboundary, hQ, hB, hval, hmaps, hUQ,
    hstates0, rfl, htransitions, hstable, hcell,
    Z, G, first, E, hZ, hG, ?_, ?_, hZcard, hGcard,
    hfirst, hfirstinv, hfirstval, hE, rfl, ?_⟩
  · simpa only [hKs] using hZs
  · simpa only [hKs] using hGs
  intro a b hab hpair hoff W hW haW
  let p := step.projection ∘ step.inclusion
  let jf := new.map
  let lower : V2 → s.Carrier := p ∘ jf
  let y₀ := lower a
  have hinj : InjOn jf K.space := by
    intro x hx y hy heq
    have heq' : (⟨x, hx⟩ : K.space) = ⟨y, hy⟩ := (states n).embedding.injective heq
    exact congrArg Subtype.val heq'
  have haK : (a : V2) ∈ K.space := hKs.symm.subset a.property
  have hbK : (b : V2) ∈ K.space := hKs.symm.subset b.property
  have hab' : (a : V2) ≠ b := fun h => hab (Subtype.ext h)
  have habZ : ((a : V2), (b : V2)) ∈ Z.space :=
    hZs.symm.subset ⟨haK, hbK, hpair, hab'⟩
  have hoff' : ∀ c ∈ K.faces, c.card ≤ 2 →
      (a : V2) ∉ convexHull ℝ (c : Set V2) ∧ (b : V2) ∉ convexHull ℝ (c : Set V2) := by
    intro c hc hcard
    constructor
    · intro hac
      exact hoff ⟨habZ, c, hc, hcard, Or.inl hac⟩
    · intro hbc
      exact hoff ⟨habZ, c, hc, hcard, Or.inr hbc⟩
  obtain ⟨i, k, x, y, H, hki, hswap, hxface, hyface, hi3, hk3, _hfalse,
    _hxQ, hyB, hcommon, hpH, _hHB, hH0, hHPL, _hHiPL, hleftface, hrightface⟩ :=
    step.exists_history_original_crossed_pair hK A hAs order horder hbefore
      P hP' hPsucc boundary hboundary Q B J hQ hB hval hmaps U hUQ
      states motions htransitions hstable hcell haK hbK hab' hpair hoff'
  have hxK : x ∈ K.space := K.convexHull_subset_space (order i).property
    (intrinsicInterior_subset hxface)
  have hyK : y ∈ K.space := K.convexHull_subset_space (order k).property
    (intrinsicInterior_subset hyface)
  let a' : D := ⟨x, hKs.subset hxK⟩
  let b' : D := ⟨y, hKs.subset hyK⟩
  have hswap' : (a' = a ∧ b' = b) ∨ (a' = b ∧ b' = a) :=
    hswap.elim (fun h => Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
      (fun h => Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩)
  have hxbase : lower x = y₀ := by
    rcases hswap with ⟨hx, _⟩ | ⟨hx, _⟩
    · exact congrArg lower hx
    · exact (congrArg lower hx).trans hpair.symm
  have hybase : lower y = y₀ := by
    rcases hswap with ⟨_, hy⟩ | ⟨_, hy⟩
    · exact (congrArg lower hy).trans hpair.symm
    · exact congrArg lower hy
  have hxne : x ≠ y := by
    intro heq
    have haa : a' = b' := Subtype.ext heq
    rcases hswap' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hab haa
    · exact hab haa.symm
  obtain ⟨w, hxw, hyw⟩ := step.projectionInclusion_local.exists_twoBranchWindow
    (fun z => (step.projectionInclusion_fiber z).1)
    (fun z => (step.projectionInclusion_fiber z).2)
    (hxbase.trans hybase.symm) (fun h => hxne (hinj hxK hyK h))
  have hfullInterior {v : V2} {c : Finset V2} (hc : c ∈ K.faces) (hc3 : c.card = 3)
      (hv : v ∈ intrinsicInterior ℝ (convexHull ℝ (c : Set V2))) :
      v ∈ interior (convexHull ℝ (c : Set V2)) := by
    let L := K.vertexSubcomplex (c : Set V2)
    have hs : L.space = convexHull ℝ (c : Set V2) := K.vertexSubcomplex_face_space hc
    have hint := L.mem_interior_space_of_full_face
      (show c ∈ L.faces from ⟨hc, fun _ hz => hz⟩)
      (by simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hc3) hv
    simpa only [hs] using hint
  have hxint := hfullInterior (order i).property hi3 hxface
  have hyint := hfullInterior (order k).property hk3 hyface
  have hbad (c : Finset V2) : IsClosed (jf '' (K.space \ interior (convexHull ℝ (c : Set V2)))) :=
    (((K.isCompact_space_of_finite hK).diff isOpen_interior).image_of_continuousOn
      ((states n).original_PL.continuousOn.mono sdiff_subset)).isClosed
  have isolate (branch : OpenPartialHomeomorph t.Carrier s.Carrier)
      (hbranch : (branch : t.Carrier → s.Carrier) = p) (hbt : branch.target = w.target)
      {v : V2} (hvK : v ∈ K.space) (hvb : jf v ∈ branch.source)
      (hvbase : lower v = y₀) {c : Finset V2}
      (hv : v ∈ interior (convexHull ℝ (c : Set V2))) :
      ∃ V : Set s.Carrier, IsOpen V ∧ y₀ ∈ V ∧ V ⊆ w.target ∧
        ∀ z ∈ V, ∀ q ∈ D, jf q ∈ branch.source → lower q = z →
          q ∈ interior (convexHull ℝ (c : Set V2)) := by
    let bad := jf '' (K.space \ interior (convexHull ℝ (c : Set V2)))
    let V := branch.target ∩ branch.symm ⁻¹' badᶜ
    have hV : IsOpen V := branch.isOpen_inter_preimage_symm (hbad c).isOpen_compl
    have hleft (q : t.Carrier) (hq : q ∈ branch.source) : branch.symm (p q) = q := by
      rw [← congrFun hbranch q]
      exact branch.left_inv hq
    have hyV : y₀ ∈ V := by
      refine ⟨?_, ?_⟩
      · have hpoint : branch (jf v) = y₀ := (congrFun hbranch (jf v)).trans hvbase
        exact hpoint ▸ branch.map_source hvb
      · change branch.symm y₀ ∉ bad
        rw [← hvbase]
        change branch.symm (p (jf v)) ∉ bad
        rw [hleft _ hvb]
        rintro ⟨q, ⟨hq, hqout⟩, heq⟩
        exact hqout ((hinj hq hvK heq).symm ▸ hv)
    refine ⟨V, hV, hyV, fun _ hz => hbt.subset hz.1, ?_⟩
    intro z hz q hqD hqb hqz
    by_contra hqout
    apply hz.2
    have hqinv : branch.symm z = jf q := by
      rw [← hqz]
      exact hleft _ hqb
    exact ⟨q, ⟨hKs.symm.subset hqD, hqout⟩, hqinv.symm⟩
  obtain ⟨V, hV, hyV, hVw, hVL⟩ :=
    isolate w.left w.left_eq w.left_target hxK hxw hxbase hxint
  obtain ⟨V', hV', hyV', _hV'w, hVR⟩ :=
    isolate w.right w.right_eq w.right_target hyK hyw hybase hyint
  have haNotRim : (a : V2) ∉ Rim := by
    intro haRim
    obtain ⟨c, hc, hac⟩ := SimplicialComplex.mem_space_iff.mp (hAs.symm.subset haRim)
    have hint : interior A.space = ∅ := by rw [hAs, interior_sphere']
    have hc2 : c.card ≤ 2 := by
      simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using
        A.face_card_le_of_interior_space_eq_empty hint hc
    exact (hoff' c (hAK hc) hc2).1 hac
  have hyR : y₀ ∈ interior (s.projection ⁻¹' R) := by
    have hyinside : y₀ ∈ s.projection ⁻¹' R :=
      (step.region_preimage R).subset (new.inside a.property)
    by_contra hn
    have hyfront : y₀ ∈ frontier (s.projection ⁻¹' R) := ⟨subset_closure hyinside, hn⟩
    have hupper : new.map a ∈ frontier (t.projection ⁻¹' R) :=
      (step.frontier_preimage R).symm.subset hyfront
    exact haNotRim ((new.whole_boundary_iff a).mp hupper)
  let N := W ∩ (interior (s.projection ⁻¹' R) ∩ (V ∩ V'))
  have hN : IsOpen N := hW.inter (isOpen_interior.inter (hV.inter hV'))
  have hyN : y₀ ∈ N := ⟨haW, hyR, hyV, hyV'⟩
  let c : V3 ≃L[ℝ] C3 := ContinuousLinearEquiv.ofFinrankEq (by simp [Module.finrank_prod])
  let coord := H.trans c.symm.toHomeomorph.toOpenPartialHomeomorph
  let T₀ := (B i).trans coord
  let T := T₀.restrOpen N hN
  have hyBi : y₀ ∈ (B i).source := by
    change lower y ∈ (B i).source at hyB
    exact hybase ▸ hyB
  have hycoord : B i y₀ = Q i (jf x) := (congrArg (B i) hybase).symm.trans hcommon.symm
  have hyT : y₀ ∈ T.source :=
    ⟨⟨hyBi, hycoord.symm ▸ hpH, mem_univ _⟩, hyN⟩
  have hTw : T.source ⊆ w.target := fun _ hz => hVw hz.2.2.2.1
  have hTvalue (z : s.Carrier) : c (T z) = H (B i z) := c.apply_symm_apply _
  have hTPL (l : s.Index) : (s.charts l).symm.trans T ∈ piecewiseAffineGroupoid V3 := by
    have hcoord := (locallyPiecewiseAffineOn_affine
      c.symm.toContinuousLinearMap.toContinuousAffineMap isOpen_univ).comp hHPL
    have hcomp := hcoord.comp (hB i l).1
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    exact hcomp.mono ((s.charts l).symm.trans T).open_source
      (fun z hz => ⟨⟨hz.1, hz.2.1.1⟩, hz.2.1.2⟩)
  have hbranchPL (branch : OpenPartialHomeomorph t.Carrier s.Carrier)
      (hbranch : (branch : t.Carrier → s.Carrier) = p) (k : t.Index) :
      (t.charts k).symm.trans (branch.trans T) ∈ piecewiseAffineGroupoid V3 := by
    apply (mem_piecewiseAffineGroupoid_iff_forward _).mpr
    intro z hz
    obtain ⟨l, hl⟩ := s.cover (branch ((t.charts k).symm z))
    let F := (t.charts k).symm.trans (branch.trans (s.charts l))
    let G := (s.charts l).symm.trans T
    have hF : F ∈ piecewiseAffineGroupoid V3 := step.branch_chart_PL branch
      (fun x _ => congrFun hbranch x) k l
    have hG : G ∈ piecewiseAffineGroupoid V3 := hTPL l
    have hzF : z ∈ F.source := ⟨hz.1, hz.2.1, hl⟩
    have hzG : F z ∈ G.source := by
      refine ⟨(s.charts l).map_source hl, ?_⟩
      change (s.charts l).symm ((s.charts l) (branch ((t.charts k).symm z))) ∈ T.source
      rw [(s.charts l).left_inv hl]
      exact hz.2.2
    obtain ⟨L, hL, hzL, hLF, hLG⟩ := hG.1.comp hF.1 z ⟨hzF, hzG⟩
    refine ⟨L, hL, hzL, ?_, ?_⟩
    · intro q hq
      have hf := (hLF hq).1
      have hg := (hLF hq).2
      refine ⟨hf.1, hf.2.1, ?_⟩
      have he := (s.charts l).left_inv hf.2.2
      exact (congrArg (fun v => v ∈ T.source) he).mp hg.2
    · apply hLG.congr
      intro q hq
      have hf := (hLF hq).1
      change T ((s.charts l).symm ((s.charts l) (branch ((t.charts k).symm q)))) =
        T (branch ((t.charts k).symm q))
      exact congrArg T ((s.charts l).left_inv hf.2.2)
  have hwhole : p ⁻¹' T.source =
      (w.left.source ∩ p ⁻¹' T.source) ∪ (w.right.source ∩ p ⁻¹' T.source) := by
    ext z
    constructor
    · intro hz
      rcases w.whole_preimage.subset (hTw hz) with hl | hr
      · exact Or.inl ⟨hl, hz⟩
      · exact Or.inr ⟨hr, hz⟩
    · exact fun hz => hz.elim And.right And.right
  have hdistinct : (order i).val ≠ (order k).val := by
    intro heq
    exact (ne_of_gt hki) (horder.injective (Subtype.ext heq))
  have hno (u v : K.faces) (hu3 : u.val.card = 3) (hv3 : v.val.card = 3)
      (huv : u.val ≠ v.val) {q : V2}
      (hqu : q ∈ convexHull ℝ (u.val : Set V2))
      (hqv : q ∈ interior (convexHull ℝ (v.val : Set V2))) : False := by
    have hsub := K.subset_of_mem_intrinsicInterior_face v.property u.property
      (interior_subset_intrinsicInterior (𝕜 := ℝ) hqv) hqu
    exact huv ((Finset.eq_of_subset_of_card_le hsub (by omega)).symm)
  have hleft (z : s.Carrier) (hz : z ∈ T.source) :
      z ∈ p '' (jf '' D ∩ w.left.source) ↔
        z ∈ lower '' convexHull ℝ ((order i).val : Set V2) := by
    constructor
    · rintro ⟨v, ⟨⟨q, hqD, rfl⟩, hqL⟩, hqz⟩
      exact ⟨q, interior_subset (hVL z hz.2.2.2.1 q hqD hqL hqz), hqz⟩
    · rintro ⟨q, hqface, hqz⟩
      have hqD := hKs.subset (K.convexHull_subset_space (order i).property hqface)
      have hqwindow : jf q ∈ w.left.source ∪ w.right.source := by
        apply w.whole_preimage.subset
        change lower q ∈ w.target
        rw [hqz]
        exact hTw hz
      rcases hqwindow with hqL | hqR
      · exact ⟨jf q, ⟨mem_image_of_mem jf hqD, hqL⟩, hqz⟩
      · exact (hno (order i) (order k) hi3 hk3 hdistinct hqface
          (hVR z hz.2.2.2.2 q hqD hqR hqz)).elim
  have hright (z : s.Carrier) (hz : z ∈ T.source) :
      z ∈ p '' (jf '' D ∩ w.right.source) ↔
        z ∈ lower '' convexHull ℝ ((order k).val : Set V2) := by
    constructor
    · rintro ⟨v, ⟨⟨q, hqD, rfl⟩, hqR⟩, hqz⟩
      exact ⟨q, interior_subset (hVR z hz.2.2.2.2 q hqD hqR hqz), hqz⟩
    · rintro ⟨q, hqface, hqz⟩
      have hqD := hKs.subset (K.convexHull_subset_space (order k).property hqface)
      have hqwindow : jf q ∈ w.left.source ∪ w.right.source := by
        apply w.whole_preimage.subset
        change lower q ∈ w.target
        rw [hqz]
        exact hTw hz
      rcases hqwindow with hqL | hqR
      · exact (hno (order k) (order i) hk3 hi3 hdistinct.symm hqface
          (hVL z hz.2.2.2.1 q hqD hqL hqz)).elim
      · exact ⟨jf q, ⟨mem_image_of_mem jf hqD, hqR⟩, hqz⟩
  have hcoordinate (c₀ : Finset V2) (z : s.Carrier) (hz : z ∈ (B i).source) :
      z ∈ lower '' convexHull ℝ (c₀ : Set V2) ↔
        B i z ∈ B i '' (lower '' convexHull ℝ (c₀ : Set V2) ∩ (B i).source) := by
    constructor
    · intro hzface
      exact mem_image_of_mem (B i) ⟨hzface, hz⟩
    · rintro ⟨v, ⟨hvface, hvB⟩, heq⟩
      exact (B i).injOn hvB hz heq ▸ hvface
  refine ⟨a', b', w, c, T, hswap', hxw, hyw, hyT,
    fun z hz => ⟨hz.2.1, hz.2.2.1, hTw hz⟩, ?_, hTPL,
    fun k => ⟨hbranchPL w.left w.left_eq k, hbranchPL w.right w.right_eq k⟩,
    hwhole, ?_, ?_⟩
  · change c.symm (H (B i y₀)) = 0
    rw [hycoord, hH0]
    exact map_zero _
  · intro z hz
    rw [hTvalue]
    exact (hleft z hz).trans ((hcoordinate (order i).val z hz.1.1).trans
      (hleftface (B i z) hz.1.2.1))
  · intro z hz
    rw [hTvalue]
    exact (hright z hz).trans ((hcoordinate (order k).val z hz.1.1).trans
      (hrightface (B i z) hz.1.2.1))

end Geometry.OriginalPLTower
