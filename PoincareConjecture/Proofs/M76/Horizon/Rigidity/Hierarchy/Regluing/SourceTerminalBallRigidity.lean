import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.SourceTerminalBallPasting
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.FiniteCellGluing
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalTargetCells
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.PairedSlabGluing



set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "E3" => ((ℝ × ℝ) × ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates



theorem HamiltonZeroPastedTerminalBalls.exists_locally_injective_endpoint
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    {phi : C(H0, H0)} {N : Set X0} {u v a b alpha beta : ℝ}
    (pasted : HamiltonZeroPastedTerminalBalls e d phi N u v a b alpha beta)
    (hu : 0 < u) (huv : u < v) (hv : v < p)
    (hab : a < b) (hsecond : b < a + p)
    (halpha : alpha < beta) (hfirst : beta < alpha + p)
    (geometry : HamiltonZeroThirdPhaseGeometry e N phi u v)
    (hinj : IsLocallyInjective (fun x : (⋃ side : Bool, frontier
      (N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v))) =>
      hamiltonZeroAmbientMap phi x)) :
    ∃ g : C(X0, X0),
      ChartwisePLMap e d
        (⟨fun x : (univ : Set X0) => (⟨g x, mem_univ _⟩ : (univ : Set X0)),
          by fun_prop⟩ : C((univ : Set X0), (univ : Set X0))) ∧
      IsLocallyInjective (fun x : N => g x) ∧
      (∀ x ∉ N, g x = hamiltonZeroAmbientMap phi x) ∧
      ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel g (interior N)ᶜ,
        (∀ t x, x ∈ N → (Q0 (G (t, x))).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (G (t, x))).1.2 ∈ AddCircle.closedIntervalArc p a b) ∧
        ∀ t x, x ∈ ⋃ side : Bool, frontier (N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
          AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)) →
          G (t, x) = hamiltonZeroAmbientMap phi x := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  obtain ⟨n, P, H, g, hwhole, hcover, hdis, hP, hoverlap, hg,
    hformula, hinterior, hout, G, hGbox, hGfixed⟩ := pasted
  let T := fun side : Bool => N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
    AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
  let B : Set X0 := ⋃ side : Bool, frontier (T side)
  let Box := fun side : Bool =>
    (Icc (if side then v else u) (if side then u + p else v) ×ˢ Icc a b) ×ˢ Icc alpha beta
  let Target := fun side : Bool => hamiltonZeroTerminalTargetCell
    (if side then v else u) (if side then u + p else v) a b alpha beta
  have hpos (side : Bool) : (if side then v else u) < (if side then u + p else v) := by
    cases side <;> dsimp <;> linarith
  have hgap (side : Bool) : (if side then u + p else v) < (if side then v else u) + p := by
    cases side <;> dsimp <;> linarith
  have hprojected (side : Bool) : Target side = hamiltonZeroBoxProjection '' Box side :=
    hamiltonZero_terminal_target_cell_eq_projected_box _ _ _ _ _ _
  have htargetFront (side : Bool) : hamiltonZeroBoxProjection '' frontier (Box side) =
      frontier (Target side) :=
    hamiltonZero_terminal_target_cell_projected_frontier (hpos side).le hab.le halpha.le
      (hgap side) hsecond hfirst
  have hPT (i : Σ side : Bool, Fin (n side)) : P i ⊆ T i.1 :=
    (subset_iUnion (fun k => P ⟨i.1, k⟩) i.2).trans (hcover i.1).subset
  have hsep := hamiltonZero_third_slabs_separated hu huv hv geometry
  have hmark (i : Σ side : Bool, Fin (n side)) (x : P i) :
      (x : X0) ∈ B ↔ (x : X0) ∈ frontier (P i) := by
    constructor
    · intro hx
      obtain ⟨side, hxside⟩ := mem_iUnion.mp hx
      by_cases hs : side = i.1
      · subst side
        exact (hP i).2.2.2.symm.subset ⟨x.property, hxside⟩
      · rw [(hP i).2.1.closed.frontier_eq]
        refine ⟨x.property, ?_⟩
        intro hi
        have hint := interior_mono (hPT i) hi
        have hs' : i.1 = !side := Bool.eq_not_of_ne (Ne.symm hs)
        rw [hs'] at hint
        exact hsep side ((geometry.slabs side).1.closed.frontier_subset hxside) hint
    · intro hx
      exact mem_iUnion.mpr ⟨i.1, ((hP i).2.2.2.subset hx).2⟩
  have hsourceTargetFront (i : Σ side : Bool, Fin (n side)) (x : P i) :
      g x ∈ frontier (Target i.1) ↔ (x : X0) ∈ frontier (P i) := by
    have hboxClosed : IsClosed (Box i.1) := (isClosed_Icc.prod isClosed_Icc).prod isClosed_Icc
    have hreal : ((H i).symm x : E3) ∈ frontier (Box i.1) ↔
        (x : X0) ∈ frontier (P i) := by
      rw [hboxClosed.frontier_eq, (hP i).2.1.closed.frontier_eq]
      have hm : ((H i).symm x : E3) ∈ Box i.1 := ((H i).symm x).property
      simp only [mem_sdiff, hm, x.property, true_and]
      exact not_congr (hinterior i x).symm
    rw [← htargetFront i.1, hformula i x]
    constructor
    · rintro ⟨z, hz, heq⟩
      have hcoord := hamiltonZero_box_projection_injOn (hgap i.1) hsecond hfirst
        (hboxClosed.frontier_subset hz) ((H i).symm x).property heq
      exact hreal.mp (hcoord ▸ hz)
    · intro hx
      exact ⟨(H i).symm x, hreal.mpr hx, rfl⟩
  have hboundary : IsLocallyInjective (fun x : B => g x) := by
    have heq : (fun x : B => g x) = (fun x : B => hamiltonZeroAmbientMap phi x) := by
      funext x
      exact (G.map_one_left x).symm.trans (hGfixed 1 x x.property)
    rw [heq]
    exact hinj
  have hlocal : IsLocallyInjective (fun x : N => g x) := by
    apply isLocallyInjective_of_finite_marked_cells (B := B) P Sigma.fst Target
      (fun side => frontier (Target side)) g (fun i => (hP i).1.isClosed)
      (isClosed_iUnion_of_finite fun _ => isClosed_frontier) hwhole.symm.subset
    · intro i j hij hs
      rcases i with ⟨s, i⟩
      rcases j with ⟨t, j⟩
      dsimp at hs
      subst t
      exact hdis s (fun h => hij (by cases h; rfl))
    · intro i x hx
      rw [hprojected i.1, hformula i ⟨x, hx⟩]
      exact ⟨(H i).symm ⟨x, hx⟩, ((H i).symm ⟨x, hx⟩).property, rfl⟩
    · intro i x hx
      exact (hsourceTargetFront i ⟨x, hx⟩).trans (hmark i ⟨x, hx⟩).symm
    · intro i j hij
      simpa only [hamiltonZeroTerminalTargetCells, Bool.false_eq_true, if_false] using
        hamiltonZero_terminal_target_cells_inter_frontier halpha hfirst hab hsecond
          (fun _ => huv) (fun _ => show v < u + p by linarith)
          (false, i) (false, j) (fun heq => hij (congrArg Prod.snd heq))
    · intro i x hx y hy heq
      apply congrArg (fun z : P i => (z : X0))
        ((H i).symm.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) ?_)
      apply Subtype.ext
      exact hamiltonZero_box_projection_injOn (hgap i.1) hsecond hfirst
        ((H i).symm ⟨x, hx⟩).property ((H i).symm ⟨y, hy⟩).property
        ((hformula i ⟨x, hx⟩).symm.trans (heq.trans (hformula i ⟨y, hy⟩)))
    · exact hboundary
  refine ⟨g, hg, hlocal, hout, G, ?_, hGfixed⟩
  intro t x hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hwhole.symm.subset hx)
  obtain ⟨z, hz, heq⟩ := hGbox i t ⟨x, hxi⟩
  rw [← heq]
  change (Q0 ((Q0).symm _)).2 ∈ _ ∧ (Q0 ((Q0).symm _)).1.2 ∈ _
  rw [(Q0).apply_symm_apply]
  exact ⟨⟨z.2, hz.2, rfl⟩, ⟨z.1.2, hz.1.2, rfl⟩⟩

theorem ChartwisePLMap.hamiltonZeroHandleMap_of_univ
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3} {g : C(X0, X0)}
    (hg : ChartwisePLMap e d
      (⟨fun x : (univ : Set X0) => (⟨g x, mem_univ _⟩ : (univ : Set X0)),
        by fun_prop⟩ : C((univ : Set X0), (univ : Set X0)))) :
    ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 (hamiltonZeroHandleMap g)) := by
  have transfer {S T : Set X0} (hS : S = univ) (hT : T = univ)
      (f : C(S, T)) (hval : ∀ x : S, (f x : X0) = g x) : ChartwisePLMap e d f := by
    subst S
    subst T
    convert hg using 1
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (hval x)
  apply transfer hamiltonZeroDomain_eq_univ hamiltonZeroDomain_eq_univ
  intro x
  rw [hamiltonZeroHandleMap_domain]
  rfl




theorem exists_hamiltonZero_paired_slab_rigid_map
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    {R : Set X0} {chi eta : C(H0, H0)} {a b alpha beta : ℝ}
    (heta : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 eta))
    (geometry : HamiltonZeroSecondPhaseGeometry e R chi a b)
    (ha : 0 < a) (hab : a < b) (hb : b < p)
    (localMaps : ∀ side : Bool,
      let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      ∃ g : C(X0, X0),
        ChartwisePLMap e d
          (⟨fun x : (univ : Set X0) => (⟨g x, mem_univ _⟩ : (univ : Set X0)),
            by fun_prop⟩ : C((univ : Set X0), (univ : Set X0))) ∧
        IsLocallyInjective (fun x : N => g x) ∧
        (∀ x ∈ N, (Q0 (g x)).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (g x)).1.2 ∈ AddCircle.closedIntervalArc p
            (if side then b else a) (if side then a + p else b)) ∧
        Nonempty ((hamiltonZeroAmbientMap eta).HomotopyRel g (interior N)ᶜ) ∧
        EqOn g (hamiltonZeroAmbientMap chi) (frontier N)) :
    ∃ g : C(X0, X0),
      ChartwisePLMap e d
        (⟨fun x : (univ : Set X0) => (⟨g x, mem_univ _⟩ : (univ : Set X0)),
          by fun_prop⟩ : C((univ : Set X0), (univ : Set X0))) ∧
      IsLocallyInjective (fun x : R => g x) ∧
      (∀ x ∈ R, (Q0 (g x)).2 ∈ AddCircle.closedIntervalArc p alpha beta) ∧
      Nonempty ((hamiltonZeroAmbientMap eta).HomotopyRel g (interior R)ᶜ) := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  let N := fun side : Bool => R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
    AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
  choose g hg hinj hrange H hfixed using localMaps
  let JH (side : Bool) := Classical.choice (H side)
  have hcover : (⋃ side, N side) = R := by
    apply le_antisymm (iUnion_subset fun _ => inter_subset_left)
    intro x hx
    have hm := (complementary_closed_circle_arcs_union p a b).symm.subset
      (mem_univ (hamiltonZeroSecondCircleMap chi x))
    exact hm.elim (fun h => mem_iUnion.mpr ⟨false, hx, h⟩)
      (fun h => mem_iUnion.mpr ⟨true, hx, h⟩)
  have hNclosed (side) : IsClosed (N side) := (geometry.slabs side).1.closed
  have hNcompact (side) : IsCompact (N side) :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset (hNclosed side) (subset_univ _)
  have hsep := hamiltonZero_second_slabs_separated ha hab hb geometry
  have hoverlap (i j : Bool) (hij : i ≠ j) : N i ∩ N j ⊆ frontier (N i) := by
    intro x hx
    rw [(hNclosed i).frontier_eq]
    refine ⟨hx.1, ?_⟩
    have hi : i = !j := Bool.eq_not_of_ne hij
    rw [hi]
    exact hsep j hx.2
  let f : ∀ side, C(N side, X0) := fun side =>
    ⟨fun x => g side x, (g side).continuous.comp continuous_subtype_val⟩
  have hf (side) : ChartwisePLMap e d
      (⟨fun x : N side => (⟨f side x, mem_univ _⟩ : (univ : Set X0)),
        by fun_prop⟩ : C(N side, (univ : Set X0))) := by
    by_cases hne : (N side).Nonempty
    · exact (hg side).restrict_compact_domain (geometry.slabs side).1
        (hNcompact side) hne (subset_univ _)
    · refine ⟨(geometry.slabs side).1, (hg side).target_domain, isOpen_univ, ?_⟩
      intro x
      exact False.elim (hne ⟨x, x.property⟩)
  let J : ∀ side, (⟨fun x : N side => hamiltonZeroAmbientMap eta x,
      by fun_prop⟩ : C(N side, X0)).HomotopyRel (f side)
      ((Subtype.val : N side → X0) ⁻¹' frontier (N side)) := fun side =>
    { toFun := fun z => JH side (z.1, (z.2 : X0))
      continuous_toFun := (JH side).continuous.comp
        (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
      map_zero_left := fun x => (JH side).map_zero_left x
      map_one_left := fun x => (JH side).map_one_left x
      prop' := fun t x hx => (JH side).prop t x hx.2 }
  obtain ⟨Gmap, hGmap, hGon, _, G, _⟩ := exists_finite_originalPL_relative_pasting
    (hamiltonZeroAmbientMap eta) heta.hamiltonZeroAmbientMap_univ N hNclosed hoverlap f hf J
  have hGon' (side : Bool) (x : X0) (hx : x ∈ N side) : Gmap x = g side x :=
    hGon side ⟨x, hx⟩
  have hlocal (side : Bool) : IsLocallyInjective (fun x : N side => Gmap x) := by
    have heq : (fun x : N side => Gmap x) = (fun x : N side => g side x) :=
      funext (fun x => hGon' side x x.property)
    rw [heq]
    exact hinj side
  have hmark : EqOn Gmap (hamiltonZeroAmbientMap chi) (frontier (N false)) := by
    intro x hx
    exact (hGon' false x ((hNclosed false).frontier_subset hx)).trans (hfixed false hx)
  let phase : C(X0, C0) := ⟨fun x => (Q0 x).1.2, by fun_prop⟩
  have hopen : IsOpenMap phase := isOpenMap_snd.comp (isOpenMap_fst.comp (Q0).isOpenMap)
  have hq : phase.comp (hamiltonZeroAmbientMap chi) = hamiltonZeroSecondCircleMap chi := by
    ext x
    exact (hamiltonZeroSecondCircleMap_ambient chi x).symm
  have hRclosed : IsClosed R := hcover ▸ isClosed_iUnion_of_finite hNclosed
  have hall := hamiltonZero_locally_injective_of_complementary_slabs
    (chi := chi) hGmap.hamiltonZeroHandleMap_of_univ hRclosed phase hopen hab
    (show b < a + p by linarith)
  dsimp only at hall
  rw [hq, hamiltonZeroAmbientMap_handle] at hall
  have hlocalR := hall (geometry.slabs false).1 hmark (fun side x hx => by
    change (Q0 (Gmap x)).1.2 ∈ _
    rw [hGon' side x hx]
    exact (hrange side x hx).2) hlocal
  refine ⟨Gmap, hGmap, hlocalR, ?_, ?_⟩
  · intro x hx
    obtain ⟨side, hs⟩ := mem_iUnion.mp (hcover.symm.subset hx)
    rw [hGon' side x hs]
    exact (hrange side x hs).1
  · refine ⟨{ G.toHomotopy with prop' := ?_ }⟩
    intro t x hx
    apply G.prop t x
    intro hi
    obtain ⟨side, hs⟩ := mem_iUnion.mp hi
    exact hx (interior_mono inter_subset_left hs)




theorem HamiltonZeroSourceBoundaryDiskData.exists_relative_locally_injective_map
    {ι κ E : Type*} [TopologicalSpace E]
    {e : ι → OpenPartialHomeomorph X0 V3} {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)} {R : Set X0} {alpha beta : ℝ}
    (data : HamiltonZeroSourceBoundaryDiskData e d phi R alpha beta)
    (hab : alpha < beta) (hwidth : beta < alpha + p)
    {K : Set E} (hK : IsCompact K) {r : ℝ} (hr : 0 ≤ r) (c0 : E × ℝ → X0)
    (hc0 : ContinuousOn c0 (K ×ˢ Icc (-r) r))
    (hi0 : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c0 z))
    (hzero : c0 '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hproduct : ∀ x : K, (Q0 (hamiltonZeroAmbientMap phi (c0 (x, 0)))).1 = g x) :
    ∃ g : C(X0, X0),
      ChartwisePLMap e d
        (⟨fun x : (univ : Set X0) => (⟨g x, mem_univ _⟩ : (univ : Set X0)),
          by fun_prop⟩ : C((univ : Set X0), (univ : Set X0))) ∧
      IsLocallyInjective (fun x : R => g x) ∧
      (∀ x ∈ R, (Q0 (g x)).2 ∈ AddCircle.closedIntervalArc p alpha beta) ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel g (interior R)ᶜ) := by
  obtain ⟨a, ha, b, hb, chi, eta, _, heta, _, ⟨Geta⟩, _, _, _, geometry, hends⟩ :=
    data.exists_pasted_terminal_balls hd hab hwidth hK hr c0 hc0 hi0 hzero g hg hproduct
  have hsecondPos : a < b := by linarith [ha.2, hb.1]
  have hsecondWidth : b < a + p := by linarith [ha.1, hb.2]
  have localMaps : ∀ side : Bool,
      let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      ∃ g : C(X0, X0),
        ChartwisePLMap e d
          (⟨fun x : (univ : Set X0) => (⟨g x, mem_univ _⟩ : (univ : Set X0)),
            by fun_prop⟩ : C((univ : Set X0), (univ : Set X0))) ∧
        IsLocallyInjective (fun x : N => g x) ∧
        (∀ x ∈ N, (Q0 (g x)).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
          (Q0 (g x)).1.2 ∈ AddCircle.closedIntervalArc p
            (if side then b else a) (if side then a + p else b)) ∧
        Nonempty ((hamiltonZeroAmbientMap eta).HomotopyRel g (interior N)ᶜ) ∧
        EqOn g (hamiltonZeroAmbientMap chi) (frontier N) := by
    intro side N
    obtain ⟨u, hu, v, hv, terminal, psi, _, _, _, hthird,
      _, _, ⟨Gpsi⟩, hfixed, hunion, pasted⟩ := hends side
    have hgeometry : HamiltonZeroThirdPhaseGeometry e N psi u v := by
      constructor
      · intro side
        dsimp only
        rw [hthird]
        exact terminal.geometry.slabs side
      · intro theta htheta
        rw [hthird]
        exact terminal.geometry.groups theta htheta
    have hsPos : (if side then b else a) < (if side then a + p else b) := by
      cases side <;> dsimp <;> linarith
    have hsWidth : (if side then a + p else b) < (if side then b else a) + p := by
      cases side <;> dsimp <;> linarith
    obtain ⟨g, hg, hinj, _, Gball, hGrange, _⟩ := pasted.exists_locally_injective_endpoint
      (show 0 < u by linarith [hu.1]) (show u < v by linarith [hu.2, hv.1])
      (show v < p by linarith [hv.2]) hsPos hsWidth hab hwidth hgeometry hunion
    refine ⟨g, hg, hinj, ?_, ⟨Gpsi.trans Gball⟩, ?_⟩
    · intro x hx
      have h1 : Gball (1, x) = g x := Gball.map_one_left x
      exact Eq.mp (congrArg (fun y : X0 =>
        (Q0 y).2 ∈ AddCircle.closedIntervalArc p alpha beta ∧
        (Q0 y).1.2 ∈ AddCircle.closedIntervalArc p
          (if side then b else a) (if side then a + p else b)) h1) (hGrange 1 x hx)
    · intro x hx
      exact (Gball.fst_eq_snd hx.2).symm.trans (hfixed hx)
  obtain ⟨g, hg, hinj, hfirst, ⟨G⟩⟩ := exists_hamiltonZero_paired_slab_rigid_map heta
    geometry (show 0 < a by linarith [ha.1]) hsecondPos
      (show b < p by linarith [hb.2]) localMaps
  exact ⟨g, hg, hinj, hfirst, ⟨Geta.trans G⟩⟩

end PoincareConjecture.M76
