import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Arcs.Mathlib.ClosedArcCoordinates
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.Boundary.RetainedRectangleEdges
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Spheres.MinimalRemoval









set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem mem_frontier_three_interval_box_iff
    {a b u v alpha beta : ℝ} {z : (ℝ × ℝ) × ℝ}
    (hz : z ∈ (Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) :
    z ∈ frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) ↔
      (z.1.1 = u ∨ z.1.1 = v) ∨ (z.1.2 = a ∨ z.1.2 = b) ∨
        (z.2 = alpha ∨ z.2 = beta) := by
  have hinterval {x l r : ℝ} (hx : x ∈ Icc l r) :
      ¬ x ∈ Ioo l r ↔ x = l ∨ x = r := by
    constructor
    · intro h
      simp only [mem_Ioo, not_and_or, not_lt] at h
      rcases h with h | h
      · exact Or.inl (le_antisymm h hx.1)
      · exact Or.inr (le_antisymm hx.2 h)
    · rintro (rfl | rfl) <;> simp
  rw [(isClosed_Icc.prod isClosed_Icc |>.prod isClosed_Icc).frontier_eq]
  simp only [mem_sdiff, interior_prod_eq, interior_Icc, mem_prod,
    not_and_or, hinterval hz.1.1, hinterval hz.1.2, hinterval hz.2]
  simp only [mem_prod] at hz
  tauto

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_hamiltonZero_box_coordinate_map
    (phi : C(H0, H0)) {S : Set X0} {alpha beta a b u v : ℝ}
    (hfirstGap : beta < alpha + p) (hsecondGap : b < a + p) (hthirdGap : v < u + p)
    (hfirst : S ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : S ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hthird : S ⊆ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v) :
    ∃ lift : C(S, (ℝ × ℝ) × ℝ),
      (∀ x, lift x ∈ (Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) ∧
      (∀ x : S, Q0 (hamiltonZeroAmbientMap phi x) =
        ((((lift x).1.1 : C0), ((lift x).1.2 : C0)), ((lift x).2 : C0))) ∧
      ∀ x, lift x ∈ frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) ↔
        (hamiltonZeroThirdCircleMap phi x = (u : C0) ∨
          hamiltonZeroThirdCircleMap phi x = (v : C0)) ∨
        (hamiltonZeroSecondCircleMap phi x = (a : C0) ∨
          hamiltonZeroSecondCircleMap phi x = (b : C0)) ∨
        (hamiltonZeroCircleMap phi x = (alpha : C0) ∨
          hamiltonZeroCircleMap phi x = (beta : C0)) := by
  let inc : C(S, X0) := ⟨Subtype.val, continuous_subtype_val⟩
  let first := AddCircle.liftToClosedArc hfirstGap ((hamiltonZeroCircleMap phi).comp inc)
    (fun x => hfirst x.property)
  let second := AddCircle.liftToClosedArc hsecondGap ((hamiltonZeroSecondCircleMap phi).comp inc)
    (fun x => hsecond x.property)
  let third := AddCircle.liftToClosedArc hthirdGap ((hamiltonZeroThirdCircleMap phi).comp inc)
    (fun x => hthird x.property)
  let lift := (third.prodMk second).prodMk first
  have hmem (x : S) : lift x ∈ (Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta :=
    ⟨⟨AddCircle.liftToClosedArc_mem hthirdGap _ _ x,
      AddCircle.liftToClosedArc_mem hsecondGap _ _ x⟩,
      AddCircle.liftToClosedArc_mem hfirstGap _ _ x⟩
  refine ⟨lift, hmem, ?_, ?_⟩
  · intro x
    exact (Prod.ext (Prod.ext (AddCircle.liftToClosedArc_coe hthirdGap _ _ x)
      (AddCircle.liftToClosedArc_coe hsecondGap _ _ x))
      (AddCircle.liftToClosedArc_coe hfirstGap _ _ x)).symm
  · intro x
    rw [mem_frontier_three_interval_box_iff (hmem x)]
    have hab : a ≤ b := (hmem x).1.2.1.trans (hmem x).1.2.2
    have huv : u ≤ v := (hmem x).1.1.1.trans (hmem x).1.1.2
    have halpha : alpha ≤ beta := (hmem x).2.1.trans (hmem x).2.2
    change (third x = u ∨ third x = v) ∨ (second x = a ∨ second x = b) ∨
      (first x = alpha ∨ first x = beta) ↔ _
    rw [AddCircle.liftToClosedArc_eq_iff hthirdGap _ _ x ⟨le_rfl, huv⟩,
      AddCircle.liftToClosedArc_eq_iff hthirdGap _ _ x ⟨huv, le_rfl⟩,
      AddCircle.liftToClosedArc_eq_iff hsecondGap _ _ x ⟨le_rfl, hab⟩,
      AddCircle.liftToClosedArc_eq_iff hsecondGap _ _ x ⟨hab, le_rfl⟩,
      AddCircle.liftToClosedArc_eq_iff hfirstGap _ _ x ⟨le_rfl, halpha⟩,
      AddCircle.liftToClosedArc_eq_iff hfirstGap _ _ x ⟨halpha, le_rfl⟩]
    rfl

theorem HamiltonZeroThirdPhaseGeometry.frontier_box_faces
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 (Fin 3 → ℝ)}
    {N : Set X0} {phi : C(H0, H0)} {u v a b alpha beta : ℝ}
    (geometry : HamiltonZeroThirdPhaseGeometry e N phi u v)
    (hfront : ∀ x ∈ frontier N,
      (hamiltonZeroSecondCircleMap phi x = (a : C0) ∨
        hamiltonZeroSecondCircleMap phi x = (b : C0)) ∨
      (hamiltonZeroCircleMap phi x = (alpha : C0) ∨
        hamiltonZeroCircleMap phi x = (beta : C0))) (side : Bool) :
    let T := N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
    ∀ x ∈ frontier T,
      (hamiltonZeroThirdCircleMap phi x = ((if side then v else u : ℝ) : C0) ∨
        hamiltonZeroThirdCircleMap phi x = ((if side then u + p else v : ℝ) : C0)) ∨
      (hamiltonZeroSecondCircleMap phi x = (a : C0) ∨
        hamiltonZeroSecondCircleMap phi x = (b : C0)) ∨
      (hamiltonZeroCircleMap phi x = (alpha : C0) ∨
        hamiltonZeroCircleMap phi x = (beta : C0)) := by
  dsimp only
  intro x hx
  rw [(geometry.slabs side).2.1] at hx
  rcases hx with hx | hx | hx
  · exact Or.inr (hfront x hx.2)
  · left
    have h : hamiltonZeroThirdCircleMap phi x = (u : C0) := hx.2
    cases side <;> simp [h]
  · left
    have h : hamiltonZeroThirdCircleMap phi x = (v : C0) := hx.2
    cases side <;> simp [h]



theorem exists_hamiltonZero_terminal_boundary_map
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 (Fin 3 → ℝ)}
    {N : Set X0} {phi : C(H0, H0)} {u v a b alpha beta : ℝ}
    (geometry : HamiltonZeroThirdPhaseGeometry e N phi u v)
    (huv : u < v) (hwidth : v < u + p)
    (hfirstGap : beta < alpha + p) (hsecondGap : b < a + p)
    (hfirst : N ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : N ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hfront : ∀ x ∈ frontier N,
      (hamiltonZeroSecondCircleMap phi x = (a : C0) ∨
        hamiltonZeroSecondCircleMap phi x = (b : C0)) ∨
      (hamiltonZeroCircleMap phi x = (alpha : C0) ∨
        hamiltonZeroCircleMap phi x = (beta : C0))) (side : Bool) :
    let T := N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
    let Box := (Icc (if side then v else u) (if side then u + p else v) ×ˢ Icc a b) ×ˢ
      Icc alpha beta
    ∃ boundaryMap : C(frontier T, frontier Box), ∀ x : frontier T,
      Q0 (hamiltonZeroAmbientMap phi x) =
        (((((boundaryMap x : (ℝ × ℝ) × ℝ).1.1) : C0),
          (((boundaryMap x : (ℝ × ℝ) × ℝ).1.2) : C0)),
          (((boundaryMap x : (ℝ × ℝ) × ℝ).2) : C0)) := by
  dsimp only
  let T := N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
    AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
  have hgap : (if side then u + p else v) < (if side then v else u) + p := by
    cases side <;> dsimp <;> linarith
  have hTN : T ⊆ N := inter_subset_left
  obtain ⟨lift, _, hvalue, hfaces⟩ := exists_hamiltonZero_box_coordinate_map phi
    hfirstGap hsecondGap hgap (hTN.trans hfirst) (hTN.trans hsecond) inter_subset_right
  have hFT : frontier T ⊆ T := (geometry.slabs side).1.closed.frontier_subset
  let inc : C(frontier T, T) := ContinuousMap.inclusion hFT
  have hmem (x : frontier T) : lift (inc x) ∈ frontier
      ((Icc (if side then v else u) (if side then u + p else v) ×ˢ Icc a b) ×ˢ
        Icc alpha beta) :=
    (hfaces (inc x)).mpr (geometry.frontier_box_faces hfront side x x.property)
  refine ⟨⟨fun x => ⟨lift (inc x), hmem x⟩,
    (lift.continuous.comp inc.continuous).subtype_mk _⟩, ?_⟩
  intro x
  exact hvalue (inc x)



theorem exists_hamiltonZero_second_slab_terminal_boundary_map
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 (Fin 3 → ℝ)}
    {R : Set X0} {chi eta : C(H0, H0)} {a b alpha beta u v : ℝ}
    (second : HamiltonZeroSecondPhaseGeometry e R chi a b)
    (hab : a < b) (hsecondWidth : b < a + p)
    (hfirstGap : beta < alpha + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap chi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hRfront : frontier R ⊆ hamiltonZeroCircleMap chi ⁻¹' {(alpha : C0), (beta : C0)})
    (hfirstEq : hamiltonZeroCircleMap eta = hamiltonZeroCircleMap chi)
    (hsecondEq : hamiltonZeroSecondCircleMap eta = hamiltonZeroSecondCircleMap chi)
    (side : Bool)
    (hfrontEq : EqOn (hamiltonZeroAmbientMap eta) (hamiltonZeroAmbientMap chi)
      (frontier (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b))))
    (third : HamiltonZeroThirdPhaseGeometry e (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) eta u v)
    (huv : u < v) (hthirdWidth : v < u + p) (thirdSide : Bool) :
    let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
    let T := N ∩ hamiltonZeroThirdCircleMap eta ⁻¹'
      AddCircle.closedIntervalArc p (if thirdSide then v else u) (if thirdSide then u + p else v)
    let Box := (Icc (if thirdSide then v else u) (if thirdSide then u + p else v) ×ˢ
      Icc (if side then b else a) (if side then a + p else b)) ×ˢ Icc alpha beta
    ∃ boundaryMap : C(frontier T, frontier Box), ∀ x : frontier T,
      Q0 (hamiltonZeroAmbientMap eta x) =
        (((((boundaryMap x : (ℝ × ℝ) × ℝ).1.1) : C0),
          (((boundaryMap x : (ℝ × ℝ) × ℝ).1.2) : C0)),
          (((boundaryMap x : (ℝ × ℝ) × ℝ).2) : C0)) := by
  have hgap : (if side then a + p else b) < (if side then b else a) + p := by
    cases side <;> dsimp <;> linarith
  apply exists_hamiltonZero_terminal_boundary_map third huv hthirdWidth hfirstGap hgap
  · rw [hfirstEq]
    exact inter_subset_left.trans hfirst
  · rw [hsecondEq]
    exact inter_subset_right
  · intro x hx
    have h := second.frontier_rectangle_edges hRfront side x hx
    have hq := congrArg Q0 (hfrontEq hx)
    have h1 : hamiltonZeroCircleMap eta x = hamiltonZeroCircleMap chi x :=
      congrArg Prod.snd hq
    have h2 : hamiltonZeroSecondCircleMap eta x = hamiltonZeroSecondCircleMap chi x :=
      congrArg (fun z => z.1.2) hq
    rw [h1, h2]
    rcases h with h | h
    · exact Or.inr (by simpa only [mem_insert_iff, mem_singleton_iff] using h)
    · exact Or.inl (by simpa only [mem_insert_iff, mem_singleton_iff] using h)

end PoincareConjecture.M76
