import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.BoundaryArcBall
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.SlabExcision
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.SecondPhaseGroups
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Topology.ExcisionInjection











set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

private instance : Fact (0 < p) := ⟨by norm_num⟩

theorem exists_hamiltonZero_closed_second_component_removal
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (hI : IsPLIrreducible e R)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hslabs : ∀ side : Bool,
      let N := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
        ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(a : C0)}) ∪
          (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(b : C0)})))
    (hgroups : ∀ s ∈ ({a, b} : Set ℝ),
      ∀ x : ↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(s : C0)}),
        Function.Injective (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(s : C0)}), X0)) x) ∧
        Function.Injective (FundamentalGroup.map (hamiltonZeroSecondPhaseCircleMap phi R s) x))
    {theta : ℝ} (htheta : theta ∈ ({a, b} : Set ℝ))
    {S : Set X0} (hSne : S.Nonempty)
    (hS : S ⊆ R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(theta : C0)})
    (hcomponent : ∀ x ∈ S, connectedComponentIn
      (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(theta : C0)}) x = S)
    (hrim : Disjoint S (frontier R)) :
    ∃ (psi : C(H0, H0)) (K : Set X0) (G : C(unitInterval × X0, X0)),
      IsCompact K ∧ K ⊆ interior R ∧ S ⊆ interior K ∧
      (∃ SK : Set X0, Nonempty (ChartwisePLBall e K SK)) ∧
      (∀ x, G (0, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ x, G (1, x) = hamiltonZeroAmbientMap psi x) ∧
      (∀ (t : unitInterval) (x : X0), x ∉ interior K →
        G (t, x) = hamiltonZeroAmbientMap phi x) ∧
      (∀ (t : unitInterval) (x : X0), (Q0 (G (t, x))).2 = hamiltonZeroCircleMap phi x) ∧
      (∀ (t : unitInterval) (x : X0),
        (Q0 (G (t, x))).1.1 = (Q0 (hamiltonZeroAmbientMap phi x)).1.1) ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty (phi.HomotopyRel psi B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel
        (hamiltonZeroAmbientMap psi) (interior R)ᶜ) ∧
      hamiltonZeroCircleMap psi = hamiltonZeroCircleMap phi ∧
      Disjoint S (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(theta : C0)}) ∧
      Disjoint ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(a : C0)}) ∪
        (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(b : C0)})) (frontier K) ∧
      (∀ s ∈ ({a, b} : Set ℝ),
        R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(s : C0)} =
          (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(s : C0)}) \ K) ∧
      (∀ side : Bool,
        let N := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹'
          AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
        PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
          ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(a : C0)}) ∪
            (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(b : C0)})) ∧
        ∀ s ∈ ({a, b} : Set ℝ),
          ∃ hSN : R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(s : C0)} ⊆ N,
            ∀ x, Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSN) x)) ∧
      ∀ s ∈ ({a, b} : Set ℝ),
        let P := R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(s : C0)}
        ∃ hsub : P ⊆ R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(s : C0)},
          (∀ x, Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hsub) x)) ∧
          ∀ x : P,
            Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion inter_subset_left) x) ∧
            Function.Injective (FundamentalGroup.map
              (⟨Subtype.val, continuous_subtype_val⟩ : C(P, X0)) x) ∧
            Function.Injective (FundamentalGroup.map (hamiltonZeroSecondPhaseCircleMap psi R s) x) ∧
            IsCyclic (FundamentalGroup P x) := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  have hR : IsCompact R :=
    isCompact_hamiltonZeroAmbient.of_isClosed_subset hI.1.closed (subset_univ _)
  have haI : a ∈ Ico (0 : ℝ) (0 + p) := ⟨ha.le, by linarith⟩
  have hbI : b ∈ Ico (0 : ℝ) (0 + p) := ⟨(ha.trans hab).le, by linarith⟩
  obtain ⟨other, hpair, hfrontTheta⟩ : ∃ other : C0,
      (((theta : C0) = (a : C0) ∧ other = (b : C0)) ∨
        ((theta : C0) = (b : C0) ∧ other = (a : C0))) ∧
      frontier (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) =
        ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) ∩
          frontier R) ∪
          ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(theta : C0)}) ∪
            (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {other})) := by
    rcases htheta with rfl | rfl
    · exact ⟨(b : C0), Or.inl ⟨rfl, rfl⟩, (hslabs false).2⟩
    · exact ⟨(a : C0), Or.inr ⟨rfl, rfl⟩, by
        simpa only [Bool.false_eq_true, if_false, union_comm] using (hslabs false).2⟩
  have hcyclic (x : ↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(theta : C0)})) :
      IsCyclic (FundamentalGroup ↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(theta : C0)}) x) := by
    let : IsCyclic (FundamentalGroup C0 (hamiltonZeroSecondPhaseCircleMap phi R theta x)) :=
      HamiltonIntervalTorus.circleFundamentalGroup_isCyclic p (by norm_num) _
    exact isCyclic_of_injective
      (FundamentalGroup.map (hamiltonZeroSecondPhaseCircleMap phi R theta) x)
      (hgroups theta htheta x).2
  obtain ⟨D, K, SK, _, ⟨ball⟩, _, hK, hKR, _, hSK, _, _, lower, upper,
      hlower, horder, hupper, hnota, hnotb, hboundary⟩ :=
    exists_hamiltonZero_closed_second_component_boundary_arc_ball e phi hI ha hab hb hpair
      (hslabs false).1 hfrontTheta hcyclic hSne hS hcomponent hrim isOpen_univ (subset_univ S)
  have hnotarc (s : ℝ) (hs : s ∈ ({a, b} : Set ℝ)) :
      (s : C0) ∉ AddCircle.closedIntervalArc p lower upper := by
    rintro ⟨z, hz, hzs⟩
    have hzI : z ∈ Ico (0 : ℝ) (0 + p) :=
      ⟨(hlower.trans_le hz.1).le, by linarith [hz.2]⟩
    rcases hs with rfl | rfl
    · exact hnota (((AddCircle.coe_eq_coe_iff_of_mem_Ico hzI haI).mp hzs) ▸ hz)
    · exact hnotb (((AddCircle.coe_eq_coe_iff_of_mem_Ico hzI hbI).mp hzs) ▸ hz)
  obtain ⟨psi, G, hzero, hone, hfixed, hnormal, hcoord, hpsi, Hpsi, Fpsi, hq,
      hrange, hphases⟩ := hphi.exists_hamiltonZero_original_ball_arc_removal hd F ball
    lower upper hlower horder hupper
    (by intro x hx; rw [← hboundary]; exact mem_image_of_mem _ hx)
  have hfixedK (x : X0) (hx : x ∉ K) :
      hamiltonZeroAmbientMap psi x = hamiltonZeroAmbientMap phi x :=
    (hone x).symm.trans (hfixed 1 x (fun hi => hx (interior_subset hi)))
  have havoid (x : X0) (hx : x ∈ K) :
      hamiltonZeroSecondCircleMap psi x ≠ (a : C0) ∧
        hamiltonZeroSecondCircleMap psi x ≠ (b : C0) :=
    ⟨fun h => hnotarc a (Or.inl rfl) (h ▸ hrange x hx),
      fun h => hnotarc b (Or.inr rfl) (h ▸ hrange x hx)⟩
  have hretained (s : ℝ) (hs : s ∈ ({a, b} : Set ℝ)) :
      R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(s : C0)} =
        (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(s : C0)}) \ K := by
    rw [hphases (s : C0) (hnotarc s hs)]
    ext x
    simp only [mem_inter_iff, mem_sdiff]
    tauto
  have hfrontK (s : ℝ) (hs : s ∈ ({a, b} : Set ℝ)) :
      Disjoint (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(s : C0)}) (frontier K) := by
    apply disjoint_left.mpr
    intro x hx hxK
    rw [ball.frontier_eq] at hxK
    have hxarc : hamiltonZeroSecondCircleMap phi x ∈ AddCircle.closedIntervalArc p lower upper := by
      rw [← hboundary]
      exact mem_image_of_mem _ hxK
    exact hnotarc s hs (hx.2 ▸ hxarc)
  have hinjNew (s : ℝ) (hs : s ∈ ({a, b} : Set ℝ)) :
      ∀ x : ↥(R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(s : C0)}),
        Function.Injective (FundamentalGroup.map
          (⟨Subtype.val, continuous_subtype_val⟩ :
            C(↥(R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(s : C0)}), X0)) x) := by
    rw [hretained s hs]
    exact FundamentalGroup.ambient_injective_sdiff_of_disjoint_frontier
      hK.isClosed (hfrontK s hs) (fun x => (hgroups s hs x).1)
  have hthrough {P T : Set X0} (hPT : P ⊆ T)
      (hinj : ∀ x : P, Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ : C(P, X0)) x)) :
      ∀ x : P, Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hPT) x) := by
    intro x
    have heq : (⟨Subtype.val, continuous_subtype_val⟩ : C(P, X0)) =
        (⟨Subtype.val, continuous_subtype_val⟩ : C(T, X0)).comp
          (ContinuousMap.inclusion hPT) := rfl
    have h := hinj x
    rw [heq, FundamentalGroup.map_comp] at h
    exact Function.Injective.of_comp h
  have hnewslabs := plDomains_hamiltonZero_second_slabs_of_supported_phase_avoidance phi psi
    hR ha hab (by simpa only [zero_add] using hb) hslabs hK.isClosed hKR hfixedK havoid
  refine ⟨psi, K, G, hK, hKR, hSK, ⟨SK, ⟨ball⟩⟩, hzero, hone, hfixed, hnormal, hcoord,
    hpsi, Hpsi, Fpsi, ?_, hq, ?_, ?_, hretained, ?_, ?_⟩
  · exact ⟨{
      toFun := G
      continuous_toFun := G.continuous
      map_zero_left := hzero
      map_one_left := hone
      prop' := by
        intro t x hx
        exact hfixed t x (fun hi => hx (hKR (interior_subset hi))) }⟩
  · rw [hretained theta htheta]
    exact disjoint_left.mpr fun x hx hy => hy.2 (interior_subset (hSK hx))
  · exact disjoint_union_left.mpr ⟨hfrontK a (Or.inl rfl), hfrontK b (Or.inr rfl)⟩
  · intro side
    obtain ⟨he, hf⟩ := hnewslabs side
    refine ⟨he, hf, ?_⟩
    intro s hs
    have hSN : R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(s : C0)} ⊆
        R ∩ hamiltonZeroSecondCircleMap psi ⁻¹'
          AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b) := by
      intro x hx
      apply he.closed.frontier_subset
      rw [hf]
      apply Or.inr
      rcases hs with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
    exact ⟨hSN, hthrough hSN (hinjNew s hs)⟩
  · intro s hs
    have hsub : R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(s : C0)} ⊆
        R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(s : C0)} := by
      rw [hretained s hs]
      exact sdiff_subset
    have hi := hthrough hsub (hinjNew s hs)
    refine ⟨hsub, hi, fun x => ⟨hthrough inter_subset_left (hinjNew s hs) x,
      hinjNew s hs x, ?_⟩⟩
    have hfactor : hamiltonZeroSecondPhaseCircleMap psi R s =
        (hamiltonZeroSecondPhaseCircleMap phi R s).comp (ContinuousMap.inclusion hsub) := by
      apply ContinuousMap.ext
      intro y
      rw [hamiltonZeroSecondPhaseCircleMap_ambient, ContinuousMap.comp_apply,
        hamiltonZeroSecondPhaseCircleMap_ambient, ← hone]
      exact hcoord 1 y
    have hcircle : Function.Injective
        (FundamentalGroup.map (hamiltonZeroSecondPhaseCircleMap psi R s) x) := by
      rw [hfactor, FundamentalGroup.map_comp]
      exact ((hgroups s hs (ContinuousMap.inclusion hsub x)).2).comp (hi x)
    let : IsCyclic (FundamentalGroup C0 (hamiltonZeroSecondPhaseCircleMap psi R s x)) :=
      HamiltonIntervalTorus.circleFundamentalGroup_isCyclic p (by norm_num) _
    exact ⟨hcircle, isCyclic_of_injective
      (FundamentalGroup.map (hamiltonZeroSecondPhaseCircleMap psi R s) x) hcircle⟩

end PoincareConjecture.M76
