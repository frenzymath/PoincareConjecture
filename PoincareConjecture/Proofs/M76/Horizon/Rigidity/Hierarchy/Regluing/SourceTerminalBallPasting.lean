import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.SourceTerminalBallMaps
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.FiniteBallPasting









set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "E3" => ((ℝ × ℝ) × ℝ)
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem ChartwisePLMap.hamiltonZeroAmbientMap_univ
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3} {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi)) :
    ChartwisePLMap e d
      (⟨fun x : (univ : Set X0) => (⟨hamiltonZeroAmbientMap phi x, mem_univ _⟩ : (univ : Set X0)),
        by fun_prop⟩ : C((univ : Set X0), (univ : Set X0))) := by
  have transfer {S T : Set X0} (hS : S = univ) (hT : T = univ)
      (f : C(S, T)) (hf : ChartwisePLMap e d f)
      (hval : ∀ x : S, (f x : X0) = hamiltonZeroAmbientMap phi x) :
      ChartwisePLMap e d
        (⟨fun x : (univ : Set X0) => (⟨hamiltonZeroAmbientMap phi x, mem_univ _⟩ : (univ : Set X0)),
          by fun_prop⟩ : C((univ : Set X0), (univ : Set X0))) := by
    subst S
    subst T
    convert hf using 1
    apply ContinuousMap.ext
    intro x
    exact Subtype.ext (hval x).symm
  exact transfer hamiltonZeroDomain_eq_univ hamiltonZeroDomain_eq_univ _ hphi (fun _ => rfl)

theorem hamiltonZero_third_slabs_cover
    {N : Set X0} (phi : C(H0, H0)) {u v : ℝ} :
    (⋃ side : Bool, N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)) = N := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  apply le_antisymm (iUnion_subset fun _ => inter_subset_left)
  intro x hx
  let t := AddCircle.equivIco p u (hamiltonZeroThirdCircleMap phi x)
  have ht : ((t : ℝ) : C0) = hamiltonZeroThirdCircleMap phi x := AddCircle.coe_equivIco
  by_cases htv : (t : ℝ) ≤ v
  · exact mem_iUnion.mpr ⟨false, hx, t, ⟨t.property.1, htv⟩, ht⟩
  · exact mem_iUnion.mpr ⟨true, hx, t, ⟨(not_le.mp htv).le, t.property.2.le⟩, ht⟩

theorem hamiltonZero_third_slabs_separated
    {ι : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {N : Set X0} {phi : C(H0, H0)} {u v : ℝ}
    (hu : 0 < u) (huv : u < v) (hv : v < p)
    (geometry : HamiltonZeroThirdPhaseGeometry e N phi u v) :
    ∀ side : Bool,
      let T := fun side : Bool => N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
      T side ⊆ (interior (T (!side)))ᶜ := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let T := fun side : Bool => N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
    AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
  have h10 : T true ⊆ (interior (T false))ᶜ := by
    intro x hx hi
    have hxN : x ∈ interior N := interior_mono inter_subset_left hi
    exact (complementary_circle_slab_agrees_exterior (hamiltonZeroThirdCircleMap phi)
      hu huv (by simpa using hv) (geometry.slabs false).2.1 x hxN).mp hx hi
  have h01 : T false ⊆ (interior (T true))ᶜ := by
    have hreg : closure (interior (T false)) = T false :=
      (geometry.slabs false).1.closure_interior
    rw [← hreg]
    apply closure_minimal _ isOpen_interior.isClosed_compl
    intro x hx hi
    exact h10 (interior_subset hi) hx
  intro side
  cases side
  · exact h01
  · exact h10



theorem HamiltonZeroTerminalBallMapFamily.exists_paired_components
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    {N : Set X0} {phi : C(H0, H0)} {u v a b alpha beta : ℝ}
    (hu : 0 < u) (huv : u < v) (hv : v < p)
    (geometry : HamiltonZeroThirdPhaseGeometry e N phi u v)
    (family : ∀ side : Bool,
      HamiltonZeroTerminalBallMapFamily e d phi
        (N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
          AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v))
        (if side then v else u) (if side then u + p else v) a b alpha beta) :
    ∃ (n : Bool → ℕ) (P : (Σ side : Bool, Fin (n side)) → Set X0),
      (⋃ i, P i) = N ∧
      (∀ i, IsCompact (P i) ∧ PLDomain e (P i) ∧
        Nonempty (ChartwisePLBall e (P i) (frontier (P i))) ∧
        frontier (P i) = P i ∩ frontier (N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
          AddCircle.closedIntervalArc p (if i.1 then v else u) (if i.1 then u + p else v))) ∧
      (∀ i j, i ≠ j → P i ∩ P j ⊆ frontier (P i) ∩ frontier (P j)) ∧
      (∀ side : Bool, (⋃ i : Fin (n side), P ⟨side, i⟩) =
        N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
          AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)) ∧
      (∀ side : Bool, Pairwise (fun i j : Fin (n side) => Disjoint (P ⟨side, i⟩) (P ⟨side, j⟩))) ∧
      ∀ i, HamiltonZeroTerminalBallReplacement e d phi (P i)
        (if i.1 then v else u) (if i.1 then u + p else v) a b alpha beta := by
  classical
  choose n P hdis hcover hprops using family
  let T := fun side : Bool => N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
    AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
  have hPT (side : Bool) (i : Fin (n side)) : P side i ⊆ T side :=
    (subset_iUnion (P side) i).trans (hcover side).subset
  have hcoverAll : (⋃ i : Σ side : Bool, Fin (n side), P i.1 i.2) = N := by
    rw [iUnion_sigma]
    simp_rw [hcover]
    exact hamiltonZero_third_slabs_cover phi
  have hsep := hamiltonZero_third_slabs_separated hu huv hv geometry
  have hoverlap (i j : Σ side : Bool, Fin (n side)) (hne : i ≠ j) :
      P i.1 i.2 ∩ P j.1 j.2 ⊆ frontier (P i.1 i.2) := by
    intro x hx
    by_cases hs : i.1 = j.1
    · rcases i with ⟨s, i⟩
      rcases j with ⟨t, j⟩
      dsimp at hs
      subst t
      exact False.elim (disjoint_left.mp (hdis s (fun h => hne (by cases h; rfl))) hx.1 hx.2)
    · have hside : i.1 = !j.1 := Bool.eq_not_of_ne hs
      rw [(hprops i.1 i.2).2.1.closed.frontier_eq]
      refine ⟨hx.1, ?_⟩
      intro hint
      have hintT := interior_mono (hPT i.1 i.2) hint
      rw [hside] at hintT
      exact hsep j.1 (hPT j.1 j.2 hx.2) hintT
  refine ⟨n, fun i => P i.1 i.2, hcoverAll,
    fun i => ⟨(hprops i.1 i.2).1, (hprops i.1 i.2).2.1,
      (hprops i.1 i.2).2.2.1, (hprops i.1 i.2).2.2.2.1⟩,
    ?_, hcover, hdis, fun i => (hprops i.1 i.2).2.2.2.2.2⟩
  intro i j hne x hx
  exact ⟨hoverlap i j hne hx, hoverlap j i hne.symm ⟨hx.2, hx.1⟩⟩



def HamiltonZeroPastedTerminalBalls {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (phi : C(H0, H0)) (N : Set X0) (u v a b alpha beta : ℝ) : Prop :=
  ∃ (n : Bool → ℕ) (P : (Σ side : Bool, Fin (n side)) → Set X0)
    (H : ∀ i, ((Icc (if i.1 then v else u) (if i.1 then u + p else v) ×ˢ Icc a b) ×ˢ
      Icc alpha beta) ≃ₜ P i) (g : C(X0, X0)),
    (⋃ i, P i) = N ∧
    (∀ side : Bool, (⋃ i : Fin (n side), P ⟨side, i⟩) =
      N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)) ∧
    (∀ side : Bool, Pairwise (fun i j : Fin (n side) => Disjoint (P ⟨side, i⟩) (P ⟨side, j⟩))) ∧
    (∀ i, IsCompact (P i) ∧ PLDomain e (P i) ∧
      Nonempty (ChartwisePLBall e (P i) (frontier (P i))) ∧
      frontier (P i) = P i ∩ frontier (N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if i.1 then v else u) (if i.1 then u + p else v))) ∧
    (∀ i j, i ≠ j → P i ∩ P j ⊆ frontier (P i) ∩ frontier (P j)) ∧
    ChartwisePLMap e d
      (⟨fun x : (univ : Set X0) => (⟨g x, mem_univ _⟩ : (univ : Set X0)),
        by fun_prop⟩ : C((univ : Set X0), (univ : Set X0))) ∧
    (∀ i (x : P i), g x = hamiltonZeroBoxProjection ((H i).symm x)) ∧
    (∀ i (x : P i), (x : X0) ∈ interior (P i) ↔
      ((H i).symm x : E3) ∈ interior
        ((Icc (if i.1 then v else u) (if i.1 then u + p else v) ×ˢ Icc a b) ×ˢ Icc alpha beta)) ∧
    (∀ x ∉ N, g x = hamiltonZeroAmbientMap phi x) ∧
    ∃ G : (hamiltonZeroAmbientMap phi).HomotopyRel g (interior N)ᶜ,
      (∀ i t (x : P i), G (t, (x : X0)) ∈ hamiltonZeroBoxProjection ''
        ((Icc (if i.1 then v else u) (if i.1 then u + p else v) ×ˢ Icc a b) ×ˢ Icc alpha beta)) ∧
      ∀ t x, x ∈ ⋃ side : Bool, frontier (N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)) →
        G (t, x) = hamiltonZeroAmbientMap phi x

theorem HamiltonZeroTerminalBallMapFamily.exists_relative_pasting
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    {N : Set X0} {phi : C(H0, H0)} {u v a b alpha beta : ℝ}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (hu : 0 < u) (huv : u < v) (hv : v < p)
    (geometry : HamiltonZeroThirdPhaseGeometry e N phi u v)
    (family : ∀ side : Bool,
      HamiltonZeroTerminalBallMapFamily e d phi
        (N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
          AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v))
        (if side then v else u) (if side then u + p else v) a b alpha beta) :
    HamiltonZeroPastedTerminalBalls e d phi N u v a b alpha beta := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  obtain ⟨n, P, hwhole, hP, hoverlap, hcover, hdis, hreplace⟩ :=
    HamiltonZeroTerminalBallMapFamily.exists_paired_components hu huv hv geometry family
  choose H f hf hformula hrange hinterior hboundary J hJbox using hreplace
  obtain ⟨g, hg, hgin, hgout, G, hG⟩ := exists_finite_originalPL_relative_pasting
    (hamiltonZeroAmbientMap phi) hphi.hamiltonZeroAmbientMap_univ P
    (fun i => (hP i).1.isClosed) (fun i j hij => (hoverlap i j hij).trans inter_subset_left)
    f hf J
  have hPN (i) : P i ⊆ N := (subset_iUnion P i).trans hwhole.subset
  let GR : (hamiltonZeroAmbientMap phi).HomotopyRel g (interior N)ᶜ :=
    { G.toHomotopy with
      prop' := by
        intro t x hx
        apply G.prop t x
        intro hxP
        obtain ⟨i, hi⟩ := mem_iUnion.mp hxP
        exact hx (interior_mono (hPN i) hi) }
  have hsep := hamiltonZero_third_slabs_separated hu huv hv geometry
  refine ⟨n, P, H, g, hwhole, hcover, hdis, hP, hoverlap, hg,
    fun i x => (hgin i x).trans (hformula i x), hinterior,
    fun x hx => hgout x (by simpa only [hwhole] using hx), GR,
    fun i t x => (hG i t x) ▸ hJbox i t x, ?_⟩
  intro t x hx
  apply G.prop t x
  intro hxP
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxP
  obtain ⟨side, hxside⟩ := mem_iUnion.mp hx
  have hPi : x ∈ P i := interior_subset hi
  by_cases hside : side = i.1
  · subst side
    exact disjoint_left.mp disjoint_interior_frontier hi ((hP i).2.2.2.symm.subset ⟨hPi, hxside⟩)
  · have hside' : i.1 = !side := Bool.eq_not_of_ne (Ne.symm hside)
    have hPT : P i ⊆ N ∩ hamiltonZeroThirdCircleMap phi ⁻¹'
        AddCircle.closedIntervalArc p (if i.1 then v else u) (if i.1 then u + p else v) :=
      (subset_iUnion (fun j => P ⟨i.1, j⟩) i.2).trans (hcover i.1).subset
    have hiT := interior_mono hPT hi
    rw [hside'] at hiT
    exact hsep side ((geometry.slabs side).1.closed.frontier_subset hxside) hiT




theorem HamiltonZeroSourceBoundaryDiskData.exists_pasted_terminal_balls
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
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      ∃ (chi eta : C(H0, H0)),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 eta) ∧
        Nonempty (phi.HomotopyRel eta (latticeHandleBoundary (Fin 0) (Fin 3) L0)) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel
          (hamiltonZeroAmbientMap eta) (interior R)ᶜ) ∧
        R ⊆ hamiltonZeroCircleMap eta ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
        R ⊆ hamiltonZeroCircleMap chi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
        frontier R ⊆ hamiltonZeroCircleMap chi ⁻¹' {(alpha : C0), (beta : C0)} ∧
        HamiltonZeroSecondPhaseGeometry e R chi a b ∧
        ∀ s : Bool,
          let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
            AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)
          ∃ u ∈ Ioo (p / 4) (p / 3), ∃ v ∈ Ioo (2 * p / 3) (3 * p / 4),
            HamiltonZeroTerminalThirdPhaseData e N eta u v ∧
            ∃ psi : C(H0, H0),
              ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
              Nonempty (phi.HomotopyRel psi (latticeHandleBoundary (Fin 0) (Fin 3) L0)) ∧
              Nonempty ((ContinuousMap.id H0).HomotopyRel psi (latticeHandleBoundary (Fin 0) (Fin 3) L0)) ∧
              hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap eta ∧
              N ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
              N ⊆ hamiltonZeroSecondCircleMap psi ⁻¹'
                AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b) ∧
              Nonempty ((hamiltonZeroAmbientMap eta).HomotopyRel
                (hamiltonZeroAmbientMap psi) (interior N)ᶜ) ∧
              EqOn (hamiltonZeroAmbientMap psi) (hamiltonZeroAmbientMap chi) (frontier N) ∧
              IsLocallyInjective (fun x : (⋃ side : Bool, frontier
                (N ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
                  AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v))) =>
                hamiltonZeroAmbientMap psi x) ∧
              HamiltonZeroPastedTerminalBalls e d psi N u v
                (if s then b else a) (if s then a + p else b) alpha beta := by
  obtain ⟨a, ha, b, hb, chi, eta, hchi, heta, Heta, Geta, hReta, hRfirst,
    hRfront, geometry, hends⟩ :=
    data.exists_terminal_ball_maps hd hab hwidth hK hr c0 hc0 hi0 hzero g hg hproduct
  refine ⟨a, ha, b, hb, chi, eta, hchi, heta, Heta, Geta, hReta, hRfirst, hRfront, geometry, ?_⟩
  intro s N
  obtain ⟨u, hu, v, hv, terminal, psi, hpsi, Hpsi, Fpsi, hthird,
    hfirst, hsecond, Gpsi, hfixed, hunion, hlocal⟩ := hends s
  have hgeometry : HamiltonZeroThirdPhaseGeometry e N psi u v := by
    constructor
    · intro side
      dsimp only
      rw [hthird]
      exact terminal.geometry.slabs side
    · intro theta htheta
      rw [hthird]
      exact terminal.geometry.groups theta htheta
  have hpasted := HamiltonZeroTerminalBallMapFamily.exists_relative_pasting hpsi
    (show 0 < u by linarith [hu.1]) (show u < v by linarith [hu.2, hv.1])
    (show v < p by linarith [hv.2]) hgeometry
    (fun side => (hlocal side).2.2.2.2.2.2.2)
  exact ⟨u, hu, v, hv, terminal, psi, hpsi, Hpsi, Fpsi, hthird,
    hfirst, hsecond, Gpsi, hfixed, hunion, hpasted⟩

end PoincareConjecture.M76
