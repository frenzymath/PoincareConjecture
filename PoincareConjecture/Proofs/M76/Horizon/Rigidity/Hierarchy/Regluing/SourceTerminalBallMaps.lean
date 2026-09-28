import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.SourceTerminalCoverings
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalSourceBalls
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalBallHomotopy









set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "E3" => ((ℝ × ℝ) × ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates



def HamiltonZeroTerminalBallReplacement {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (phi : C(H0, H0)) (P : Set X0) (u v a b alpha beta : ℝ) : Prop :=
      ∃ (H : ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta) ≃ₜ P) (f : C(P, X0)),
        ChartwisePLMap e d
          (⟨fun x => (⟨f x, mem_univ _⟩ : (univ : Set X0)),
            f.continuous.subtype_mk _⟩ : C(P, (univ : Set X0))) ∧
        (∀ x, f x = hamiltonZeroBoxProjection (H.symm x)) ∧
        (range f = hamiltonZeroBoxProjection '' ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)) ∧
        (∀ x : P, (x : X0) ∈ interior P ↔
          (H.symm x : E3) ∈ interior ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)) ∧
        (∀ x : P, (x : X0) ∈ frontier P → f x = hamiltonZeroAmbientMap phi x) ∧
        ∃ F : (⟨fun x : P => hamiltonZeroAmbientMap phi x,
            (hamiltonZeroAmbientMap phi).continuous.comp continuous_subtype_val⟩ : C(P, X0)).HomotopyRel
            f ((Subtype.val : P → X0) ⁻¹' frontier P),
          ∀ t x, F (t, x) ∈ hamiltonZeroBoxProjection ''
            ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)



def HamiltonZeroTerminalBallMapFamily {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (phi : C(H0, H0)) (T : Set X0) (u v a b alpha beta : ℝ) : Prop :=
  ∃ (n : ℕ) (P : Fin n → Set X0),
    Pairwise (fun i j => Disjoint (P i) (P j)) ∧ (⋃ i, P i) = T ∧
    ∀ i, IsCompact (P i) ∧ PLDomain e (P i) ∧
      Nonempty (ChartwisePLBall e (P i) (frontier (P i))) ∧
      frontier (P i) = P i ∩ frontier T ∧
      (∀ x ∈ P i, connectedComponentIn T x = P i) ∧
      HamiltonZeroTerminalBallReplacement e d phi (P i) u v a b alpha beta



theorem HamiltonZeroTerminalSphericalCover.exists_ball_map_family
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {phi : C(H0, H0)}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {T : Set X0} (hI : IsPLIrreducible e T) (hT : IsCompact T) (hne : T.Nonempty)
    {u v a b alpha beta : ℝ} (huv : u < v) (hab : a < b) (halpha : alpha < beta)
    (hthird : v < u + p) (hsecond : b < a + p) (hfirst : beta < alpha + p)
    (hTfirst : T ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hTsecond : T ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hTthird : T ⊆ hamiltonZeroThirdCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v)
    (cover : HamiltonZeroTerminalSphericalCover e phi T u v a b alpha beta) :
    HamiltonZeroTerminalBallMapFamily e d phi T u v a b alpha beta := by
  classical
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  obtain ⟨boundaryMap, hvalue, hc, _⟩ := cover
  obtain ⟨_, n, P, hdis, hwhole, hP⟩ := exists_hamiltonZero_terminal_source_balls
    hd hphi F hI hT hne huv hab halpha hthird hsecond hfirst hTfirst boundaryMap hvalue hc
  have hPT (i : Fin n) : P i ⊆ T := (subset_iUnion P i).trans hwhole.subset
  refine ⟨n, P, hdis, hwhole, ?_⟩
  intro i
  obtain ⟨hcompact, ⟨ball⟩, hcomponent⟩ := hP i
  let x0 : P i := ball.parametrization ⟨0, by simp⟩
  have heq : connectedComponentIn T (x0 : X0) = P i := hcomponent x0 x0.property
  have hPL : PLDomain e (P i) := heq ▸ (hI.connectedComponentIn hT (hPT i x0.property)).1
  have hfront : frontier (P i) = P i ∩ frontier T := by
    rw [← heq]
    exact hI.1.frontier_connectedComponentIn_of_compact hT (hPT i x0.property)
  have hPF : frontier (P i) ⊆ frontier T := hfront.subset.trans inter_subset_right
  let inc : C(frontier (P i), frontier T) := ContinuousMap.inclusion hPF
  have hclopen : IsClopen ((Subtype.val : frontier T → X0) ⁻¹' P i) := by
    have h := Poincare.Topology.isClopen_part_of_finite_closed_partition
      P (fun k => (hP k).1.isClosed) hdis i
    let j : frontier T → (⋃ k, P k) := fun x =>
      ⟨x, hwhole.symm.subset (hI.1.closed.frontier_subset x.property)⟩
    exact h.preimage (show Continuous j from continuous_subtype_val.subtype_mk _)
  have hrange : range inc = (Subtype.val : frontier T → X0) ⁻¹' P i := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (hfront.subset y.property).1
    · intro hx
      exact ⟨⟨x, hfront.symm.subset ⟨hx, x.property⟩⟩, Subtype.ext rfl⟩
  have hi : IsOpenEmbedding inc :=
    ⟨IsEmbedding.inclusion hPF, hrange.symm ▸ hclopen.isOpen⟩
  let localMap : C(frontier (P i), frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)) :=
    boundaryMap.comp inc
  let : CompactSpace (frontier (P i)) := isCompact_iff_compactSpace.mp
    (hcompact.of_isClosed_subset isClosed_frontier hPL.closed.frontier_subset)
  have hlocal : IsCoveringMap localMap := isLocalHomeomorph_iff_isCoveringMap.mp
    (hc.isLocalHomeomorph.comp hi.isLocalHomeomorph)
  obtain ⟨H, f, hf, hformula, hfRange, hinterior, G, hG⟩ :=
    ball.exists_terminalBox_relative_replacement hPL hd hphi huv hab halpha
      hthird hsecond hfirst ((hPT i).trans hTfirst) ((hPT i).trans hTsecond)
      ((hPT i).trans hTthird) localMap (fun x => hvalue (inc x)) hlocal
  exact ⟨hcompact, hPL, ⟨ball⟩, hfront, hcomponent,
    H, f, hf, hformula, hfRange, hinterior,
    fun x hx => (G.fst_eq_snd hx).symm, G, hG⟩




theorem HamiltonZeroSourceBoundaryDiskData.exists_terminal_ball_maps
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
        Nonempty (phi.HomotopyRel eta B0) ∧
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
              Nonempty (phi.HomotopyRel psi B0) ∧
              Nonempty ((ContinuousMap.id H0).HomotopyRel psi B0) ∧
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
              ∀ side : Bool,
                let T := N ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
                  AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
                PLDomain e T ∧ IsCompact T ∧ T.Nonempty ∧ IsPLIrreducible e T ∧
                  (∀ x : T, Subsingleton (FundamentalGroup T x)) ∧
                  IsLocallyInjective (fun x : frontier T => hamiltonZeroAmbientMap psi x) ∧
                  HamiltonZeroTerminalSphericalCover e psi T
                    (if side then v else u) (if side then u + p else v)
                    (if s then b else a) (if s then a + p else b) alpha beta ∧
                  HamiltonZeroTerminalBallMapFamily e d psi T
                    (if side then v else u) (if side then u + p else v)
                    (if s then b else a) (if s then a + p else b) alpha beta := by
  obtain ⟨a, ha, b, hb, chi, eta, hchi, heta, Heta, Geta, hReta, hRfirst, hRfront, geometry, hends⟩ :=
    data.exists_terminal_spherical_coverings hd hab hwidth hK hr c0 hc0 hi0 hzero g hg hproduct
  refine ⟨a, ha, b, hb, chi, eta, hchi, heta, Heta, Geta, hReta, hRfirst, hRfront, geometry, ?_⟩
  intro s N
  obtain ⟨u, hu, v, hv, terminal, psi, hpsi, Hpsi, ⟨Fpsi⟩, hthird,
    hfirst, hsecond, Gpsi, hfixed, hunion, hlocal⟩ := hends s
  refine ⟨u, hu, v, hv, terminal, psi, hpsi, Hpsi, ⟨Fpsi⟩, hthird,
    hfirst, hsecond, Gpsi, hfixed, hunion, ?_⟩
  intro side T
  obtain ⟨hT, hcompact, hne, hI, hgroups, hinj, hcover⟩ := hlocal side
  have hthirdPos : (if side then v else u) < (if side then u + p else v) := by
    cases side <;> dsimp <;> linarith [hu.1, hu.2, hv.1, hv.2]
  have hthirdWidth : (if side then u + p else v) < (if side then v else u) + p := by
    cases side <;> dsimp <;> linarith [hu.1, hu.2, hv.1, hv.2]
  have hsecondPos : (if s then b else a) < (if s then a + p else b) := by
    cases s <;> dsimp <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hsecondWidth : (if s then a + p else b) < (if s then b else a) + p := by
    cases s <;> dsimp <;> linarith [ha.1, ha.2, hb.1, hb.2]
  exact ⟨hT, hcompact, hne, hI, hgroups, hinj, hcover,
    hcover.exists_ball_map_family hd hpsi Fpsi hI hcompact hne hthirdPos hsecondPos hab
      hthirdWidth hsecondWidth hwidth (inter_subset_left.trans hfirst)
      (inter_subset_left.trans hsecond) inter_subset_right⟩

end PoincareConjecture.M76
