import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalLocalGluing
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalBoundaryMap
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalBoundaryCovering
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.TerminalSphericalFrontier








set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "E3" => ((ℝ × ℝ) × ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Ann" => PLAnnularStrip.squareAnnulus 8 1
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates



def HamiltonZeroTerminalSphericalCover {ι : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (phi : C(H0, H0))
    (T : Set X0) (u v a b alpha beta : ℝ) : Prop :=
  ∃ boundaryMap : C(frontier T, frontier ((Icc u v ×ˢ Icc a b) ×ˢ Icc alpha beta)),
    (∀ x : frontier T, Q0 (hamiltonZeroAmbientMap phi x) =
      (((((boundaryMap x : E3).1.1) : C0), (((boundaryMap x : E3).1.2) : C0)),
        (((boundaryMap x : E3).2) : C0))) ∧ IsCoveringMap boundaryMap ∧
    ∃ (n : ℕ) (S : Fin n → Set X0),
      Pairwise (fun i j => Disjoint (S i) (S j)) ∧ (⋃ i, S i) = frontier T ∧
      ∀ i, IsCompact (S i) ∧ (S i).Nonempty ∧
        Nonempty (ChartwisePLSphere e (S i)) ∧
        ∀ x ∈ S i, connectedComponentIn (frontier T) x = S i



theorem exists_hamiltonZero_terminal_spherical_coverings
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    {N : Set X0} (hN : IsClosed N) {eta psi : C(H0, H0)}
    (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
    {u v a b alpha beta : ℝ}
    (terminal : HamiltonZeroTerminalThirdPhaseData e N eta u v)
    (hthird : hamiltonZeroThirdCircleMap psi = hamiltonZeroThirdCircleMap eta)
    (huv : u < v) (hthirdWidth : v < u + p)
    (hab : a < b) (hsecondWidth : b < a + p)
    (halpha : alpha < beta) (hfirstWidth : beta < alpha + p)
    (hfirst : N ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : N ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hfront : ∀ x ∈ frontier N,
      (hamiltonZeroSecondCircleMap psi x = (a : C0) ∨
        hamiltonZeroSecondCircleMap psi x = (b : C0)) ∨
      (hamiltonZeroCircleMap psi x = (alpha : C0) ∨
        hamiltonZeroCircleMap psi x = (beta : C0)))
    (hinj : ∀ side : Bool,
      let T := N ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
        AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
      IsLocallyInjective (fun x : frontier T => hamiltonZeroAmbientMap psi x)) :
    ∀ side : Bool,
      let T := N ∩ hamiltonZeroThirdCircleMap psi ⁻¹'
        AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v)
      PLDomain e T ∧ IsCompact T ∧ T.Nonempty ∧ IsPLIrreducible e T ∧
        HamiltonZeroTerminalSphericalCover e psi T
          (if side then v else u) (if side then u + p else v) a b alpha beta := by
  have geometry : HamiltonZeroThirdPhaseGeometry e N psi u v := by
    constructor
    · intro side
      dsimp only
      rw [hthird]
      exact terminal.geometry.slabs side
    · intro theta htheta
      rw [hthird]
      exact terminal.geometry.groups theta htheta
  intro side T
  have hPL : PLDomain e T := (geometry.slabs side).1
  have hcompact : IsCompact T := isCompact_hamiltonZeroAmbient.of_isClosed_subset
    hPL.closed (subset_univ _)
  have hne : T.Nonempty := by
    obtain ⟨x, hxfront, hxphase⟩ := terminal.boundary (u : C0)
    obtain ⟨hSN, _⟩ := (geometry.slabs side).2.2 u (by simp)
    exact ⟨x, hSN ⟨hN.frontier_subset hxfront, by simpa only [hthird] using hxphase⟩⟩
  have hI : IsPLIrreducible e T := by
    simpa only [T, hthird] using terminal.irreducible side
  have hpos : (if side then v else u) < (if side then u + p else v) := by
    cases side <;> dsimp <;> linarith
  have hgap : (if side then u + p else v) < (if side then v else u) + p := by
    cases side <;> dsimp <;> linarith
  obtain ⟨boundaryMap, hvalue⟩ := exists_hamiltonZero_terminal_boundary_map geometry
    huv hthirdWidth hfirstWidth hsecondWidth hfirst hsecond hfront side
  have hc := isCoveringMap_hamiltonZero_terminal_boundary hd hpsi hPL hcompact hne
    hpos hab halpha hgap hsecondWidth hfirstWidth boundaryMap hvalue (hinj side)
  exact ⟨hPL, hcompact, hne, hI, boundaryMap, hvalue, hc,
    exists_hamiltonZero_terminal_spherical_frontier hd hpsi hPL hcompact hne
      hpos hab halpha hgap hsecondWidth hfirstWidth boundaryMap hvalue hc⟩




theorem HamiltonZeroSourceBoundaryDiskData.exists_terminal_spherical_coverings
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
                    (if s then b else a) (if s then a + p else b) alpha beta := by
  obtain ⟨a, ha, b, hb, chi, eta, hchi, heta, Heta, Geta, hReta, hRfirst, hRfront, geometry, hends⟩ :=
    data.exists_locally_injective_terminal_endpoints hab hwidth hK hr c0 hc0 hi0 hzero g hg hproduct
  refine ⟨a, ha, b, hb, chi, eta, hchi, heta, Heta, Geta, hReta, hRfirst, hRfront, geometry, ?_⟩
  intro s N
  obtain ⟨u, hu, v, hv, terminal, hgroups, psi, hpsi, Hpsi, Fpsi, hthird,
    hfirst, hsecond, Gpsi, hfixed, hunion, hlocal⟩ := hends s
  refine ⟨u, hu, v, hv, terminal, psi, hpsi, Hpsi, Fpsi, hthird,
    hfirst, hsecond, Gpsi, hfixed, hunion, ?_⟩
  have huv : u < v := by linarith [hu.2, hv.1]
  have huvWidth : v < u + p := by linarith [hu.1, hv.2]
  have hsecondPos : (if s then b else a) < (if s then a + p else b) := by
    cases s <;> dsimp <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hsecondWidth : (if s then a + p else b) < (if s then b else a) + p := by
    cases s <;> dsimp <;> linarith [ha.1, ha.2, hb.1, hb.2]
  have hfront : ∀ x ∈ frontier N,
      (hamiltonZeroSecondCircleMap psi x = ((if s then b else a : ℝ) : C0) ∨
        hamiltonZeroSecondCircleMap psi x = ((if s then a + p else b : ℝ) : C0)) ∨
      (hamiltonZeroCircleMap psi x = (alpha : C0) ∨
        hamiltonZeroCircleMap psi x = (beta : C0)) := by
    intro x hx
    have h := geometry.frontier_rectangle_edges hRfront s x hx
    have hq := congrArg Q0 (hfixed hx)
    have h1 : hamiltonZeroCircleMap psi x = hamiltonZeroCircleMap chi x :=
      congrArg Prod.snd hq
    have h2 : hamiltonZeroSecondCircleMap psi x = hamiltonZeroSecondCircleMap chi x :=
      congrArg (fun z => z.1.2) hq
    rw [h1, h2]
    rcases h with h | h
    · exact Or.inr (by simpa only [mem_insert_iff, mem_singleton_iff] using h)
    · exact Or.inl (by simpa only [mem_insert_iff, mem_singleton_iff] using h)
  have hconstructed := exists_hamiltonZero_terminal_spherical_coverings hd
    (geometry.slabs s).1.closed hpsi terminal hthird huv huvWidth hsecondPos hsecondWidth
    hab hwidth hfirst hsecond hfront hlocal
  intro side T
  obtain ⟨hT, hcompact, hne, hI, hspheres⟩ := hconstructed side
  refine ⟨hT, hcompact, hne, hI, ?_, hlocal side, hspheres⟩
  have htransport : ∀ M : Set X0,
      M = N ∩ hamiltonZeroThirdCircleMap eta ⁻¹'
        AddCircle.closedIntervalArc p (if side then v else u) (if side then u + p else v) →
      ∀ x : M, Subsingleton (FundamentalGroup M x) := by
    intro M hM
    subst M
    exact hgroups side
  exact htransport T (by dsimp only [T]; rw [hthird])

end PoincareConjecture.M76
