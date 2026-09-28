import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.SimultaneousSlabHierarchy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.TerminalGroups









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

theorem HamiltonZeroSupportedThirdRealization.slabs_pi1_subsingleton
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    {phi chi : C(H0, H0)} {R : Set X0} {a b : ℝ}
    (h : HamiltonZeroSupportedThirdRealization e d phi R chi a b)
    (heR : PLDomain e R)
    (hinjR : ∀ x : R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x))
    (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hreg : ∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e R phi (theta : C0))
    {cut alpha beta cut' u v : ℝ}
    (halpha : cut < alpha) (hbeta : beta < cut + p)
    (hu : cut' < u) (hv : v < cut' + p)
    (hfirst : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hsecond : R ⊆ hamiltonZeroSecondCircleMap phi ⁻¹' AddCircle.closedIntervalArc p u v) :
    ∀ side : Bool,
      let N := R ∩ hamiltonZeroThirdCircleMap chi ⁻¹'
        AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
      ∀ x : N, Subsingleton (FundamentalGroup N x) := by
  obtain ⟨psi, A, hA, hAR, hfixed, hfirstEq, hsecondEq, _, _, ⟨Fpsi⟩, _, terminal, heq⟩ := h
  have hboundary : (frontier R ∩ hamiltonZeroThirdCircleMap phi ⁻¹' {(a : C0)}).Nonempty := by
    obtain ⟨x, hx, hphase⟩ := terminal.boundary a
    refine ⟨x, hx, ?_⟩
    change hamiltonZeroThirdCircleMap phi x = (a : C0)
    have hxA : x ∉ A := fun h => hx.2 (hAR h)
    rw [hamiltonZeroThirdCircleMap_ambient, ← hfixed x hxA,
      ← hamiltonZeroThirdCircleMap_ambient]
    exact hphase
  have hfirstPsi : R ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta := by
    rw [hfirstEq]
    exact hfirst
  have hsecondPsi : R ⊆ hamiltonZeroSecondCircleMap psi ⁻¹' AddCircle.closedIntervalArc p u v := by
    rw [hsecondEq]
    exact hsecond
  have hgroups := hamiltonZero_terminal_third_slabs_pi1_subsingleton e phi psi Fpsi
    heR hinjR hA hAR hfixed ha hab hb hreg terminal.geometry hboundary
    halpha hbeta hu hv hfirstPsi hsecondPsi
  have hsets (T : Set C0) :
      R ∩ hamiltonZeroThirdCircleMap chi ⁻¹' T = R ∩ hamiltonZeroThirdCircleMap psi ⁻¹' T := by
    ext x
    by_cases hx : x ∈ R
    · have hthird : hamiltonZeroThirdCircleMap chi x = hamiltonZeroThirdCircleMap psi x := by
        rw [hamiltonZeroThirdCircleMap_ambient, heq hx, ← hamiltonZeroThirdCircleMap_ambient]
      simp only [mem_inter_iff, mem_preimage, hthird]
    · simp only [mem_inter_iff, hx, false_and]
  intro side
  dsimp only
  rw [hsets]
  exact hgroups side

theorem exists_hamiltonZero_source_simultaneous_terminal_trivial_groups
    {E ι κ : Type*} [TopologicalSpace E] [Zero E]
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F0 : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} (hI : IsPLIrreducible e R)
    {cut alpha beta : ℝ}
    (ha : cut < alpha) (hab : alpha < beta) (hb : beta < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p alpha beta)
    (hRfront : frontier R ⊆ hamiltonZeroCircleMap phi ⁻¹' {(alpha : C0), (beta : C0)})
    (hinjR : ∀ x : R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x))
    {K : Set E} (hK : IsCompact K) (hne : K.Nonempty) {r : ℝ} (hr : 0 < r)
    (c : E × ℝ → X0)
    (hc : ContinuousOn c (K ×ˢ Icc (-r) r))
    (hi : Topology.IsEmbedding (fun z : (K ×ˢ Icc (-r) r : Set (E × ℝ)) => c z))
    (ho : IsOpen (c '' (K ×ˢ Ioo (-r) r)))
    (hzero : c '' (K ×ˢ ({0} : Set ℝ)) = frontier R)
    (hside : ∀ z ∈ K ×ˢ Icc (-r) r, c z ∈ R ↔ 0 ≤ z.2)
    (g : C(K, C0 × C0)) (hg : IsCoveringMap g)
    (hproduct : ∀ x : K, ∀ t ∈ Icc (-r) r,
      ((hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates)
        (hamiltonZeroAmbientMap phi (c (x, t)))).1 = g x) :
    ∃ a ∈ Ioo (p / 4) (p / 3), ∃ b ∈ Ioo (2 * p / 3) (3 * p / 4),
      (∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroSecondCoordinateRegularity e R phi (theta : C0)) ∧
      ∃ (psi chi : C(H0, H0)) (A : Set X0),
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
        Nonempty (phi.HomotopyRel psi B0) ∧
        ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 chi) ∧
        Nonempty (phi.HomotopyRel chi B0) ∧
        Nonempty ((ContinuousMap.id H0).HomotopyRel chi B0) ∧
        Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap chi) (interior R)ᶜ) ∧
        IsCompact A ∧ A ⊆ interior R ∧
        (∀ x ∉ A, hamiltonZeroAmbientMap chi x = hamiltonZeroAmbientMap psi x) ∧
        hamiltonZeroCircleMap chi = hamiltonZeroCircleMap psi ∧
        hamiltonZeroSecondCircleMap chi = hamiltonZeroSecondCircleMap psi ∧
        R ⊆ hamiltonZeroCircleMap chi ⁻¹' AddCircle.closedIntervalArc p alpha beta ∧
        HamiltonZeroSecondPhaseGeometry e R chi a b ∧
        (∀ side : Bool, IsPLIrreducible e (R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
          AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b))) ∧
        (∀ side : Bool,
          let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
          ∀ x : N, Function.Injective
            (FundamentalGroup.map (ContinuousMap.inclusion (inter_subset_left : N ⊆ R)) x)) ∧
        (∀ theta : C0, (frontier R ∩ hamiltonZeroSecondCircleMap chi ⁻¹' {theta}).Nonempty) ∧
        ∀ side : Bool,
          let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
            AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
          ∃ u ∈ Ioo (p / 4) (p / 3), ∃ v ∈ Ioo (2 * p / 3) (3 * p / 4),
            (∀ t ∈ ({u, v} : Set ℝ), HamiltonZeroThirdCoordinateRegularity e N psi (t : C0)) ∧
            HamiltonZeroTerminalThirdPhaseData e N chi u v ∧
            HamiltonZeroSupportedThirdRealization e d psi N chi u v ∧
            ∀ thirdSide : Bool,
              let T := N ∩ hamiltonZeroThirdCircleMap chi ⁻¹'
                AddCircle.closedIntervalArc p (if thirdSide then v else u) (if thirdSide then u + p else v)
              ∀ x : T, Subsingleton (FundamentalGroup T x) := by
  obtain ⟨a, ha', b, hb', hreg, psi, chi, A, hpsi, Hpsi, hchi, Hchi, Fchi, Gchi,
      hA, hAR, hfixed, hfirstEq, hsecondEq, hRchi, geometry, hcuts, hinj, hboundary, terminal⟩ :=
    exists_hamiltonZero_source_simultaneous_terminal_hierarchies e d hd phi hphi F0 hI
      ha hab hb hR hRfront hinjR hK hne hr c hc hi ho hzero hside g hg hproduct
  refine ⟨a, ha', b, hb', hreg, psi, chi, A, hpsi, Hpsi, hchi, Hchi, Fchi, Gchi,
    hA, hAR, hfixed, hfirstEq, hsecondEq, hRchi, geometry, hcuts, hinj, hboundary, ?_⟩
  intro side
  let N := R ∩ hamiltonZeroSecondCircleMap chi ⁻¹'
    AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
  obtain ⟨u, hu, v, hv, hregThird, hterminal, hreal⟩ := terminal side
  refine ⟨u, hu, v, hv, hregThird, hterminal, hreal, ?_⟩
  have hinjN : ∀ x : N, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(N, X0)) x) := by
    let incl := ContinuousMap.inclusion (inter_subset_left : N ⊆ R)
    let ambient : C(R, X0) := ⟨Subtype.val, continuous_subtype_val⟩
    intro x
    change Function.Injective (FundamentalGroup.map (ambient.comp incl) x)
    rw [FundamentalGroup.map_comp]
    exact (hinjR (incl x)).comp (hinj side x)
  have hfirstN : N ⊆ hamiltonZeroCircleMap psi ⁻¹' AddCircle.closedIntervalArc p alpha beta := by
    rw [← hfirstEq]
    exact inter_subset_left.trans hRchi
  have hsecondN : N ⊆ hamiltonZeroSecondCircleMap psi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b) := by
    rw [← hsecondEq]
    exact inter_subset_right
  apply hreal.slabs_pi1_subsingleton (geometry.slabs side).1 hinjN
    (by linarith [hu.1]) (by linarith [hu.2, hv.1]) (by linarith [hv.2]) hregThird
    ha hb (cut' := if side then (a + b) / 2 else 0) ?_ ?_ hfirstN hsecondN
  · cases side <;> dsimp <;> linarith [ha'.1, ha'.2, hb'.1]
  · cases side <;> dsimp <;> linarith [ha'.2, hb'.1, hb'.2]

end PoincareConjecture.M76
