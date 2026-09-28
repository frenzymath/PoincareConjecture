import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.Removal
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Spheres.FinitePhaseCover
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Spheres.Iteration.PhaseFamily









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


structure HamiltonZeroSecondPhaseGeometry {ι : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (R : Set X0) (phi : C(H0, H0)) (a b : ℝ) : Prop where
  slabs : ∀ side : Bool,
    let N := R ∩ hamiltonZeroSecondCircleMap phi ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
    PLDomain e N ∧ frontier N = (N ∩ frontier R) ∪
      ((R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(a : C0)}) ∪
        (R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(b : C0)})) ∧
    ∀ s ∈ ({a, b} : Set ℝ),
      ∃ hSN : R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(s : C0)} ⊆ N,
        ∀ x, Function.Injective (FundamentalGroup.map (ContinuousMap.inclusion hSN) x)
  groups : ∀ s ∈ ({a, b} : Set ℝ),
    ∀ x : ↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(s : C0)}),
      Function.Injective (FundamentalGroup.map
        (⟨Subtype.val, continuous_subtype_val⟩ :
          C(↥(R ∩ hamiltonZeroSecondCircleMap phi ⁻¹' {(s : C0)}), X0)) x) ∧
      Function.Injective (FundamentalGroup.map (hamiltonZeroSecondPhaseCircleMap phi R s) x)

private def EliminationCandidate {ι κ : Type*}
    (e : ι → OpenPartialHomeomorph X0 V3) (d : κ → OpenPartialHomeomorph X0 V3)
    (R : Set X0) (phi : C(H0, H0)) (a b : ℝ) (n : ℕ) : Prop :=
  ∃ (eta : C(H0, H0)) (K : Set X0), IsCompact K ∧ K ⊆ interior R ∧
    (∀ x ∉ K, hamiltonZeroAmbientMap eta x = hamiltonZeroAmbientMap phi x) ∧
    hamiltonZeroCircleMap eta = hamiltonZeroCircleMap phi ∧
    ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 eta) ∧
    Nonempty (phi.HomotopyRel eta B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel eta B0) ∧
    Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap eta) (interior R)ᶜ) ∧
    HamiltonZeroSecondPhaseGeometry e R eta a b ∧
    ∃ M : Fin n → Set X0,
      (⋃ i, M i) = (R ∩ hamiltonZeroSecondCircleMap eta ⁻¹' {(a : C0)}) ∪
        (R ∩ hamiltonZeroSecondCircleMap eta ⁻¹' {(b : C0)}) ∧
      ∀ i, IsConnected (M i)

theorem exists_hamiltonZero_second_phases_without_closed_components
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3)
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi0 phi : C(H0, H0))
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 phi))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R A0 : Set X0} (hI : IsPLIrreducible e R)
    (hA0 : IsCompact A0) (hA0R : A0 ⊆ interior R)
    (hfixed0 : ∀ x ∉ A0, hamiltonZeroAmbientMap phi x = hamiltonZeroAmbientMap phi0 x)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (hreg : ∀ theta ∈ ({a, b} : Set ℝ), HamiltonZeroSecondCoordinateRegularity e R phi0 (theta : C0))
    (geometry : HamiltonZeroSecondPhaseGeometry e R phi a b) :
    ∃ (eta : C(H0, H0)) (K : Set X0), IsCompact K ∧ K ⊆ interior R ∧
      (∀ x ∉ K, hamiltonZeroAmbientMap eta x = hamiltonZeroAmbientMap phi x) ∧
      hamiltonZeroCircleMap eta = hamiltonZeroCircleMap phi ∧
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 eta) ∧
      Nonempty (phi.HomotopyRel eta B0) ∧ Nonempty ((ContinuousMap.id H0).HomotopyRel eta B0) ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel (hamiltonZeroAmbientMap eta) (interior R)ᶜ) ∧
      HamiltonZeroSecondPhaseGeometry e R eta a b ∧
      ∀ theta ∈ ({a, b} : Set ℝ), ∀ S : Set X0, S.Nonempty →
        S ⊆ R ∩ hamiltonZeroSecondCircleMap eta ⁻¹' {(theta : C0)} →
        (∀ x ∈ S, connectedComponentIn
          (R ∩ hamiltonZeroSecondCircleMap eta ⁻¹' {(theta : C0)}) x = S) →
        (S ∩ frontier R).Nonempty := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  have hne : (a : C0) ≠ (b : C0) := by
    intro h
    exact hab.ne ((AddCircle.coe_eq_coe_iff_of_mem_Ico
      (show a ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)
      (show b ∈ Ico (0 : ℝ) (0 + p) by constructor <;> linarith)).mp h)
  obtain ⟨n0, M0, hM0, hc0⟩ := exists_hamiltonZero_compressed_paired_phase_connected_cover
    e phi0 phi hI.1 hA0 hA0R hfixed0 hne hreg
      (geometry.slabs false).1 (geometry.slabs false).2.1
  have hex : ∃ n, EliminationCandidate e d R phi a b n := by
    refine ⟨n0, phi, ∅, isCompact_empty, empty_subset _, fun _ _ => rfl, rfl,
      hphi, ⟨ContinuousMap.HomotopyRel.refl phi B0⟩, ⟨F⟩,
      ⟨ContinuousMap.HomotopyRel.refl _ _⟩, geometry, M0, hM0, hc0⟩
  obtain ⟨eta, K, hK, hKR, hfixed, hnormal, heta, ⟨Heta⟩, ⟨Feta⟩, ⟨Hext⟩,
      geom, M, hM, hcM⟩ := Nat.find_spec hex
  refine ⟨eta, K, hK, hKR, hfixed, hnormal, heta, ⟨Heta⟩, ⟨Feta⟩, ⟨Hext⟩, geom, ?_⟩
  intro theta htheta S hSne hS hcomponent
  by_contra hrim
  have hdis : Disjoint S (frontier R) :=
    disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hrim)
  obtain ⟨psi, K', G, hK', hK'R, hSK', _, hzero, hone, hfixed', _, _, hpsi,
      ⟨Hpsi⟩, ⟨Fpsi⟩, ⟨Hext'⟩, hnormal', _, hfrontK', hphases, hslabs, hgroups⟩ :=
    exists_hamiltonZero_closed_second_component_removal e d hd eta heta Feta hI ha hab hb
      (fun side => ⟨(geom.slabs side).1, (geom.slabs side).2.1⟩)
      geom.groups htheta hSne hS hcomponent hdis
  have hmeet : (((R ∩ hamiltonZeroSecondCircleMap eta ⁻¹' {(a : C0)}) ∪
      (R ∩ hamiltonZeroSecondCircleMap eta ⁻¹' {(b : C0)})) ∩ K').Nonempty := by
    obtain ⟨x, hx⟩ := hSne
    refine ⟨x, ?_, interior_subset (hSK' hx)⟩
    rcases htheta with rfl | rfl
    · exact Or.inl (hS hx)
    · exact Or.inr (hS hx)
  obtain ⟨m, U, hmn, hU, hcU⟩ := HamiltonIntervalTorus.exists_finite_connected_cover_decrease
    M hM hcM hK'.isClosed hfrontK' hmeet
  have hphaseUnion : ((R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(a : C0)}) ∪
      (R ∩ hamiltonZeroSecondCircleMap psi ⁻¹' {(b : C0)})) =
      ((R ∩ hamiltonZeroSecondCircleMap eta ⁻¹' {(a : C0)}) ∪
        (R ∩ hamiltonZeroSecondCircleMap eta ⁻¹' {(b : C0)})) \ K' := by
    rw [hphases a (Or.inl rfl), hphases b (Or.inr rfl), union_sdiff_distrib]
  have hnew : EliminationCandidate e d R phi a b m := by
    refine ⟨psi, K ∪ K', hK.union hK', union_subset hKR hK'R, ?_,
      hnormal'.trans hnormal, hpsi, ⟨Heta.trans Hpsi⟩, ⟨Fpsi⟩,
      ⟨Hext.trans Hext'⟩, ⟨hslabs, ?_⟩, U, hU.trans hphaseUnion.symm, hcU⟩
    · intro x hx
      exact ((hone x).symm.trans (hfixed' 1 x
        (fun hi => hx (Or.inr (interior_subset hi))))).trans
          (hfixed x (fun h => hx (Or.inl h)))
    · intro s hs x
      obtain ⟨_, _, hnewgroups⟩ := hgroups s hs
      exact ⟨(hnewgroups x).2.1, (hnewgroups x).2.2.1⟩
  exact (Nat.not_lt_of_ge (Nat.find_min' hex hnew)) hmn

end PoincareConjecture.M76
