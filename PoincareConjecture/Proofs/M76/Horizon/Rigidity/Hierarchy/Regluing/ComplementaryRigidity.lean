import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.PairedSlabGluing
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.LocalRigidity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Disks.Maps.SimultaneousTerminalDiskInstallation









set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p

theorem exists_hamiltonZero_rigidity_of_complementary_endpoints
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (phase : C(X0, C0)) (hopen : IsOpenMap phase)
    {a b : ℝ} (hab : a < b) (hw : b < a + p) :
    let q := phase.comp (hamiltonZeroAmbientMap phi)
    let N := fun side : Bool => (univ : Set X0) ∩ q ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)
    (∀ s, PLDomain e (N s)) →
    (∀ s, frontier (N s) = q ⁻¹' {(a : C0), (b : C0)}) →
    (∀ s, ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel
        (hamiltonZeroAmbientMap psi) (interior (N s))ᶜ) ∧
      MapsTo (phase ∘ hamiltonZeroAmbientMap psi) (N s)
        (AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)) ∧
      IsLocallyInjective (fun x : N s => hamiltonZeroAmbientMap psi x)) →
    ∃ g : H0 ≃ₜ H0,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 0) (Fin 3) L0 g) ∧
      Nonempty (phi.HomotopyRel ⟨g, g.continuous⟩ B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel ⟨g, g.continuous⟩ B0) := by
  classical
  let : Fact (0 < p) := ⟨by norm_num⟩
  intro q N he hfront hends
  choose psi hPL H hmap hinj using hends
  have hsep : ∀ s, N s ⊆ (interior (N (!s)))ᶜ := by
    intro s x hx hint
    have hxother := interior_subset hint
    have hend : q x ∈ ({(a : C0), (b : C0)} : Set C0) := by
      rw [← complementary_closed_circle_arcs_inter p hab hw]
      cases s
      · exact ⟨hx.2, hxother.2⟩
      · exact ⟨hxother.2, hx.2⟩
    have hxfront : x ∈ frontier (N (!s)) := by
      rw [hfront]
      exact hend
    exact hxfront.2 hint
  obtain ⟨chi, hchi, ⟨Gchi⟩, _, hvalue, _, _⟩ :=
    exists_hamiltonZero_exterior_relative_slab_pasting hd phi F psi N
      (fun s => (he s).closed) hsep hPL (fun s => (H s).some)
      (R := univ) (fun _ => subset_univ _)
  have hfixed : EqOn (hamiltonZeroAmbientMap chi) (hamiltonZeroAmbientMap phi)
      (frontier (N false)) := by
    intro x hx
    exact (hvalue false ((he false).closed.frontier_subset hx)).trans
      (((H false).some).fst_eq_snd hx.2).symm
  have hmap' : ∀ s, MapsTo (phase ∘ hamiltonZeroAmbientMap chi) (N s)
      (AddCircle.closedIntervalArc p (if s then b else a) (if s then a + p else b)) := by
    intro s x hx
    change phase (hamiltonZeroAmbientMap chi x) ∈ _
    rw [hvalue s hx]
    exact hmap s hx
  have hinj' : ∀ s, IsLocallyInjective (fun x : N s => hamiltonZeroAmbientMap chi x) := by
    intro s
    have hfun : (fun x : N s => hamiltonZeroAmbientMap chi x) =
        (fun x : N s => hamiltonZeroAmbientMap (psi s) x) :=
      funext (fun x => hvalue s x.property)
    rw [hfun]
    exact hinj s
  have hlocal := hamiltonZero_locally_injective_of_complementary_slabs
    (chi := phi) hchi isClosed_univ phase hopen hab hw (he false) hfixed hmap' hinj'
  have hambient : IsLocallyInjective (hamiltonZeroAmbientMap chi) := by
    have h := hlocal.comp_right (Homeomorph.Set.univ X0).symm.continuous
      (Homeomorph.Set.univ X0).symm.injective
    exact h
  obtain ⟨g, _, hg, G, Fg⟩ :=
    exists_hamiltonZero_rigidity_of_locallyInjective e d phi chi F Gchi hchi hambient
  exact ⟨g, hg, G, Fg⟩

end PoincareConjecture.M76
