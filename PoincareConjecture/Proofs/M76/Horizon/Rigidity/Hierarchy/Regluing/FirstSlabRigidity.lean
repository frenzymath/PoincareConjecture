import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Regluing.ComplementaryRigidity
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.ComplementarySlabDomains












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
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem exists_hamiltonZero_rigidity_of_first_slab_endpoints
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3}
    (hd : StandardLatticeHandleAtlas (Fin 0) (Fin 3) L0 d)
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hb : b < p)
    (he : PLDomain e (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b))
    (hfront : frontier (hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b) =
      hamiltonZeroCircleMap phi ⁻¹' {(a : C0), (b : C0)}) :
    let R := hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b
    (∀ side : Bool, ∃ psi : C(H0, H0),
      ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∧
      Nonempty ((hamiltonZeroAmbientMap phi).HomotopyRel
        (hamiltonZeroAmbientMap psi) (interior (if side then (interior R)ᶜ else R))ᶜ) ∧
      MapsTo (hamiltonZeroCircleMap psi) (if side then (interior R)ᶜ else R)
        (AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b)) ∧
      IsLocallyInjective (fun x : ↥(if side then (interior R)ᶜ else R) => hamiltonZeroAmbientMap psi x)) →
    ∃ g : H0 ≃ₜ H0,
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 0) (Fin 3) L0 g) ∧
      Nonempty (phi.HomotopyRel ⟨g, g.continuous⟩ B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel ⟨g, g.continuous⟩ B0) := by
  intro R hends
  let : Fact (0 < p) := ⟨by norm_num⟩
  let phase : C(X0, C0) := ⟨fun x => (Q0 x).2, (Q0).continuous.snd⟩
  have hopen : IsOpenMap phase := isOpenMap_snd.comp (Q0).isOpenMap
  have hphase (psi : C(H0, H0)) : phase.comp (hamiltonZeroAmbientMap psi) =
      hamiltonZeroCircleMap psi := by
    ext x
    exact hamiltonZeroAmbientMap_circle psi x
  have hcomp : (interior R)ᶜ =
      hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p b (a + p) :=
    circle_slab_closed_exterior_eq p (hamiltonZeroCircleMap phi) ha hab hb hfront
  have hN (side : Bool) : (univ : Set X0) ∩ (phase.comp (hamiltonZeroAmbientMap phi)) ⁻¹'
      AddCircle.closedIntervalArc p (if side then b else a) (if side then a + p else b) =
        (if side then (interior R)ᶜ else R) := by
    rw [hphase, univ_inter]
    cases side
    · rfl
    · exact hcomp.symm
  apply exists_hamiltonZero_rigidity_of_complementary_endpoints hd phi F phase hopen
    hab (by linarith : b < a + p)
  · intro side
    dsimp only
    rw [hN side]
    cases side
    · exact he
    · exact he.closed_exterior
  · intro side
    dsimp only
    rw [hN side, hphase]
    cases side
    · exact hfront
    · exact he.frontier_closed_exterior.trans hfront
  · intro side
    dsimp only
    obtain ⟨psi, hpsi, Hpsi, hmap, hinj⟩ := hends side
    refine ⟨psi, hpsi, ?_, ?_, ?_⟩
    · rwa [hN side]
    · intro x hx
      change (Q0 (hamiltonZeroAmbientMap psi x)).2 ∈ _
      rw [hamiltonZeroAmbientMap_circle]
      exact hmap ((hN side).subset hx)
    · exact hinj.comp_right (Homeomorph.setCongr (hN side)).continuous
        (Homeomorph.setCongr (hN side)).injective

end PoincareConjecture.M76
