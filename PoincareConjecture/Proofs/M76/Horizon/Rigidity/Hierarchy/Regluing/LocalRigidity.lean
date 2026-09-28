import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.OneSheet.OpenDomain
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.OneSheet.OriginalAtlas
import PoincareConjecture.Proofs.M76.Rigidity.OriginalHandleHomotopy
import PoincareConjecture.Proofs.M76.Rigidity.OriginalClosedAmbient









set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "R0" => latticeHandleDomain (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0

theorem isCoveringMap_hamiltonZero_of_locallyInjective
    {ι κ : Type*} {e : ι → OpenPartialHomeomorph X0 V3}
    {d : κ → OpenPartialHomeomorph X0 V3} {psi : C(H0, H0)}
    (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
    (hinj : IsLocallyInjective (hamiltonZeroAmbientMap psi)) :
    IsCoveringMap psi := by
  let : T2Space H0 := hamiltonZeroHierarchyCoordinates.isEmbedding.t2Space
  let : CompactSpace X0 := isCompact_univ_iff.mp isCompact_hamiltonZeroAmbient
  let : CompactSpace H0 := hamiltonZeroAmbientEquiv.surjective.compactSpace
    hamiltonZeroAmbientEquiv.continuous
  have hRopen : IsOpen R0 := hamiltonZeroDomain_eq_univ.symm ▸ isOpen_univ
  have hdomainInj : IsLocallyInjective (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) := by
    rw [← hamiltonZeroAmbientMapInDomain_original]
    intro x
    obtain ⟨U, hU, hxU, hiU⟩ := hinj (x : X0)
    refine ⟨Subtype.val ⁻¹' U, hU.preimage continuous_subtype_val, hxU, ?_⟩
    intro y hy z hz heq
    apply Subtype.ext
    exact hiU hy hz (congrArg Subtype.val heq)
  have hdomain := hpsi.isLocalHomeomorph_of_open hRopen hRopen hdomainInj
  let q := latticeHandleDomainEquiv (Fin 0) (Fin 3) L0
  have hlocal := q.isLocalHomeomorph.comp (hdomain.comp q.symm.isLocalHomeomorph)
  have hval : (q ∘ (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi) ∘ q.symm) = psi := by
    funext x
    change q (q.symm (psi (q (q.symm x)))) = psi x
    rw [q.apply_symm_apply, q.apply_symm_apply]
  rw [hval] at hlocal
  exact isLocalHomeomorph_iff_isCoveringMap.mp hlocal

theorem exists_hamiltonZero_rigidity_of_locallyInjective
    {ι κ : Type*} (e : ι → OpenPartialHomeomorph X0 V3)
    (d : κ → OpenPartialHomeomorph X0 V3) (phi psi : C(H0, H0))
    (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    (G : phi.HomotopyRel psi B0)
    (hpsi : ChartwisePLMap e d (latticeHandleMapInDomain (Fin 0) (Fin 3) L0 psi))
    (hinj : IsLocallyInjective (hamiltonZeroAmbientMap psi)) :
    ∃ g : H0 ≃ₜ H0,
      (∀ x, g x = psi x) ∧
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain (Fin 0) (Fin 3) L0 g) ∧
      Nonempty (phi.HomotopyRel ⟨g, g.continuous⟩ B0) ∧
      Nonempty ((ContinuousMap.id H0).HomotopyRel ⟨g, g.continuous⟩ B0) :=
  exists_lattice_handle_rigidity_of_covering L0 e d phi psi F G hpsi
    (isCoveringMap_hamiltonZero_of_locallyInjective hpsi hinj)

end PoincareConjecture.M76
