import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.PLMapTransport
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonLatticeHandleModel









set_option autoImplicit false

open Set

namespace PoincareConjecture.M76



theorem ChartwisePLMap.lattice_handle_conjugacy
    {ι ι' κ κ' α β : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    {L : Submodule ℤ (κ → ℝ)} {L' : Submodule ℤ (κ' → ℝ)}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι' κ' L') (Fin 3 → ℝ)}
    {d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι' κ' L') (Fin 3 → ℝ)}
    {phi : C(LatticeHandle ι' κ' L', LatticeHandle ι' κ' L')}
    (hphi : ChartwisePLMap e d (latticeHandleMapInDomain ι' κ' L' phi))
    (h : LatticeHandleAmbient ι κ L ≃ₜ LatticeHandleAmbient ι' κ' L')
    (g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι' κ' L')
    (hR : h ⁻¹' latticeHandleDomain ι' κ' L' = latticeHandleDomain ι κ L)
    (hg : ∀ x, ((g x).1.val, (g x).2) = h (x.1.val, x.2))
    (psi : C(LatticeHandle ι κ L, LatticeHandle ι κ L))
    (hconj : ∀ x, g (psi x) = phi (g x)) :
    ChartwisePLMap (fun i => h.transOpenPartialHomeomorph (e i))
      (fun i => h.transOpenPartialHomeomorph (d i)) (latticeHandleMapInDomain ι κ L psi) := by
  apply hphi.transport_homeomorph h h hR.symm hR.symm
    (latticeHandleMapInDomain ι κ L psi)
  intro x
  let q := latticeHandleDomainEquiv ι κ L
  let q' := latticeHandleDomainEquiv ι' κ' L'
  have hx : h x ∈ latticeHandleDomain ι' κ' L' := by
    change x.val ∈ h ⁻¹' latticeHandleDomain ι' κ' L'
    rw [hR]
    exact x.property
  have hqx : g (q x) = q' ⟨h x, hx⟩ := by
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (hg (q x))
    · have hy := congrArg Prod.snd (hg (q x))
      exact hy
  change h ((psi (q x)).1.val, (psi (q x)).2) =
    ((phi (q' ⟨h x, hx⟩)).1.val, (phi (q' ⟨h x, hx⟩)).2)
  rw [← hg, hconj, hqx]



theorem ChartwisePLHomeomorph.lattice_handle_conjugacy
    {ι ι' κ κ' α β : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    {L : Submodule ℤ (κ → ℝ)} {L' : Submodule ℤ (κ' → ℝ)}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι' κ' L') (Fin 3 → ℝ)}
    {d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι' κ' L') (Fin 3 → ℝ)}
    {f : LatticeHandle ι' κ' L' ≃ₜ LatticeHandle ι' κ' L'}
    (hf : ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain ι' κ' L' f))
    (h : LatticeHandleAmbient ι κ L ≃ₜ LatticeHandleAmbient ι' κ' L')
    (g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι' κ' L')
    (hR : h ⁻¹' latticeHandleDomain ι' κ' L' = latticeHandleDomain ι κ L)
    (hg : ∀ x, ((g x).1.val, (g x).2) = h (x.1.val, x.2))
    (f' : LatticeHandle ι κ L ≃ₜ LatticeHandle ι κ L)
    (hconj : ∀ x, g (f' x) = f (g x)) :
    ChartwisePLHomeomorph (fun i => h.transOpenPartialHomeomorph (e i))
      (fun i => h.transOpenPartialHomeomorph (d i)) (latticeHandleHomeomorphInDomain ι κ L f') := by
  refine ⟨ChartwisePLMap.lattice_handle_conjugacy
      (phi := ⟨f, f.continuous⟩) hf.1 h g hR hg ⟨f', f'.continuous⟩ hconj,
    ChartwisePLMap.lattice_handle_conjugacy
      (phi := ⟨f.symm, f.symm.continuous⟩) hf.2 h g hR hg
      ⟨f'.symm, f'.symm.continuous⟩ ?_⟩
  intro x
  change g (f'.symm x) = f.symm (g x)
  apply f.injective
  rw [f.apply_symm_apply, ← hconj, f'.apply_symm_apply]

end PoincareConjecture.M76
