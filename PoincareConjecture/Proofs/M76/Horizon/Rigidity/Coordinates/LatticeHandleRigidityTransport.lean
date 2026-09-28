import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coordinates.LatticeHandleNormalization

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

theorem exists_lattice_handle_rigidity_transport
    {ι ι' κ κ' α β : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
    {L : Submodule ℤ (κ → ℝ)} {L' : Submodule ℤ (κ' → ℝ)}
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι' κ' L') (Fin 3 → ℝ)}
    {d : β → OpenPartialHomeomorph (LatticeHandleAmbient ι' κ' L') (Fin 3 → ℝ)}
    (h : LatticeHandleAmbient ι κ L ≃ₜ LatticeHandleAmbient ι' κ' L')
    (g : LatticeHandle ι κ L ≃ₜ LatticeHandle ι' κ' L')
    (hR : h ⁻¹' latticeHandleDomain ι' κ' L' = latticeHandleDomain ι κ L)
    (hg : ∀ x, ((g x).1.val, (g x).2) = h (x.1.val, x.2))
    (hB : g ⁻¹' latticeHandleBoundary ι' κ' L' = latticeHandleBoundary ι κ L)
    (phi : C(LatticeHandle ι' κ' L', LatticeHandle ι' κ' L'))
    (psi : C(LatticeHandle ι κ L, LatticeHandle ι κ L))
    (hconj : ∀ x, g (psi x) = phi (g x))
    (F : (ContinuousMap.id (LatticeHandle ι' κ' L')).HomotopyRel phi
      (latticeHandleBoundary ι' κ' L'))
    (f : LatticeHandle ι κ L ≃ₜ LatticeHandle ι κ L)
    (hf : ChartwisePLHomeomorph (fun i => h.transOpenPartialHomeomorph (e i))
      (fun i => h.transOpenPartialHomeomorph (d i)) (latticeHandleHomeomorphInDomain ι κ L f))
    (H : psi.HomotopyRel ⟨f, f.continuous⟩ (latticeHandleBoundary ι κ L)) :
    ∃ f' : LatticeHandle ι' κ' L' ≃ₜ LatticeHandle ι' κ' L',
      ChartwisePLHomeomorph e d (latticeHandleHomeomorphInDomain ι' κ' L' f') ∧
      Nonempty (phi.HomotopyRel ⟨f', f'.continuous⟩ (latticeHandleBoundary ι' κ' L')) ∧
      Nonempty ((ContinuousMap.id (LatticeHandle ι' κ' L')).HomotopyRel
        ⟨f', f'.continuous⟩ (latticeHandleBoundary ι' κ' L')) := by
  let f' := (g.symm.trans f).trans g
  have hRi : h.symm ⁻¹' latticeHandleDomain ι κ L = latticeHandleDomain ι' κ' L' := by
    rw [← hR]
    ext y
    simp only [mem_preimage, h.apply_symm_apply]
  have hBi : g.symm ⁻¹' latticeHandleBoundary ι κ L = latticeHandleBoundary ι' κ' L' := by
    rw [← hB]
    ext y
    simp only [mem_preimage, g.apply_symm_apply]
  have hgi (x : LatticeHandle ι' κ' L') :
      ((g.symm x).1.val, (g.symm x).2) = h.symm (x.1.val, x.2) := by
    apply h.injective
    rw [h.apply_symm_apply, ← hg, g.apply_symm_apply]
  have hfi (x) : g.symm (f' x) = f (g.symm x) := g.symm_apply_apply _
  have hphii (x) : g.symm (phi x) = psi (g.symm x) := by
    apply g.injective
    rw [g.apply_symm_apply, hconj, g.apply_symm_apply]
  have H' : phi.HomotopyRel ⟨f', f'.continuous⟩ (latticeHandleBoundary ι' κ' L') := by
    simpa only [hBi] using H.of_homeomorph_conjugacy
      (g₀ := phi) (g₁ := ⟨f', f'.continuous⟩) g.symm hphii hfi
  refine ⟨f', ?_, ⟨H'⟩, ⟨F.trans H'⟩⟩
  simpa only [homeomorph_pullback_chart_cancel] using
    hf.lattice_handle_conjugacy h.symm g.symm hRi hgi f' hfi

end PoincareConjecture.M76
