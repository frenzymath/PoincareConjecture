import PoincareConjecture.Proofs.Horizon.Topology.Homotopy.Cube.CubeHomotopyLifting









set_option autoImplicit false

open scoped Topology unitInterval

universe u v

namespace Poincare.Topology

noncomputable section

private theorem int_hom_injective_of_surjective
    (F : Multiplicative Int →* Multiplicative Int) (hsurj : Function.Surjective F) :
    Function.Injective F := by
  have hformula (z : Int) :
      (F (Multiplicative.ofAdd z)).toAdd =
        z * (F (Multiplicative.ofAdd 1)).toAdd := by
    have h := congrArg Multiplicative.toAdd
      (map_zpow F (Multiplicative.ofAdd (1 : Int)) z)
    simpa [← ofAdd_zsmul, Int.zsmul_eq_mul] using h
  have hne : (F (Multiplicative.ofAdd 1)).toAdd ≠ 0 := by
    intro hzero
    obtain ⟨a, ha⟩ := hsurj (Multiplicative.ofAdd 1)
    have h := hformula a.toAdd
    simp only [ofAdd_toAdd, ha, toAdd_ofAdd, hzero,
      mul_zero] at h
    exact one_ne_zero h
  intro a b hab
  change a.toAdd = b.toAdd
  apply mul_right_cancel₀ hne
  rw [← hformula, ← hformula]
  exact congrArg Multiplicative.toAdd hab

private theorem bijective_of_maps_int_generator
    {G : Type u} [Group G] {H : Type v} [Group H]
    (eG : G ≃* Multiplicative Int) (eH : H ≃* Multiplicative Int)
    (F : G →* H) (a : G) (ha : eH (F a) = Multiplicative.ofAdd 1) :
    Function.Bijective F := by
  have hsurj : Function.Surjective F := by
    intro b
    refine ⟨a ^ (eH b).toAdd, eH.injective ?_⟩
    rw [map_zpow, map_zpow, ha]
    simp [← ofAdd_zsmul]
  let ZF : Multiplicative Int →* Multiplicative Int :=
    eH.toMonoidHom.comp (F.comp eG.symm.toMonoidHom)
  have hZF : Function.Injective ZF := int_hom_injective_of_surjective ZF
    (eH.surjective.comp (hsurj.comp eG.symm.surjective))
  refine ⟨?_, hsurj⟩
  intro a b hab
  apply eG.injective
  apply hZF
  simpa only [ZF, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply] using congrArg eH hab

theorem exists_sphere_map_of_homotopyGroup_int_equiv
    {S : Type u} [TopologicalSpace S]
    {Y : Type v} [TopologicalSpace Y]
    (n : Nat) (q : C((Fin (n + 1) → unitInterval), S))
    (hq : _root_.Topology.IsQuotientMap q)
    (hfiber : ∀ a b, q a = q b ↔ a = b ∨
      (a ∈ Cube.boundary (Fin (n + 1)) ∧ b ∈ Cube.boundary (Fin (n + 1))))
    (y0 : Y)
    (eS : HomotopyGroup.Pi (n + 1) S (q (fun _ => 0)) ≃* Multiplicative Int)
    (eY : HomotopyGroup.Pi (n + 1) Y y0 ≃* Multiplicative Int) :
    ∃ f : C(S, Y), f (q (fun _ => 0)) = y0 ∧
      Function.Bijective (homotopyGroupPostcomp n f (q (fun _ => 0))) := by
  let zero : Fin (n + 1) → unitInterval := fun _ => 0
  let s0 : S := q zero
  have hz : zero ∈ Cube.boundary (Fin (n + 1)) := ⟨0, Or.inl rfl⟩
  have hqboundary (z : Fin (n + 1) → unitInterval)
      (h : z ∈ Cube.boundary (Fin (n + 1))) : q z = s0 :=
    (hfiber z zero).mpr (Or.inr ⟨h, hz⟩)
  let b : GenLoop (Fin (n + 1)) S s0 := ⟨q, hqboundary⟩
  obtain ⟨a, ha⟩ := Quotient.exists_rep (eY.symm (Multiplicative.ofAdd 1))
  have hgen : eY (Quotient.mk _ a) = Multiplicative.ofAdd 1 := by
    rw [ha]
    exact eY.apply_symm_apply _
  have hlift_bijective (f : C(S, Y)) (hbase : f s0 = y0)
      (hfa : ∀ z, f (q z) = a z) :
      Function.Bijective (homotopyGroupPostcomp n f s0) := by
    subst y0
    apply bijective_of_maps_int_generator eS eY (homotopyGroupPostcomp n f s0)
      (Quotient.mk _ b)
    have he : genLoopPostcomp n f s0 b = a := by
      apply GenLoop.ext
      exact hfa
    change eY (Quotient.mk _ (genLoopPostcomp n f s0 b)) = Multiplicative.ofAdd 1
    rw [he]
    exact hgen
  have hfactor : Function.FactorsThrough a.val q := by
    intro z w h
    rcases (hfiber z w).mp h with rfl | ⟨hz', hw⟩
    · rfl
    · exact (GenLoop.boundary a z hz').trans (GenLoop.boundary a w hw).symm
  let f : C(S, Y) := hq.lift a.val hfactor
  have hfa (z : Fin (n + 1) → unitInterval) : f (q z) = a z :=
    DFunLike.congr_fun (hq.lift_comp a.val hfactor) z
  have hbase : f s0 = y0 := (hfa zero).trans (GenLoop.boundary a zero hz)
  exact ⟨f, hbase, hlift_bijective f hbase hfa⟩

end

end Poincare.Topology
