import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcSelectedRegion



set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Circle" => sphere (0 : Plane) 1
local notation "CY" => sphere (0 : Fin 2 → ℝ) 1

theorem exists_selected_region_of_normalized_graph
    {Z κ : Type*} [TopologicalSpace Z] [Fintype κ]
    (hk : Fintype.card κ = 2) (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    (F : C(Z,(κ → ℝ) ⧸ L.toAddSubgroup)) (hFi : Function.Injective F)
    (J : C(Z,κ → ℝ)) (hJi : Function.Injective J)
    (hJ : ∀ z, QuotientAddGroup.mk (J z) = F z)
    (gamma delta : C(CY,Z))
    (hgamma : Function.Injective gamma) (hdelta : Function.Injective delta)
    {W C0 C1 : Set Z} (hg : range gamma = W ∪ C0) (hd : range delta = W ∪ C1)
    (hC0 : ∀ z ∈ C0, ‖J z‖ = (3/4 : ℝ))
    (hC1 : ∀ z ∈ C1, ‖J z‖ = (3/4 : ℝ))
    (hne0 : C0.Nonempty) (hne1 : C1.Nonempty)
    (hdiff : range gamma ≠ range delta)
    (havoid : ∀ z, F z ∉ (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) ''
      ball 0 (3/4)) :
    ∃ U : Set ((κ → ℝ) ⧸ L.toAddSubgroup), IsOpen U ∧ IsCompact (closure U) ∧
      IsSimplyConnected U ∧
      (frontier U = range (F.comp gamma) ∨ frontier U = range (F.comp delta)) ∧
      Disjoint (closure U)
        ((QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) '' ball 0 (3/4)) := by
  let a : Plane ≃L[ℝ] (κ → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [hk])
  let c : (Fin 2 → ℝ) ≃L[ℝ] Plane := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let C := PoincareConjecture.Proofs.M02.Topology.unitSphereHomeomorph c
  let sigma : C(Circle,CY) := ⟨C.symm,C.symm.continuous⟩
  let j : C(Z,Plane) := ⟨fun z => a.symm (J z),a.symm.continuous.comp J.continuous⟩
  let g := j.comp (gamma.comp sigma)
  let d := j.comp (delta.comp sigma)
  have hji : Function.Injective j := a.symm.injective.comp hJi
  have hgi : Function.Injective g := hji.comp (hgamma.comp C.symm.injective)
  have hdi : Function.Injective d := hji.comp (hdelta.comp C.symm.injective)
  have hgr : range g = j '' range gamma := by
    change range ((j ∘ gamma) ∘ C.symm) = _
    rw [C.symm.surjective.range_comp,Set.range_comp]
  have hdr : range d = j '' range delta := by
    change range ((j ∘ delta) ∘ C.symm) = _
    rw [C.symm.surjective.range_comp,Set.range_comp]
  let p : Plane →+ ((κ → ℝ) ⧸ L.toAddSubgroup) :=
    (QuotientAddGroup.mk' L.toAddSubgroup).comp a.toLinearEquiv.toAddEquiv.toAddMonoidHom
  have hp : IsCoveringMap p :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm DiscreteTopology.isDiscrete).isCoveringMap
      |>.comp_homeomorph a.toHomeomorph
  have hpj (z : Z) : p (j z) = F z := by
    change QuotientAddGroup.mk (a (a.symm (J z))) = _
    rw [a.apply_symm_apply,hJ]
  let T := a ⁻¹' ball (0 : κ → ℝ) (3/4)
  have hT : IsPreconnected T := a.toHomeomorph.isPreconnected_preimage.mpr
    (convex_ball (0 : κ → ℝ) (3/4)).isPreconnected
  have hclT : closure T = a ⁻¹' closedBall (0 : κ → ℝ) (3/4) := by
    change closure (a.toHomeomorph ⁻¹' ball 0 (3/4)) = _
    rw [←a.toHomeomorph.preimage_closure,closure_ball _ (by norm_num : (3/4 : ℝ) ≠ 0)]
    rfl
  have hpT : p '' T =
      (QuotientAddGroup.mk : (κ → ℝ) → (κ → ℝ) ⧸ L.toAddSubgroup) '' ball 0 (3/4) := by
    change (QuotientAddGroup.mk ∘ a) '' (a ⁻¹' ball 0 (3/4)) = _
    ext y
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨a x,hx,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      exact ⟨a.symm x,by simpa using hx,by simp⟩
  have hpi : InjOn p (range g ∪ range d) := by
    rw [hgr,hdr,←image_union]
    rintro _ ⟨x,_,rfl⟩ _ ⟨y,_,rfl⟩ hh
    exact congrArg j (hFi (by simpa only [hpj] using hh))
  have hav : Disjoint (p '' (range g ∪ range d)) (p '' T) := by
    rw [hgr,hdr,←image_union,hpT]
    apply disjoint_left.mpr
    rintro _ ⟨_,⟨z,_,rfl⟩,rfl⟩ hh
    exact havoid z (hpj z ▸ hh)
  have h0 : j '' C0 ⊆ closure T := by
    rintro _ ⟨z,hz,rfl⟩
    rw [hclT]
    change a (a.symm (J z)) ∈ closedBall 0 (3/4)
    rw [a.apply_symm_apply,mem_closedBall_zero_iff,hC0 z hz]
  have h1 : j '' C1 ⊆ closure T := by
    rintro _ ⟨z,hz,rfl⟩
    rw [hclT]
    change a (a.symm (J z)) ∈ closedBall 0 (3/4)
    rw [a.apply_symm_apply,mem_closedBall_zero_iff,hC1 z hz]
  have hmark0 : (range g ∩ closure T).Nonempty := by
    obtain ⟨z,hz⟩ := hne0
    exact ⟨j z,hgr.symm ▸ mem_image_of_mem j (hg.symm ▸ Or.inr hz),h0 (mem_image_of_mem j hz)⟩
  have hmark1 : (range d ∩ closure T).Nonempty := by
    obtain ⟨z,hz⟩ := hne1
    exact ⟨j z,hdr.symm ▸ mem_image_of_mem j (hd.symm ▸ Or.inr hz),h1 (mem_image_of_mem j hz)⟩
  have hdiff' : range g ≠ range d := by
    rw [hgr,hdr]
    exact fun hh => hdiff (Set.image_injective.mpr hji hh)
  obtain ⟨U,hU,hUc,hK,hsc,hreg,hfront,hKi,hdis,hopen,hscq,hcl,hfr⟩ :=
    exists_selected_quotient_jordan_region p hp g d hgi hdi hpi hT hav
      (by rw [hgr,hg,image_union]) (by rw [hdr,hd,image_union]) h0 h1 hmark0 hmark1 hdiff'
  have hpg : p '' range g = range (F.comp gamma) := by
    rw [hgr,image_image]
    change (fun z => p (j z)) '' range gamma = range (F ∘ gamma)
    simp only [hpj,Set.range_comp]
  have hpd : p '' range d = range (F.comp delta) := by
    rw [hdr,image_image]
    change (fun z => p (j z)) '' range delta = range (F ∘ delta)
    simp only [hpj,Set.range_comp]
  refine ⟨p '' U,hopen,hcl ▸ hK.image hp.continuous,hscq,?_,?_⟩
  · rcases hfront with hh | hh
    · exact Or.inl (hfr.trans ((congrArg (p '' ·) hh).trans hpg))
    · exact Or.inr (hfr.trans ((congrArg (p '' ·) hh).trans hpd))
  · simpa only [←hcl,hpT] using hdis

end PoincareConjecture.M76
