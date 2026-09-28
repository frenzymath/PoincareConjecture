import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.BoundedSphereRegion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Cutting.OriginalFiniteSphereCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.NoL3CutBallObstruction

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem OriginalFiniteSphereCollar.not_both_ports_subset_of_lattice
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {R S O : Set (LatticeHandleAmbient ι κ L)}
    {B : Bool → Set (LatticeHandleAmbient ι κ L)}
    (C : OriginalFiniteSphereCollar e R S O B)
    (s : ChartwisePLSphere e S)
    (he : PLDomain e (latticeHandleDomain ι κ L))
    (hdim : Fintype.card ι + Fintype.card κ = 3)
    (hSR : S ⊆ latticeHandleDomain ι κ L)
    {A : Set (LatticeHandleAmbient ι κ L)}
    (hA : IsPreconnected A) (hAO : A ⊆ Oᶜ) :
    ¬ (B false ⊆ A ∧ B true ⊆ A) := by
  classical
  obtain ⟨D, hD, _, _, hfront, hclfront, _⟩ :=
    s.exists_lattice_bounded_region L he hdim hSR
  have hregular : interior (closure D) = D := by
    rw [← closure_sdiff_frontier, closure_closure, hclfront, ← hfront,
      hD.frontier_eq, sdiff_sdiff_right_self, inter_eq_right.mpr subset_closure]
  have hclosedRegular : closure (interior (closure D)) = closure D := by rw [hregular]
  have hexteriorRegular : closure (interior Dᶜ) = Dᶜ := by
    rw [interior_compl, closure_compl, hregular]
  have hcenter : C.map '' (C.complex.space ×ˢ ({0} : Set ℝ)) = S := by
    ext x
    constructor
    · rintro ⟨⟨z,t⟩, ⟨hz,ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      rw [C.center ⟨z,hz⟩]
      exact (C.parametrization ⟨z,hz⟩).property
    · intro hx
      refine ⟨((C.parametrization.symm ⟨x,hx⟩ : C.complex.space),0),
        ⟨(C.parametrization.symm ⟨x,hx⟩).property,rfl⟩, ?_⟩
      rw [C.center]
      exact congrArg Subtype.val (C.parametrization.apply_symm_apply ⟨x,hx⟩)
  have hSO : S ⊆ O := by
    apply hcenter.symm.subset.trans
    apply Subset.trans _ C.open_eq.symm.subset
    apply image_mono
    exact prod_mono subset_rfl (by
      intro t ht
      have ht0 : t = 0 := ht
      rw [ht0]
      exact ⟨neg_lt_zero.mpr C.width_pos, C.width_pos⟩)
  have hc : ContinuousOn C.map (C.complex.space ×ˢ Icc (-1 : ℝ) 1) :=
    C.pl.continuousOn
  have hi : InjOn C.map (C.complex.space ×ˢ Icc (-1 : ℝ) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val (C.embedding.injective (a₁ := ⟨x,hx⟩) (a₂ := ⟨y,hy⟩) hxy)
  have hopen : IsOpen (C.map '' (C.complex.space ×ˢ Ioo (-C.width) C.width)) :=
    C.open_eq ▸ C.isOpen
  have hne : S.Nonempty := by
    obtain ⟨x,hx⟩ := (isConnected_sphere (by simp) (0 : V3) zero_le_one).nonempty
    exact ⟨s.parametrization ⟨x,hx⟩, (s.parametrization ⟨x,hx⟩).property⟩
  obtain ⟨b,x,hxb,hxin⟩ := exists_collar_end_in_interior C.width_pos
    (by linarith [C.width_le]) hc hi hopen (hcenter.trans hclfront.symm)
    (hclfront.symm ▸ hne) hclosedRegular
  obtain ⟨b',y,hyb,hyout⟩ := exists_collar_end_in_interior C.width_pos
    (by linarith [C.width_le]) hc hi hopen
    (hcenter.trans ((frontier_compl (s := D)).trans hfront).symm)
    (((frontier_compl (s := D)).trans hfront).symm ▸ hne) hexteriorRegular
  rw [hregular] at hxin
  intro hboth
  have hBA (j : Bool) : B j ⊆ A := by cases j <;> simp_all
  have hxA := hBA b ((C.endpoint_eq b).symm.subset hxb)
  have hyA := hBA b' ((C.endpoint_eq b').symm.subset hyb)
  have hdis : Disjoint A (frontier D) := by
    rw [hfront]
    exact disjoint_left.mpr fun z hzA hzS => hAO hzA (hSO hzS)
  have hAD : A ⊆ interior D :=
    hA.subset_interior_of_avoids_frontier hdis ⟨x,hxA,hD.interior_eq.symm ▸ hxin⟩
  exact (interior_subset hyout) (interior_subset (hAD hyA))

end PoincareConjecture.M76
