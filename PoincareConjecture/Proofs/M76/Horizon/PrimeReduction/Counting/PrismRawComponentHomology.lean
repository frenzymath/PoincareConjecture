import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.PrismEndpointComplementSection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ComponentHomologyTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ComponentHomeomorphTransport
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.PrismInterpolationReflection







set_option autoImplicit false
open Set CategoryTheory Limits
namespace PoincareConjecture.M76.PrismBelt
universe u
local notation "I" => Icc (0 : ℝ) 1

theorem prism_rescaling_fixes_midpoint
    {E : Type*} [TopologicalSpace E] {A B : Set E}
    (H : (A ×ˢ I : Set (E × ℝ)) ≃ₜ B)
    (C : (A ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim H)
    (hC : ∀ y, (C y : E) = H (trimProduct A y))
    (r : E → E) (hr : ∀ y, r (C y) = H y) (x : prismTrim H) :
    r (prismFiberInterpolation C x fiberMidHeight) =
      (prismFiberInterpolation C x fiberMidHeight : E) := by
  rw [prismFiberInterpolation_midpoint]
  let y : (A ×ˢ I : Set (E × ℝ)) :=
    ⟨((C.symm x : E × ℝ).1,(1/2 : ℝ)),(C.symm x).property.1,by norm_num⟩
  change r (C y) = (C y : E)
  rw [hr,hC]
  congr 2
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · norm_num [trimProduct,trimInterval,y]

theorem exists_raw_prism_component_homology_retract
    {E ι : Type u} [TopologicalSpace E] {A B : ι → Set E} {V R : Set E}
    (H : ∀ j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ B j)
    (C : ∀ j, (A j ×ˢ I : Set (E × ℝ)) ≃ₜ prismTrim (H j))
    (hC : ∀ j y, (C j y : E) = H j (trimProduct (A j) y))
    (L : C((⋃ j,prismTrim (H j)) × I,(⋃ j,prismTrim (H j))))
    (hL : ∀ j (y : prismTrim (H j)) t,
      (L (⟨y,mem_iUnion.mpr ⟨j,y.property⟩⟩,t) : E) = prismFiberInterpolation (C j) y t)
    (r : E → E) (hr : ∀ j y, r (C j y) = H j y)
    (W : ((⋃ j,prismTrim (H j)) \ ⋃ j,prismEnds (C j) : Set E) ≃ₜ V)
    (hW : ∀ x, (W x : E) = r x)
    (htrim : (⋃ j,prismTrim (H j)) ⊆ R) (hV : V ⊆ R)
    (p : (⋃ j,prismEnds (C j) : Set E))
    (hcover : connectedComponentIn R (p : E) ⊆ V)
    (M : ModuleCat.{u} (ZMod 2))
    (i₀ : M ⟶ (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn (⋃ j,prismTrim (H j)) (p : E)))).homology M 1)
    (r₀ : (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn (⋃ j,prismTrim (H j)) (p : E)))).homology M 1 ⟶ M)
    (hi₀ : i₀ ≫ r₀ = 𝟙 M) :
    ∃ (i : M ⟶ (TopCat.toSSet.obj (TopCat.of (connectedComponentIn R (p : E)))).homology M 1)
      (s : (TopCat.toSSet.obj (TopCat.of (connectedComponentIn R (p : E)))).homology M 1 ⟶ M),
      i ≫ s = 𝟙 M := by
  obtain ⟨J,_,hJ,hfree⟩ := exists_prism_reflection_of_interpolation C L hL
  let ep := prismEndpointInclusion C p
  obtain ⟨s,inc,hs,_,hh⟩ := exists_prism_endpoint_complement_section C L hL J hJ hfree ep
  obtain ⟨i₁,r₁,hi₁⟩ := CutGraph.module_homology_retract_of_homotopy_section M s inc hh 1 i₀ r₀ hi₀
  have hmid : (L (ep,fiberMidHeight) : E) ∈
      (⋃ j,prismTrim (H j)) \ ⋃ j,prismEnds (C j) :=
    connectedComponentIn_nonempty_iff.mp ⟨s ⟨p,mem_connectedComponentIn ep.property⟩,
      (s ⟨p,mem_connectedComponentIn ep.property⟩).property⟩
  let m : ((⋃ j,prismTrim (H j)) \ ⋃ j,prismEnds (C j) : Set E) := ⟨_,hmid⟩
  obtain ⟨i₂,r₂,hi₂⟩ := module_homology_retract_of_component_homeomorph W m i₁ r₁ hi₁
  have hfixed : r (L (ep,fiberMidHeight)) = (L (ep,fiberMidHeight) : E) := by
    obtain ⟨j,hj⟩ := mem_iUnion.mp ep.property
    rw [hL j ⟨ep,hj⟩ fiberMidHeight]
    exact prism_rescaling_fixes_midpoint (H j) (C j) (hC j) r (hr j) ⟨ep,hj⟩
  have hlabel : (W m : E) ∈ connectedComponentIn R (p : E) := by
    rw [hW,show (m : E) = (L (ep,fiberMidHeight) : E) from rfl,hfixed]
    let γ : I → E := fun t => L (ep,t)
    have hγ : Continuous γ := by unfold γ; fun_prop
    have hzero : γ 0 = p := by
      obtain ⟨j,hj⟩ := mem_iUnion.mp ep.property
      exact (hL j ⟨ep,hj⟩ 0).trans (congrArg Subtype.val (prismFiberInterpolation_zero _ _))
    exact (isPreconnected_range hγ).subset_connectedComponentIn ⟨0,hzero⟩
      (by rintro z ⟨t,rfl⟩; exact htrim (L (ep,t)).property) ⟨fiberMidHeight,rfl⟩
  have heq : connectedComponentIn V (W m : E) = connectedComponentIn R (p : E) := by
    apply subset_antisymm
    · exact (connectedComponentIn_mono _ hV).trans (connectedComponentIn_eq hlabel).symm.subset
    · exact isPreconnected_connectedComponentIn.subset_connectedComponentIn hlabel hcover
  rw [← heq]
  exact ⟨i₂,r₂,hi₂⟩

end PoincareConjecture.M76.PrismBelt
