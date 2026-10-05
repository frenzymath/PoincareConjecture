import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.PrismEndpointComplementSection
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Counting.ComponentHomologyTransport

/-! # The endpoint class survives after removing the cutting spheres -/

set_option autoImplicit false
open Set CategoryTheory Limits
open scoped Topology
universe u v
namespace PoincareMT.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_prism_endpoint_complement_homology_retract
    {E ι : Type u} [TopologicalSpace E]
    {A B : ι → Set E} (H : ∀i,(A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (L : C((⋃i,B i) × I,(⋃i,B i)))
    (hL : ∀i (y : B i) t,(L (⟨y,mem_iUnion.mpr ⟨i,y.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) y t)
    (J : (⋃i,B i) ≃ₜ (⋃i,B i))
    (hJ : ∀i (y : B i),(J ⟨y,mem_iUnion.mpr ⟨i,y.property⟩⟩ : E) = prismFiberReflection (H i) y)
    (hfree : ∀i (y : B i),
      (((H i).symm y : E × ℝ).2 = 0 ∨ ((H i).symm y : E × ℝ).2 = 1) →
      (J ⟨y,mem_iUnion.mpr ⟨i,y.property⟩⟩ : E) ≠ y)
    (p : (⋃i,prismEnds (H i) : Set E))
    (R : ModuleCat.{u} (ZMod 2))
    (i₀ : R ⟶ (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn (⋃i,B i) (p : E)))).homology R 1)
    (r₀ : (TopCat.toSSet.obj (TopCat.of
      (connectedComponentIn (⋃i,B i) (p : E)))).homology R 1 ⟶ R)
    (hi₀ : i₀ ≫ r₀ = 𝟙 R) :
    ∃ (i : R ⟶ (TopCat.toSSet.obj (TopCat.of
        (connectedComponentIn ((⋃i,B i) \ ⋃i,prismEnds (H i))
        (L (prismEndpointInclusion H p,fiberMidHeight) : E)))).homology R 1)
      (r : (TopCat.toSSet.obj (TopCat.of
        (connectedComponentIn ((⋃i,B i) \ ⋃i,prismEnds (H i))
          (L (prismEndpointInclusion H p,fiberMidHeight) : E)))).homology R 1 ⟶ R), i ≫ r = 𝟙 R := by
  obtain ⟨s,inc,hs,hi,hh⟩ := exists_prism_endpoint_complement_section H L hL J hJ hfree
    (prismEndpointInclusion H p)
  exact CutGraph.module_homology_retract_of_homotopy_section R s inc hh 1 i₀ r₀ hi₀

end PoincareMT.M76.PrismBelt
