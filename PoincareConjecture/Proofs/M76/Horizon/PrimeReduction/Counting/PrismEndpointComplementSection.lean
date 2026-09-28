import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Counting.ComponentHomotopySection
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.IntervalBundleMidpoint
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Bundles.RawPrismRescalingInjection

set_option autoImplicit false
open Set Geometry
open scoped Topology
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1

theorem exists_prism_endpoint_complement_section
    {E ι : Type*} [TopologicalSpace E] {A B : ι → Set E}
    (H : ∀i,(A i ×ˢ I : Set (E × ℝ)) ≃ₜ B i)
    (L : C((⋃i,B i) × I,(⋃i,B i)))
    (hL : ∀i (y : B i) t,(L (⟨y,mem_iUnion.mpr ⟨i,y.property⟩⟩,t) : E) =
      prismFiberInterpolation (H i) y t)
    (J : (⋃i,B i) ≃ₜ (⋃i,B i))
    (hJ : ∀i (y : B i),(J ⟨y,mem_iUnion.mpr ⟨i,y.property⟩⟩ : E) = prismFiberReflection (H i) y)
    (hfree : ∀i (y : B i),
      (((H i).symm y : E × ℝ).2 = 0 ∨ ((H i).symm y : E × ℝ).2 = 1) →
      (J ⟨y,mem_iUnion.mpr ⟨i,y.property⟩⟩ : E) ≠ y)
    (x : (⋃i,B i : Set E)) :
    ∃ (s : C(connectedComponentIn (⋃i,B i) x,
        connectedComponentIn ((⋃i,B i) \ ⋃i,prismEnds (H i)) (L (x,fiberMidHeight) : E)))
      (i : C(connectedComponentIn ((⋃i,B i) \ ⋃i,prismEnds (H i)) (L (x,fiberMidHeight) : E),
        connectedComponentIn (⋃i,B i) x)),
      (∀y,(s y : E) = L (⟨y,connectedComponentIn_subset _ _ y.property⟩,fiberMidHeight)) ∧
      (∀y,(i y : E) = y) ∧ (i.comp s).Homotopic (ContinuousMap.id _) := by
  let F : C(I × (⋃i,B i : Set E),(⋃i,B i)) :=
    ⟨fun z => L (z.2,⟨(z.1 : ℝ)/2,by constructor <;> linarith [z.1.property.1,z.1.property.2]⟩),by fun_prop⟩
  have hF0 (y) : F (0,y) = y := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp y.property
    apply Subtype.ext
    have hh := hL i ⟨y,hi⟩ 0
    have hEq : (F (0,y) : E) =
        (L (⟨y,mem_iUnion.mpr ⟨i,hi⟩⟩,0) : E) := by
      unfold F
      apply congrArg (fun z : (⋃i,B i) × I => (L z : E))
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        norm_num
    exact hEq.trans (hh.trans (by simp only [prismFiberInterpolation_zero]))
  have hF1 (y) : (F (1,y) : E) ∈ (⋃i,B i) \ ⋃i,prismEnds (H i) := by
    refine ⟨(F (1,y)).property,?_⟩
    have hfixed : J (F (1,y)) = F (1,y) := by
      obtain ⟨i,hi⟩ := mem_iUnion.mp y.property
      have hv : (F (1,y) : E) = prismFiberMidpoint (H i) ⟨y,hi⟩ :=
        (hL i ⟨y,hi⟩ fiberMidHeight).trans
          (congrArg Subtype.val (prismFiberInterpolation_midpoint (H i) ⟨y,hi⟩))
      have he : F (1,y) = ⟨prismFiberMidpoint (H i) ⟨y,hi⟩,
          mem_iUnion.mpr ⟨i,(prismFiberMidpoint (H i) ⟨y,hi⟩).property⟩⟩ := Subtype.ext hv
      apply Subtype.ext
      rw [he,hJ,prismFiberMidpoint_fixed]
    intro hm
    obtain ⟨i,⟨⟨a,b⟩,hab⟩⟩ := mem_iUnion.mp hm
    have ht : (((H i).symm (prismEndMap (H i) a b) : E × ℝ).2 = 0 ∨
        ((H i).symm (prismEndMap (H i) a b) : E × ℝ).2 = 1) := by
      cases b <;> simp [prismEndMap]
    have he : F (1,y) = ⟨prismEndMap (H i) a b,
        mem_iUnion.mpr ⟨i,(prismEndMap (H i) a b).property⟩⟩ := Subtype.ext hab.symm
    have hj : (J ⟨prismEndMap (H i) a b,
        mem_iUnion.mpr ⟨i,(prismEndMap (H i) a b).property⟩⟩ : E) =
        prismEndMap (H i) a b := by
      calc
        (J ⟨prismEndMap (H i) a b,_⟩ : E) = (J (F (1,y)) : E) := by
          rw [he]
        _ = F (1,y) := congrArg Subtype.val hfixed
        _ = prismEndMap (H i) a b := congrArg Subtype.val he
    exact hfree i (prismEndMap (H i) a b) ht hj
  exact exists_component_homotopy_section _ _ sdiff_subset F hF0 hF1 x

end PoincareConjecture.M76.PrismBelt
