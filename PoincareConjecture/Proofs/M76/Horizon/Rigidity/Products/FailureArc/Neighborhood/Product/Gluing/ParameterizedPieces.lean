import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.Real.Lemmas



set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli.ProductGluing

local notation "I" => Icc (0 : ℝ) 1

theorem exists_homeomorph_of_parametrized_pieces
    {X σ : Type*} [TopologicalSpace X] [T2Space X] [Finite σ]
    (C : σ → Type*) [∀ i, TopologicalSpace (C i)] [∀ i, CompactSpace (C i)]
    (b : ∀ i, C i → X) (f : ∀ i, C i × I → X)
    (hf : ∀ i, Continuous (f i))
    (hzero : ∀ i x, f i (x,⟨0,by norm_num⟩) = b i x)
    (hcollision : ∀ i j (x : C i) (y : C j) (s t : I),
      f i (x,s) = f j (y,t) ↔ b i x = b j y ∧ s = t) :
    ∃ H : (⋃ i, range (b i)) × I ≃ₜ (⋃ i, range (f i)),
      (∀ i x t, (H (⟨b i x,mem_iUnion.mpr ⟨i,mem_range_self x⟩⟩,t) : X) = f i (x,t)) ∧
      ∀ x, (H (x,⟨0,by norm_num⟩) : X) = x := by
  classical
  let B : Set X := ⋃ i, range (b i)
  let R : Set X := ⋃ i, range (f i)
  have hb (i : σ) : Continuous (b i) := by
    have hc : Continuous (fun x => f i (x,⟨0,by norm_num⟩)) :=
      (hf i).comp (continuous_id.prodMk continuous_const)
    exact hc.congr (fun x => hzero i x)
  have hB : IsCompact B := isCompact_iUnion fun i => isCompact_range (hb i)
  letI := isCompact_iff_compactSpace.mp hB
  have hchoose (x : B) : ∃ i, ∃ y : C i, b i y = x := by
    obtain ⟨i,hi⟩ := mem_iUnion.mp x.property
    obtain ⟨y,hy⟩ := hi
    exact ⟨i,y,hy⟩
  choose index point hpoint using hchoose
  let g : B × I → R := fun z =>
    ⟨f (index z.1) (point z.1,z.2),mem_iUnion.mpr ⟨index z.1,mem_range_self _⟩⟩
  have hvalue (i : σ) (x : C i) (t : I) :
      (g (⟨b i x,mem_iUnion.mpr ⟨i,mem_range_self x⟩⟩,t) : X) = f i (x,t) := by
    exact (hcollision _ i _ x t t).mpr ⟨hpoint _,rfl⟩
  let q : (Σ i, C i × I) → B × I := fun z =>
    (⟨b z.1 z.2.1,mem_iUnion.mpr ⟨z.1,mem_range_self _⟩⟩,z.2.2)
  have hqc : Continuous q := continuous_sigma fun i =>
    ((hb i).comp continuous_fst |>.subtype_mk _).prodMk continuous_snd
  have hqsurj : Function.Surjective q := by
    rintro ⟨x,t⟩
    refine ⟨⟨index x,point x,t⟩,?_⟩
    exact Prod.ext (Subtype.ext (hpoint x)) rfl
  have hquot : IsQuotientMap q := .of_surjective_continuous hqsurj hqc
  have hgc : Continuous g := hquot.continuous_iff.mpr (continuous_sigma fun i => by
    have hc : Continuous (fun z : C i × I =>
        (⟨f i z,mem_iUnion.mpr ⟨i,mem_range_self z⟩⟩ : R)) := (hf i).subtype_mk _
    apply hc.congr
    intro z
    exact Subtype.ext (hvalue i z.1 z.2).symm)
  have hgbij : Function.Bijective g := by
    constructor
    · rintro ⟨x,s⟩ ⟨y,t⟩ hxy
      have h := (hcollision (index x) (index y) (point x) (point y) s t).mp
        (congrArg Subtype.val hxy)
      exact Prod.ext (Subtype.ext ((hpoint x).symm.trans (h.1.trans (hpoint y)))) h.2
    · intro y
      obtain ⟨i,hi⟩ := mem_iUnion.mp y.property
      obtain ⟨⟨x,t⟩,hxy⟩ := hi
      refine ⟨(⟨b i x,mem_iUnion.mpr ⟨i,mem_range_self x⟩⟩,t),?_⟩
      exact Subtype.ext ((hvalue i x t).trans hxy)
  let H := (show Continuous (Equiv.ofBijective g hgbij) from hgc).homeoOfEquivCompactToT2
  refine ⟨H,hvalue,?_⟩
  intro x
  exact (hzero (index x) (point x)).trans (hpoint x)

end PoincareConjecture.M76.Dehn.Annuli.ProductGluing
