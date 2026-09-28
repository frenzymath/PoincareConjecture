import PoincareConjecture.Proofs.M02.Topology.IntegralCompactSupportOpenMV









set_option autoImplicit false

noncomputable section

open Set TopologicalSpace

universe u

namespace PoincareConjecture.Proofs.M02.Topology

variable {X : Type u} [TopologicalSpace X]

theorem exists_integralCompact_preimage_of_subset_range
    {Y : Type u} [TopologicalSpace Y] (f : C(X, Y))
    (hf : _root_.Topology.IsOpenEmbedding f) (R : Compacts Y)
    (hR : (R : Set Y) ⊆ Set.range f) :
    ∃ S : Compacts X, S.map f f.continuous = R := by
  have hmem : R ∈ Set.range (Compacts.map f f.continuous) := by
    rw [Compacts.range_map hf.isEmbedding.isInducing]
    exact hR
  exact hmem

def integralCompactSubtypePreimage (U : Set X) (P : Set X) (hP : IsCompact P)
    (hPU : P ⊆ U) : Compacts U :=
  ⟨(Subtype.val : U → X) ⁻¹' P,
    (Topology.IsInducing.subtypeVal.isCompact_preimage' hP (by
      intro x hx
      exact ⟨⟨x, hPU hx⟩, rfl⟩))⟩

theorem integralCompactSubtypePreimage_le_iff (U P : Set X) (hP : IsCompact P)
    (hPU : P ⊆ U) (K : Compacts U) :
    K ≤ integralCompactSubtypePreimage U P hP hPU ↔
      (integralOpenSubtypeVal U) '' (K : Set U) ⊆ P := by
  constructor
  · intro h x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact h hy
  · intro h x hx
    change (x : X) ∈ P
    exact h ⟨x, hx, rfl⟩

theorem integralCompactSubtypePreimage_image_subset (U P : Set X) (hP : IsCompact P)
    (hPU : P ⊆ U) :
    (integralOpenSubtypeVal U) ''
        ((integralCompactSubtypePreimage U P hP hPU : Compacts U) : Set U) ⊆ P := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  exact hy

theorem integralCompactSubtypePreimage_image_eq (U P : Set X) (hP : IsCompact P)
    (hPU : P ⊆ U) :
    (integralOpenSubtypeVal U) ''
        ((integralCompactSubtypePreimage U P hP hPU : Compacts U) : Set U) = P := by
  apply Set.Subset.antisymm
  · exact integralCompactSubtypePreimage_image_subset U P hP hPU
  · intro y hy
    exact ⟨⟨y, hPU hy⟩, hy, rfl⟩

theorem exists_integralCompactSubtype_enlargement (U P : Set X) (hP : IsCompact P)
    (hPU : P ⊆ U) (K : Compacts U)
    (hKP : (integralOpenSubtypeVal U) '' (K : Set U) ⊆ P) :
    ∃ L : Compacts U, K ≤ L ∧
      (integralOpenSubtypeVal U) '' (L : Set U) ⊆ P := by
  refine ⟨integralCompactSubtypePreimage U P hP hPU, ?_,
    integralCompactSubtypePreimage_image_subset U P hP hPU⟩
  exact (integralCompactSubtypePreimage_le_iff U P hP hPU K).mpr hKP

theorem exists_integralCompact_union_refinement
    [T2Space X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (A : Compacts U) (B : Compacts V) (P : Compacts ↥(U ∪ V))
    (hA : A.map (integralOpenSubtypeUnionInclusion U V hU)
        (integralOpenSubtypeUnionInclusion U V hU).continuous ≤ P)
    (hB : B.map (integralOpenSubtypeUnionInclusionRight U V hV)
        (integralOpenSubtypeUnionInclusionRight U V hV).continuous ≤ P) :
    ∃ A' : Compacts U, ∃ B' : Compacts V,
      A ≤ A' ∧ B ≤ B' ∧
        A'.map (integralOpenSubtypeUnionInclusion U V hU)
            (integralOpenSubtypeUnionInclusion U V hU).continuous ⊔
          B'.map (integralOpenSubtypeUnionInclusionRight U V hV)
            (integralOpenSubtypeUnionInclusionRight U V hV).continuous = P := by
  let vW : C(↥(U ∪ V), X) := integralOpenSubtypeVal (U ∪ V)
  let PX : Compacts X := P.map vW vW.continuous
  have hPX : (PX : Set X) ⊆ U ∪ V := by
    intro x hx
    change x ∈ vW '' (P : Set ↥(U ∪ V)) at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.property
  obtain ⟨PU, PV, hPUc, hPVc, hPU, hPV, hPXeq⟩ :=
    PX.isCompact.binary_compact_cover hU hV hPX
  let A0 := integralCompactSubtypePreimage U PU hPUc hPU
  let B0 := integralCompactSubtypePreimage V PV hPVc hPV
  let A' := A ⊔ A0
  let B' := B ⊔ B0
  have hA0 : (A0.map (integralOpenSubtypeUnionInclusion U V hU)
      (integralOpenSubtypeUnionInclusion U V hU).continuous : Set ↥(U ∪ V)) ⊆ P := by
    intro y hy
    change y ∈ (integralOpenSubtypeUnionInclusion U V hU) '' (A0 : Set U) at hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxPU : (integralOpenSubtypeVal U) x ∈ PU := by
      exact integralCompactSubtypePreimage_image_subset U PU hPUc hPU ⟨x, hx, rfl⟩
    have hxPX : (x : X) ∈ PX := by
      change (x : X) ∈ (PX : Set X)
      rw [hPXeq]
      exact Or.inl hxPU
    change (x : X) ∈ vW '' (P : Set ↥(U ∪ V)) at hxPX
    rcases hxPX with ⟨p, hp, hpx⟩
    have hxp : (integralOpenSubtypeUnionInclusion U V hU) x = p :=
      Subtype.ext hpx.symm
    exact hxp ▸ hp
  have hB0 : (B0.map (integralOpenSubtypeUnionInclusionRight U V hV)
      (integralOpenSubtypeUnionInclusionRight U V hV).continuous : Set ↥(U ∪ V)) ⊆ P := by
    intro y hy
    change y ∈ (integralOpenSubtypeUnionInclusionRight U V hV) '' (B0 : Set V) at hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxPV : (integralOpenSubtypeVal V) x ∈ PV := by
      exact integralCompactSubtypePreimage_image_subset V PV hPVc hPV ⟨x, hx, rfl⟩
    have hxPX : (x : X) ∈ PX := by
      change (x : X) ∈ (PX : Set X)
      rw [hPXeq]
      exact Or.inr hxPV
    change (x : X) ∈ vW '' (P : Set ↥(U ∪ V)) at hxPX
    rcases hxPX with ⟨p, hp, hpx⟩
    have hxp : (integralOpenSubtypeUnionInclusionRight U V hV) x = p :=
      Subtype.ext hpx.symm
    exact hxp ▸ hp
  have hA' : (A'.map (integralOpenSubtypeUnionInclusion U V hU)
      (integralOpenSubtypeUnionInclusion U V hU).continuous : Set ↥(U ∪ V)) ⊆ P := by
    change (integralOpenSubtypeUnionInclusion U V hU) ''
      ((A : Set U) ∪ (A0 : Set U)) ⊆ P
    rw [Set.image_union]
    exact union_subset hA hA0
  have hB' : (B'.map (integralOpenSubtypeUnionInclusionRight U V hV)
      (integralOpenSubtypeUnionInclusionRight U V hV).continuous : Set ↥(U ∪ V)) ⊆ P := by
    change (integralOpenSubtypeUnionInclusionRight U V hV) ''
      ((B : Set V) ∪ (B0 : Set V)) ⊆ P
    rw [Set.image_union]
    exact union_subset hB hB0
  refine ⟨A', B', le_sup_left, le_sup_left, ?_⟩
  apply Compacts.ext
  apply Set.Subset.antisymm
  · rw [Compacts.coe_sup]
    exact union_subset hA' hB'
  · intro y hy
    have hpPX : (vW y : X) ∈ PX := ⟨y, hy, rfl⟩
    change (vW y : X) ∈ (PX : Set X) at hpPX
    rw [hPXeq] at hpPX
    change y ∈
      (integralOpenSubtypeUnionInclusion U V hU) '' (A' : Set U) ∪
        (integralOpenSubtypeUnionInclusionRight U V hV) '' (B' : Set V)
    rcases hpPX with hpU | hpV
    · let x : U := ⟨(y : X), hPU hpU⟩
      have hxA0 : x ∈ A0 := by
        change (x : X) ∈ PU
        exact hpU
      left
      exact ⟨x, Or.inr hxA0, Subtype.ext rfl⟩
    · let x : V := ⟨(y : X), hPV hpV⟩
      have hxB0 : x ∈ B0 := by
        change (x : X) ∈ PV
        exact hpV
      right
      exact ⟨x, Or.inr hxB0, Subtype.ext rfl⟩

end PoincareConjecture.Proofs.M02.Topology
