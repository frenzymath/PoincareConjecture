import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.OriginalRectangleBoundaryCover









set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt.OriginalFaceRectangles

theorem exists_cap_page
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} {g : E → X} {S : Set X} {s : Finset E}
    (D : OriginalFaceRectangles K g S s) (k : D.Region) (b : Bool) :
    ∃ N n : Set E, IsFinitePLBallPair (ℝ × ℝ) N n ∧ N ⊆ D.carrier k ∧
      D.arc (D.cap k b) ⊆ n ∧ N ∩ (⋃ i, D.arc i) = D.arc (D.cap k b) := by
  classical
  obtain ⟨G,hG,hW,hZ,_,_⟩ := D.rectangle k
  obtain ⟨f,hf,hfG⟩ := hG
  let a : ℝ := if b then 1/2 else 0
  let c : ℝ := if b then 1 else 1/2
  let P : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc a c
  have hac : a < c := by cases b <;> norm_num [a,c]
  have hsub : P ⊆ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) := by
    intro x hx
    refine ⟨hx.1,?_⟩
    have h0 : 0 ≤ a := by cases b <;> norm_num [a]
    have h1 : c ≤ 1 := by cases b <;> norm_num [c]
    exact ⟨h0.trans hx.2.1,hx.2.2.trans h1⟩
  have hfi : InjOn f (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1 : Set (ℝ × ℝ)) := by
    intro x hx y hy he
    have heq : G ⟨x,hx⟩ = G ⟨y,hy⟩ := Subtype.ext
      ((hfG ⟨x,hx⟩).trans (he.trans (hfG ⟨y,hy⟩).symm))
    exact congrArg Subtype.val (G.injective heq)
  have hP := (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)).prod
    (isFinitePLBallPair_Icc hac)
  have hN := hP.image_of_subset hf hsub hfi
  refine ⟨f '' P,f '' (({0,1} ×ˢ Icc a c) ∪ (Icc 0 1 ×ˢ {a,c})),hN,?_,?_,?_⟩
  · rintro x ⟨y,hy,rfl⟩
    rw [←hfG ⟨y,hsub hy⟩]
    exact (G ⟨y,hsub hy⟩).property
  · intro x hx
    have hxM : x ∈ D.carrier k := (D.regionBall k).1 (Or.inl (by
      cases b
      · exact Or.inl hx
      · exact Or.inr hx))
    let y := G.symm ⟨x,hxM⟩
    have hyx : f (y : ℝ × ℝ) = x := (hfG y).symm.trans (congrArg Subtype.val (G.apply_symm_apply _))
    have hycap : (y : ℝ × ℝ).2 = if b then 1 else 0 := by
      cases b
      · apply (hW y).mp
        exact (congrArg Subtype.val (G.apply_symm_apply _)).symm ▸ hx
      · apply (hZ y).mp
        exact (congrArg Subtype.val (G.apply_symm_apply _)).symm ▸ hx
    refine ⟨y,Or.inr ⟨y.property.1,?_⟩,hyx⟩
    rw [hycap]
    cases b <;> simp [a,c]
  · ext x
    constructor
    · rintro ⟨⟨y,hy,rfl⟩,hycut⟩
      have hyM : f y ∈ D.carrier k := (hfG ⟨y,hsub hy⟩) ▸ (G ⟨y,hsub hy⟩).property
      have hends := (D.cutContact k).subset ⟨hyM,hycut⟩
      have hy0 (h : f y ∈ D.arc (D.cap k false)) : y.2 = 0 :=
        (hW ⟨y,hsub hy⟩).mp ((hfG ⟨y,hsub hy⟩).symm ▸ h)
      have hy1 (h : f y ∈ D.arc (D.cap k true)) : y.2 = 1 :=
        (hZ ⟨y,hsub hy⟩).mp ((hfG ⟨y,hsub hy⟩).symm ▸ h)
      cases b
      · rcases hends with hw | hz
        · exact hw
        · have hle : y.2 ≤ 1/2 := hy.2.2
          rw [hy1 hz] at hle
          norm_num at hle
      · rcases hends with hw | hz
        · have hle : 1/2 ≤ y.2 := hy.2.1
          rw [hy0 hw] at hle
          norm_num at hle
        · exact hz
    · intro hx
      have hxM : x ∈ D.carrier k := (D.regionBall k).1 (Or.inl (by
        cases b
        · exact Or.inl hx
        · exact Or.inr hx))
      let y := G.symm ⟨x,hxM⟩
      have hyx : f (y : ℝ × ℝ) = x := (hfG y).symm.trans (congrArg Subtype.val (G.apply_symm_apply _))
      have hycap : (y : ℝ × ℝ).2 = if b then 1 else 0 := by
        cases b
        · exact (hW y).mp ((congrArg Subtype.val (G.apply_symm_apply _)).symm ▸ hx)
        · exact (hZ y).mp ((congrArg Subtype.val (G.apply_symm_apply _)).symm ▸ hx)
      refine ⟨⟨y,⟨y.property.1,?_⟩,hyx⟩,mem_iUnion.mpr ⟨D.cap k b,hx⟩⟩
      change a ≤ (y : ℝ × ℝ).2 ∧ (y : ℝ × ℝ).2 ≤ c
      rw [hycap]
      cases b <;> norm_num [a,c]

end PoincareConjecture.M76.PrismBelt.OriginalFaceRectangles
