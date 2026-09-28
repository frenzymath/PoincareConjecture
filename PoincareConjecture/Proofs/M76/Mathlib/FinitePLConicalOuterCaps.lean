import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarCoordinateCaps
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLConicalHalfBlocks









set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]





theorem AffineOnFaces.isFinitePLBallPair_conical_outer_caps
    {K : SimplicialComplex ℝ E} {f : E → ((ℝ × ℝ) × ℝ)}
    (hf : K.AffineOnFaces f) (hK : K.faces.Finite) (hinj : InjOn f K.space)
    {p : E} (hp : p ∈ K.vertices) (hfp : f p = 0)
    (hint : (0 : (ℝ × ℝ) × ℝ) ∈ interior (f '' K.space))
    (c : ((ℝ × ℝ) × ℝ) ≃L[ℝ] (Fin 3 → ℝ)) :
    (∀ j : Bool, IsFinitePLBallPair (ℝ × ℝ)
      ((K.link p).space ∩ {x | if j then (f x).2 ≤ 0 else 0 ≤ (f x).2})
      ((K.link p).space ∩ {x | (f x).2 = 0})) ∧
    ∀ i j : Bool, IsFinitePLBallPair (ℝ × ℝ)
      ((K.link p).space ∩ {x | (if i then (f x).1.1 ≤ 0 else 0 ≤ (f x).1.1) ∧
        (if j then (f x).2 ≤ 0 else 0 ≤ (f x).2)})
      (((K.link p).space ∩ {x | (f x).1.1 = 0 ∧
        (if j then (f x).2 ≤ 0 else 0 ≤ (f x).2)}) ∪
        ((K.link p).space ∩ {x | (f x).2 = 0 ∧
          (if i then (f x).1.1 ≤ 0 else 0 ≤ (f x).1.1)})) := by
  classical
  let J := hf.embeddedImage hinj
  have hJ : J.faces.Finite := hf.embeddedImage_finite hinj hK
  have hJs : J.space = f '' K.space := hf.embeddedImage_space hinj
  have hJlink : (J.link 0).space = f '' (K.link p).space := by
    have h := hf.embeddedImage_link_space hinj hp
    change (J.link (f p)).space = f '' (K.link p).space at h
    simpa only [hfp] using h
  have hzJ : (0 : (ℝ × ℝ) × ℝ) ∈ J.vertices := by
    rw [hf.embeddedImage_vertices hinj]
    exact ⟨p, hp, hfp⟩
  obtain ⟨hcaps, hquads⟩ := J.isFinitePLBallPair_closedStar_coordinate_caps
    hJ hzJ (hJs.symm ▸ hint) c
  let g : ((ℝ × ℝ) × ℝ) → E := Function.invFunOn f K.space
  have hleft : LeftInvOn g f K.space := hinj.leftInvOn_invFunOn
  have hback (x : (ℝ × ℝ) × ℝ) (hx : x ∈ J.space) :
      g x ∈ K.space ∧ f (g x) = x := by
    obtain ⟨y, hy, rfl⟩ := hJs.subset hx
    rw [hleft hy]
    exact ⟨hy, rfl⟩
  have hg : FinitePiecewiseAffineOn g J.space :=
    (hf.invFunOn_embeddedImage hinj).finitePiecewiseAffineOn hJ
  have hginj : InjOn g J.space := by
    intro x hx y hy hxy
    exact (hback x hx).2.symm.trans ((congrArg f hxy).trans (hback y hy).2)
  have hlinksub : (K.link p).space ⊆ K.space :=
    space_subset_of_le (fun _ hs => hs.1)
  have hJlinksub : (J.link 0).space ⊆ J.space :=
    space_subset_of_le (fun _ hs => hs.1)
  have himage (P : ((ℝ × ℝ) × ℝ) → Prop) :
      g '' ((J.link 0).space ∩ {x | P x}) =
        (K.link p).space ∩ {x | P (f x)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, hzy⟩ := hJlink.subset hy.1
      refine ⟨?_, ?_⟩
      · rw [← hzy, hleft (hlinksub hz)]
        exact hz
      · change P (f (g y))
        rw [(hback y (hJlinksub hy.1)).2]
        exact hy.2
    · intro hx
      exact ⟨f x, ⟨hJlink.symm.subset (mem_image_of_mem f hx.1), hx.2⟩,
        hleft (hlinksub hx.1)⟩
  have hpull (P Q : ((ℝ × ℝ) × ℝ) → Prop)
      (hb : IsFinitePLBallPair (ℝ × ℝ)
        ((J.link 0).space ∩ {x | P x}) ((J.link 0).space ∩ {x | Q x})) :
      IsFinitePLBallPair (ℝ × ℝ)
        ((K.link p).space ∩ {x | P (f x)})
        ((K.link p).space ∩ {x | Q (f x)}) := by
    have hr := hb.image_of_subset hg
      (show (J.link 0).space ∩ {x | P x} ⊆ J.space from
        fun _ hx => hJlinksub hx.1) hginj
    simpa only [himage P, himage Q] using hr
  refine ⟨fun j => hpull _ _ (hcaps j), ?_⟩
  intro i j
  let P : ((ℝ × ℝ) × ℝ) → Prop := fun x =>
    (if i then x.1.1 ≤ 0 else 0 ≤ x.1.1) ∧ (if j then x.2 ≤ 0 else 0 ≤ x.2)
  let Q : ((ℝ × ℝ) × ℝ) → Prop := fun x =>
    (x.1.1 = 0 ∧ (if j then x.2 ≤ 0 else 0 ≤ x.2)) ∨
      (x.2 = 0 ∧ (if i then x.1.1 ≤ 0 else 0 ≤ x.1.1))
  have hq := hquads i j
  have hrim :
      ((J.link 0).space ∩ {x | x.1.1 = 0 ∧ (if j then x.2 ≤ 0 else 0 ≤ x.2)}) ∪
        ((J.link 0).space ∩ {x | x.2 = 0 ∧ (if i then x.1.1 ≤ 0 else 0 ≤ x.1.1)}) =
        (J.link 0).space ∩ {x | Q x} := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq, Q]
    tauto
  rw [hrim] at hq
  have htarget :
      ((K.link p).space ∩ {x | (f x).1.1 = 0 ∧
        (if j then (f x).2 ≤ 0 else 0 ≤ (f x).2)}) ∪
        ((K.link p).space ∩ {x | (f x).2 = 0 ∧
          (if i then (f x).1.1 ≤ 0 else 0 ≤ (f x).1.1)}) =
        (K.link p).space ∩ {x | Q (f x)} := by
    ext x
    simp only [mem_union, mem_inter_iff, mem_ofPred_eq, Q]
    tauto
  rw [htarget]
  exact hpull P Q hq

end Geometry.SimplicialComplex
