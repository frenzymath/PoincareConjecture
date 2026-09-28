import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarHalfspaceCuts
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedVertexIncidence










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Nontrivial F] [DecidableEq E]
  {ι κ : Type*} [Finite ι] [Nonempty ι] [Finite κ]





theorem AffineOnFaces.isFinitePLBallPair_conical_halfspaces
    {K : SimplicialComplex ℝ E} {f : E → F}
    (hf : K.AffineOnFaces f) (hK : K.faces.Finite) (hinj : InjOn f K.space)
    {p : E} (hp : p ∈ K.vertices) (hstar : K.closedStar p = K)
    (hfp : f p = 0) (hint : (0 : F) ∈ interior (f '' K.space))
    (c : F ≃L[ℝ] (ι → ℝ)) (A : κ → F →ₗ[ℝ] ℝ)
    (hpositive : ∃ v : F, ∀ j, 0 < A j v) :
    IsFinitePLBallPair F (K.space ∩ {x | ∀ j, 0 ≤ A j (f x)})
      {x | x ∈ K.space ∧ (∀ j, 0 ≤ A j (f x)) ∧
        (x ∈ (K.link p).space ∨ ∃ j, A j (f x) = 0)} := by
  classical
  let J := hf.embeddedImage hinj
  have hJ : J.faces.Finite := hf.embeddedImage_finite hinj hK
  have hJs : J.space = f '' K.space := hf.embeddedImage_space hinj
  have hJstar : (J.closedStar 0).space = J.space := by
    have h := hf.embeddedImage_closedStar_space hinj hp
    change (J.closedStar (f p)).space = f '' (K.closedStar p).space at h
    simpa only [hfp, hstar, ← hJs] using h
  have hJlink : (J.link 0).space = f '' (K.link p).space := by
    have h := hf.embeddedImage_link_space hinj hp
    change (J.link (f p)).space = f '' (K.link p).space at h
    simpa only [hfp] using h
  have hzJ : (0 : F) ∈ J.vertices := by
    rw [hf.embeddedImage_vertices hinj]
    exact ⟨p, hp, hfp⟩
  have hball := J.isFinitePLBallPair_closedStar_halfspace_cuts hJ hzJ
    (hJs.symm ▸ hint) c A hpositive
  rw [hJstar] at hball
  let Q : Set F := {x | ∀ j, 0 ≤ A j x}
  let T := J.space ∩ Q
  let g : F → E := Function.invFunOn f K.space
  have hleft : LeftInvOn g f K.space := hinj.leftInvOn_invFunOn
  have hback (x : F) (hx : x ∈ J.space) : g x ∈ K.space ∧ f (g x) = x := by
    obtain ⟨y, hy, rfl⟩ := hJs.subset hx
    rw [hleft hy]
    exact ⟨hy, rfl⟩
  have hg : FinitePiecewiseAffineOn g J.space :=
    (hf.invFunOn_embeddedImage hinj).finitePiecewiseAffineOn hJ
  have hginj : InjOn g J.space := by
    intro x hx y hy hxy
    exact (hback x hx).2.symm.trans ((congrArg f hxy).trans (hback y hy).2)
  have hsource : g '' (J.space ∩ {x | ∀ j, 0 ≤ A j x}) =
      K.space ∩ {x | ∀ j, 0 ≤ A j (f x)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(hback y hy.1).1, ?_⟩
      intro j
      rw [(hback y hy.1).2]
      exact hy.2 j
    · intro hx
      refine ⟨f x, ⟨hJs.symm.subset (mem_image_of_mem f hx.1), hx.2⟩, hleft hx.1⟩
  have hlinksub : (K.link p).space ⊆ K.space :=
    space_subset_of_le (fun _ hs => hs.1)
  have hrim : g '' {x | x ∈ J.space ∧ (∀ j, 0 ≤ A j x) ∧
      (x ∈ (J.link 0).space ∨ ∃ j, A j x = 0)} =
      {x | x ∈ K.space ∧ (∀ j, 0 ≤ A j (f x)) ∧
        (x ∈ (K.link p).space ∨ ∃ j, A j (f x) = 0)} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hgy := hback y hy.1
      refine ⟨hgy.1, ?_, ?_⟩
      · intro j
        simpa only [hgy.2] using hy.2.1 j
      · rcases hy.2.2 with hylink | ⟨j, hj⟩
        · obtain ⟨z, hz, hzy⟩ := hJlink.subset hylink
          left
          rw [← hzy, hleft (hlinksub hz)]
          exact hz
        · exact Or.inr ⟨j, by simpa only [hgy.2] using hj⟩
    · rintro ⟨hxK, hxQ, hxr⟩
      refine ⟨f x, ⟨hJs.symm.subset (mem_image_of_mem f hxK), hxQ, ?_⟩, hleft hxK⟩
      rcases hxr with hxlink | hxplane
      · exact Or.inl (hJlink.symm.subset (mem_image_of_mem f hxlink))
      · exact Or.inr hxplane
  have hresult := hball.image_of_subset hg (show T ⊆ J.space from inter_subset_left) hginj
  simpa only [hsource, hrim] using hresult

end Geometry.SimplicialComplex
