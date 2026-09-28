import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionPLLocalInterior
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalFrontier
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLCoordinates











set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]





theorem FinitePiecewiseAffineOn.exists_open_topFace_image
    {f : E → X × ℝ} {S : Set E} {D : Set X}
    (hf : FinitePiecewiseAffineOn f S)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ X) (hinj : InjOn f S)
    (hmap : MapsTo f S (frontier (D ×ˢ Icc (-1 : ℝ) 1)))
    {x : E} (hx : x ∈ interior S) (hxD : (f x).1 ∈ interior D)
    (hxtop : (f x).2 = 1) :
    ∃ U : Set X, IsOpen U ∧ (f x).1 ∈ U ∧ U ⊆ interior D ∧
      U ×ˢ {(1 : ℝ)} ⊆ f '' S := by
  let V := interior S ∩ f ⁻¹' (interior D ×ˢ Ioi (0 : ℝ))
  have hV : IsOpen V := (hf.continuousOn.mono interior_subset).isOpen_inter_preimage
    isOpen_interior (isOpen_interior.prod isOpen_Ioi)
  have hxV : x ∈ V := ⟨hx, hxD, by rw [hxtop]; norm_num⟩
  obtain ⟨K, hK, hcv, hxK, hKV⟩ := hV.exists_finite_convex_neighborhood hxV
  have hKS : K.space ⊆ S := fun y hy => interior_subset (hKV hy).1
  have htop (y : E) (hy : y ∈ K.space) : (f y).2 = 1 := by
    let z : frontier (D ×ˢ Icc (-1 : ℝ) 1) := ⟨f y, hmap (hKS hy)⟩
    have hband := Set.ext_iff.mp
      (preimage_top_face_eq_preimage_positive_band (Subset.rfl : interior D ⊆ interior D)) z
    exact ((hband.mpr (hKV hy).2).2 : (f y).2 ∈ ({1} : Set ℝ))
  let a := (ContinuousLinearMap.fst ℝ X ℝ).toContinuousAffineMap
  have hfst : FinitePiecewiseAffineOn (a ∘ f) K.space := (hf.restrict K hK hKS).postcomp a
  have hfstinj : InjOn (a ∘ f) K.space := by
    intro y hy z hz he
    apply hinj (hKS hy) (hKS hz)
    exact Prod.ext he ((htop y hy).trans (htop z hz).symm)
  have hxi : (f x).1 ∈ interior ((a ∘ f) '' K.space) :=
    hfst.mem_interior_image_of_convex hcv hdim hfstinj hxK
  let U := interior ((a ∘ f) '' K.space) ∩ interior D
  refine ⟨U, isOpen_interior.inter isOpen_interior, ⟨hxi, hxD⟩,
    inter_subset_right, ?_⟩
  rintro ⟨y, t⟩ ⟨hy, ht⟩
  have ht' : t = 1 := ht
  obtain ⟨z, hz, hzy⟩ := interior_subset hy.1
  exact ⟨z, hKS hz, Prod.ext hzy ((htop z hz).trans ht'.symm)⟩

end Geometry

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X]





theorem IsFinitePLBallPair.mem_interior_preimage_cylinder
    {s b : Set (X × ℝ)} {D : Set X} (hs : IsFinitePLBallPair E s b)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ X)
    (hsub : s ⊆ frontier (D ×ˢ Icc (-1 : ℝ) 1))
    (p : frontier (D ×ˢ Icc (-1 : ℝ) 1)) (hp : (p : X × ℝ) ∈ s \ b)
    (hpD : (p : X × ℝ).1 ∈ interior D) (hptop : (p : X × ℝ).2 = 1) :
    p ∈ interior ((Subtype.val : frontier (D ×ˢ Icc (-1 : ℝ) 1) → X × ℝ) ⁻¹' s) := by
  obtain ⟨_, C, _, _, _, e, he, heb⟩ := hs
  obtain ⟨f, hf, hfv⟩ := he.symm
  have hinj : InjOn f C := by
    intro x hx y hy hxy
    have h : e.symm ⟨x, hx⟩ = e.symm ⟨y, hy⟩ :=
      Subtype.ext ((hfv ⟨x, hx⟩).trans (hxy.trans (hfv ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (e.symm.injective h)
  have hmap : MapsTo f C (frontier (D ×ˢ Icc (-1 : ℝ) 1)) := by
    intro x hx
    rw [← hfv ⟨x, hx⟩]
    exact hsub (e.symm ⟨x, hx⟩).property
  let y : C := e ⟨p, hp.1⟩
  have hy : (y : E) ∈ interior C := by
    by_contra hnot
    exact hp.2 ((heb ⟨p, hp.1⟩).mpr ⟨subset_closure y.property, hnot⟩)
  have hfy : f y = (p : X × ℝ) := by
    rw [← hfv y]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨p, hp.1⟩)
  obtain ⟨U, hU, hpU, hUD, hUimage⟩ := hf.exists_open_topFace_image hdim hinj hmap
    hy (hfy.symm ▸ hpD) (hfy.symm ▸ hptop)
  have hUs : U ×ˢ {(1 : ℝ)} ⊆ s := by
    intro x hx
    obtain ⟨z, hz, hzx⟩ := hUimage hx
    rw [← hzx, ← hfv ⟨z, hz⟩]
    exact (e.symm ⟨z, hz⟩).property
  apply interior_maximal (preimage_mono hUs) (isOpen_preimage_top_face hU hUD)
  exact ⟨by simpa only [hfy] using hpU, hptop⟩

end Set
