import PoincareConjecture.Proofs.M38.ProjectiveDoubleBoundary

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

private instance cylinderNonempty : Nonempty RoundCylinderSpace := by
  let : Nonempty UnitTwoSphere :=
    (isConnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp))
      (0 : EuclideanSpace ℝ (Fin 3)) (zero_le_one : (0 : ℝ) ≤ 1)).nonempty.to_subtype
  infer_instance

variable {Q : Type*} [TopologicalSpace Q]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Q]
  (C : SmoothProjectiveDoubleModel Q)

noncomputable def projectiveDoubleCollarInverse : Q → RoundCylinderSpace :=
  Function.invFunOn C.collar (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)

theorem projectiveDoubleCollarInverse_left :
    Set.LeftInvOn (projectiveDoubleCollarInverse C) C.collar
      (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
  C.collar_injective.leftInvOn_invFunOn

theorem projectiveDoubleCollarInverse_mem {y : Q}
    (hy : y ∈ C.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) :
    projectiveDoubleCollarInverse C y ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
  Function.invFunOn_mem hy

theorem projectiveDoubleCollarInverse_right :
    Set.LeftInvOn C.collar (projectiveDoubleCollarInverse C)
      (C.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) :=
  fun _ hy => Function.invFunOn_eq hy

theorem projectiveDoubleCollarInverse_smooth :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (projectiveDoubleCollarInverse C)
      (C.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)) := by
  rintro y ⟨x, hx, hxy⟩
  let hlocal := C.collar_local_diffeomorph ⟨x, hx⟩
  let s := hlocal.localInverse
  have hy : y ∈ s.source := hxy ▸ hlocal.localInverse_mem_source
  have hsy : s y = x := by
    rw [← hxy]
    exact hlocal.localInverse_left_inv hlocal.localInverse_mem_target
  have hs : ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ s y :=
    hlocal.contmdiffOn_localInverse.contMDiffAt (s.open_source.mem_nhds hy)
  have hD : IsOpen ((Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    isOpen_univ.prod isOpen_Ioo
  have hsd : s y ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 := hsy ▸ hx
  have hn : ∀ᶠ z in 𝓝 y, s z ∈ Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1 :=
    hs.continuousAt.preimage_mem_nhds (hD.mem_nhds hsd)
  apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [s.open_source.mem_nhds hy, hn] with z hz hsz
  have hzimage : z ∈ C.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1) :=
    ⟨s z, hsz, hlocal.localInverse_right_inv hz⟩
  apply C.collar_injective (projectiveDoubleCollarInverse_mem C hzimage) hsz
  rw [projectiveDoubleCollarInverse_right C hzimage, hlocal.localInverse_right_inv hz]

noncomputable def projectiveDoubleCollarChart :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) RoundCylinderSpace Q ∞ where
  toFun := C.collar
  invFun := projectiveDoubleCollarInverse C
  source := Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1
  target := C.collar '' (Set.univ ×ˢ Set.Ioo (-1 : ℝ) 1)
  map_source' := fun _ hx => Set.mem_image_of_mem C.collar hx
  map_target' := fun {_} hy => projectiveDoubleCollarInverse_mem C hy
  left_inv' := projectiveDoubleCollarInverse_left C
  right_inv' := projectiveDoubleCollarInverse_right C
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := C.collar_open
  contMDiffOn_toFun := C.collar_local_diffeomorph.contMDiffOn
  contMDiffOn_invFun := projectiveDoubleCollarInverse_smooth C

end PoincareConjecture.M38
