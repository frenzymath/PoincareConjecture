import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Neighborhood.Disks.RimBands.Collar.TangentPLFactorization
import PoincareConjecture.Proofs.M76.Brown.NormalPairAtlas







set_option autoImplicit false

open Set Geometry SignType

namespace PoincareConjecture.M76.Dehn.Annuli.RimBands

local notation "P2" => (ℝ × ℝ)
local notation "C3" => (P2 × ℝ)

private theorem zero_inverse (h : OpenPartialHomeomorph C3 C3)
    (hpair : ∀ z ∈ h.source, (h z).2 = 0 ↔ z.2 = 0)
    (z : C3) (hz : z ∈ h.target) (hz0 : z.2 = 0) : (h.symm z).2 = 0 := by
  apply (hpair _ (h.map_target hz)).mp
  rwa [h.right_inv hz]


def tangentialTransition (h : OpenPartialHomeomorph C3 C3)
    (hpair : ∀ z ∈ h.source, (h z).2 = 0 ↔ z.2 = 0) :
    OpenPartialHomeomorph P2 P2 where
  toFun z := (h (z, 0)).1
  invFun z := (h.symm (z, 0)).1
  source := (fun z : P2 => (z, (0 : ℝ))) ⁻¹' h.source
  target := (fun z : P2 => (z, (0 : ℝ))) ⁻¹' h.target
  map_source' := by
    intro z hz
    change ((h (z, 0)).1, (0 : ℝ)) ∈ h.target
    have he : ((h (z, 0)).1, (0 : ℝ)) = h (z, 0) :=
      Prod.ext rfl ((hpair _ hz).mpr rfl).symm
    rw [he]
    exact h.map_source hz
  map_target' := by
    intro z hz
    change ((h.symm (z, 0)).1, (0 : ℝ)) ∈ h.source
    have he : ((h.symm (z, 0)).1, (0 : ℝ)) = h.symm (z, 0) :=
      Prod.ext rfl (zero_inverse h hpair _ hz rfl).symm
    rw [he]
    exact h.map_target hz
  left_inv' := by
    intro z hz
    have he : ((h (z, 0)).1, (0 : ℝ)) = h (z, 0) :=
      Prod.ext rfl ((hpair _ hz).mpr rfl).symm
    change (h.symm ((h (z, 0)).1, 0)).1 = z
    rw [he, h.left_inv hz]
  right_inv' := by
    intro z hz
    have he : ((h.symm (z, 0)).1, (0 : ℝ)) = h.symm (z, 0) :=
      Prod.ext rfl (zero_inverse h hpair _ hz rfl).symm
    change (h ((h.symm (z, 0)).1, 0)).1 = z
    rw [he, h.right_inv hz]
  open_source := h.open_source.preimage (continuous_id.prodMk continuous_const)
  open_target := h.open_target.preimage (continuous_id.prodMk continuous_const)
  continuousOn_toFun :=
    (h.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hz => hz)).fst
  continuousOn_invFun :=
    (h.symm.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hz => hz)).fst

theorem tangentialTransition_plane (h : OpenPartialHomeomorph C3 C3)
    (hpair : ∀ z ∈ h.source, (h z).2 = 0 ↔ z.2 = 0)
    (z : P2) (hz : (z, (0 : ℝ)) ∈ h.source) :
    h (z, 0) = (tangentialTransition h hpair z, 0) :=
  Prod.ext rfl ((hpair _ hz).mpr rfl)

theorem tangentialTransition_mem_piecewiseAffineGroupoid
    (h : OpenPartialHomeomorph C3 C3)
    (hh : h ∈ piecewiseAffineGroupoid C3)
    (hpair : ∀ z ∈ h.source, (h z).2 = 0 ↔ z.2 = 0) :
    tangentialTransition h hpair ∈ piecewiseAffineGroupoid P2 := by
  let incl : P2 →ᴬ[ℝ] C3 :=
    (ContinuousAffineMap.id ℝ P2).prod (ContinuousAffineMap.const ℝ P2 0)
  let proj : C3 →ᴬ[ℝ] P2 :=
    (ContinuousLinearMap.fst ℝ P2 ℝ).toContinuousAffineMap
  have hincl := locallyPiecewiseAffineOn_affine incl isOpen_univ
  have hproj := locallyPiecewiseAffineOn_affine proj isOpen_univ
  constructor
  · exact ((hproj.comp (hh.1.comp hincl)).mono
      (tangentialTransition h hpair).open_source
      (fun z hz => ⟨⟨mem_univ _, hz⟩, mem_univ _⟩))
  · exact ((hproj.comp (hh.2.comp hincl)).mono
      (tangentialTransition h hpair).open_target
      (fun z hz => ⟨⟨mem_univ _, hz⟩, mem_univ _⟩))

variable {X ι : Type*} [TopologicalSpace X] {S : Set X}


def atlasTangentialTransition (A : BrownCollar.FlatteningAtlas P2 S ι) (i j : ι) :
    OpenPartialHomeomorph P2 P2 :=
  tangentialTransition (A.transition i j) (A.transition_pair i j)

theorem atlasTangentialTransition_base
    (A : BrownCollar.FlatteningAtlas P2 S ι) (i j : ι) (x : S)
    (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    atlasTangentialTransition A i j (A.coordinate i x) = A.coordinate j x := by
  have he := congrArg (fun z : C3 => z.1) (A.transition_base i j x hx)
  exact he

theorem atlasTransition_sign_factorization
    (A : BrownCollar.FlatteningAtlas P2 S ι) (i j : ι)
    (hPL : A.transition i j ∈ piecewiseAffineGroupoid C3)
    (x : S) (hx : x ∈ A.baseSet i ∩ A.baseSet j) :
    plLocalSign (A.transition i j) hPL
      ⟨(A.coordinate i x, 0), A.transition_mem_source i j x hx⟩ =
      plLocalSign (atlasTangentialTransition A i j)
        (tangentialTransition_mem_piecewiseAffineGroupoid _ hPL _)
        ⟨A.coordinate i x, A.transition_mem_source i j x hx⟩ *
      A.transitionSign i j x := by
  rw [BrownCollar.FlatteningAtlas.transitionSign, dif_pos hx]
  exact plLocalSign_eq_tangentialPL_mul_normalTransitionSign
    (A.transition i j) hPL (A.transition_pair i j)
    (atlasTangentialTransition A i j)
    (tangentialTransition_mem_piecewiseAffineGroupoid _ hPL _)
    (fun z _ hz => tangentialTransition_plane _ _ z hz)
    ⟨A.coordinate i x, A.transition_mem_source i j x hx⟩
    (A.transition_mem_source i j x hx)

end PoincareConjecture.M76.Dehn.Annuli.RimBands
