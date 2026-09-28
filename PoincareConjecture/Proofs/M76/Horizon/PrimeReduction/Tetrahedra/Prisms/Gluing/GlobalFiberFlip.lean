import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Tetrahedra.Prisms.Belts.RectangleCornerModels
import PoincareConjecture.Proofs.M76.Mathlib.NestedPLBallBoundary

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76.PrismBelt
local notation "I" => Icc (0 : ℝ) 1
local notation "Square" => (I ×ˢ I : Set (ℝ × ℝ))

def fiberFlip (b : Bool) : I ≃ₜ I :=
  if b then unitInterval.symmHomeomorph else Homeomorph.refl I

@[simp] theorem fiberFlip_false (t : I) : fiberFlip false t = t := rfl
@[simp] theorem fiberFlip_true (t : I) : fiberFlip true t = unitInterval.symm t := rfl
@[simp] theorem fiberFlip_apply_apply (b : Bool) (t : I) : fiberFlip b (fiberFlip b t) = t := by
  cases b
  · rfl
  · exact unitInterval.symm_symm t

theorem fiberFlip_finitePL (b : Bool) : (fiberFlip b).IsFinitePL := by
  obtain ⟨K,_,hK,hKs,_,_⟩ :=
    (isFinitePLBallPair_Icc (show (0 : ℝ) < 1 from zero_lt_one)).exists_finite_carrier_and_rim_complexes
  cases b
  · exact Homeomorph.isFinitePL_setCongr rfl K hK hKs
  · let f : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.const ℝ ℝ 1 - ContinuousAffineMap.id ℝ ℝ
    exact ⟨f,⟨K,hK,hKs,K.affineOnFaces_affine f⟩,fun _ => rfl⟩

def rectangleFiberFlip (b : Bool) : Square ≃ₜ Square :=
  (Homeomorph.Set.prod I I).trans
    (((Homeomorph.refl I).prodCongr (fiberFlip b)).trans (Homeomorph.Set.prod I I).symm)

theorem rectangleFiberFlip_finitePL (b : Bool) : (rectangleFiberFlip b).IsFinitePL :=
  (fiberFlip_finitePL false).prod (fiberFlip_finitePL b)

@[simp] theorem rectangleFiberFlip_false (x : Square) : rectangleFiberFlip false x = x := by
  apply Subtype.ext
  exact Prod.ext rfl rfl

@[simp] theorem rectangleFiberFlip_apply (b : Bool) (u t : I) :
    rectangleFiberFlip b ⟨(u,t),u.property,t.property⟩ =
      ⟨(u,fiberFlip b t),u.property,(fiberFlip b t).property⟩ := rfl

@[simp] theorem fiberFlip_zero (b : Bool) :
    (fiberFlip b 0 : ℝ) = if b then 1 else 0 := by
  cases b
  · rfl
  · change (1 : ℝ) - 0 = 1
    ring

@[simp] theorem fiberFlip_one (b : Bool) :
    (fiberFlip b 1 : ℝ) = if b then 0 else 1 := by
  cases b
  · rfl
  · change (1 : ℝ) - 1 = 0
    ring

end PoincareConjecture.M76.PrismBelt
