import PoincareConjecture.Proofs.M38.SchoenfliesPort.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Caps.ReflectedGeometry







open _root_.AddCircle
open _root_.Poincare
open _root_.Poincare.Manifold
open _root_.Poincare.Manifold.Schoenflies
open _root_.Poincare.Manifold.Schoenflies.SaddleLevel
open _root_.PoincareConjecture

namespace M38Schoenflies


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Caps
open Poincare.Geometry.Euclidean PlaneArcs.Terminal.Reflection
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

variable {f : S2 → E3} (M : SphereMorseReduction f) {g : S2 → E3}
    (P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g)
    (p : S2) (e : OpenPartialHomeomorph E2 S2)
    (d : OrientationReview.TerminalSaddleGeometry M P p e)
    (R : SphereMorseReduction M.reflectedOriginal) (hv : R.v = M.v)
    (Q : SphereSurgeryPath (R.v : E3) (fun q => R.D (M.reflectedOriginal q))
      (heightReflection (mem_sphere_zero_iff_norm.mp M.v.property) ∘ g))
    (A : SphereSurgeryCoreCap.AnnularEndFamily (R.v : E3)
      (heightReflection (mem_sphere_zero_iff_norm.mp M.v.property) ∘ g)
      ((fun q => inner Real (R.v : E3) (R.D (M.reflectedOriginal q))) ''
        {q | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (R.v : E3) (R.D (M.reflectedOriginal y))) q = 0}) Q.core)
    (hl : A.lowerCut = -d.ends.upperCut) (hu : A.upperCut = -d.ends.lowerCut)
    (L : d.ends.EndIndex ≃ A.EndIndex)

local notation "G" => reflectedGeometry M P p e d R hv Q A hl hu L
local notation "J" => heightReflection (mem_sphere_zero_iff_norm.mp M.v.property)

theorem reflectedGeometry_flatten (y : E3) : (G).flatten y = Rz (d.flatten (J y)) := by
  simp only [TerminalSaddleGeometry.flatten, reflectedGeometry, Diffeomorph.coe_trans,
    comp_apply, heightReflection_heightReflection]

theorem reflectedGeometry_flatten_leaf (q : S2) :
    (G).flatten ((J ∘ g) q) = Rz (d.flatten (g q)) := by
  rw [reflectedGeometry_flatten]
  simp only [comp_apply, heightReflection_heightReflection]

theorem reflectedGeometry_filledModel (y : E3) : (G).filledModel y = J (d.filledModel y) := by
  simp only [TerminalSaddleGeometry.filledModel, reflectedGeometry, Diffeomorph.coe_trans,
    comp_apply, Rz_involutive]

theorem reflectedGeometry_flatten_model (y : E3) :
    (G).flatten ((G).filledModel y) = Rz (d.flatten (d.filledModel y)) := by
  rw [reflectedGeometry_flatten, reflectedGeometry_filledModel,
    heightReflection_heightReflection]

theorem reflectedGeometry_mem_I (z : Real) : z ∈ (G).I ↔ -z ∈ d.I := by
  change (A.lowerCut ≤ z ∧ z ≤ A.upperCut) ↔
    (d.ends.lowerCut ≤ -z ∧ -z ≤ d.ends.upperCut)
  rw [hl, hu]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem reflectedGeometry_actual_image :
    (G).flatten '' range (J ∘ g) = Rz '' (d.flatten '' range g) := by
  rw [← image_univ, ← image_univ, image_image, image_image, image_image]
  apply image_congr
  intro q _
  exact reflectedGeometry_flatten_leaf M P p e d R hv Q A hl hu L q

theorem reflectedGeometry_model_image :
    (G).flatten '' ((G).filledModel '' sphere (0 : E3) 1) =
      Rz '' (d.flatten '' (d.filledModel '' sphere (0 : E3) 1)) := by
  simp only [image_image]
  apply image_congr
  intro y _
  exact reflectedGeometry_flatten_model M P p e d R hv Q A hl hu L y

theorem reflectedGeometry_A (z : Real) : (G).A z = d.A (-z) := by
  ext x
  change Saddle.toE3 x z ∈ (G).flatten '' range (J ∘ g) ↔ _
  rw [reflectedGeometry_actual_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    change Saddle.toE3 x (-z) ∈ d.flatten '' range g
    rw [← Rz_toE3, ← heq, Rz_involutive]
    exact hy
  · intro hx
    exact ⟨Saddle.toE3 x (-z), hx, by simp⟩

theorem reflectedGeometry_B (z : Real) : (G).B z = d.B (-z) := by
  ext x
  change Saddle.toE3 x z ∈ (G).flatten '' ((G).filledModel '' sphere (0 : E3) 1) ↔ _
  rw [reflectedGeometry_model_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    change Saddle.toE3 x (-z) ∈ d.flatten '' (d.filledModel '' sphere (0 : E3) 1)
    rw [← Rz_toE3, ← heq, Rz_involutive]
    exact hy
  · intro hx
    exact ⟨Saddle.toE3 x (-z), hx, by simp⟩

theorem reflectedGeometry_C
    (hcaps : ∀ i, terminalEndCap A (L i) = terminalEndCap d.ends i)
    (i : Fin 3) : (G).C i = Rz '' d.C i := by
  change ((G).flatten ∘ (J ∘ g)) '' terminalEndCap A (L (d.labels i)) = _
  rw [hcaps]
  change _ = Rz '' ((d.flatten ∘ g) '' terminalEndCap d.ends (d.labels i))
  rw [image_image]
  apply image_congr
  intro q _
  exact reflectedGeometry_flatten_leaf M P p e d R hv Q A hl hu L q

theorem reflectedGeometry_modelDomain (i : Fin 3) : (G).modelDomain i = d.modelDomain i := by
  have hset : {q : S2 | inner Real (R.v : E3) ((G).filledModel q) ∉ (G).I} =
      {q : S2 | inner Real (M.v : E3) (d.filledModel q) ∉ d.I} := by
    ext q
    simp only [mem_ofPred_eq, reflectedGeometry_mem_I, reflectedGeometry_filledModel,
      hv, inner_heightReflection, neg_neg]
  change closure (connectedComponentIn _ (d.modelSeed i)) =
    closure (connectedComponentIn _ (d.modelSeed i))
  rw [hset]

theorem reflectedGeometry_modelCaps (i : Fin 3) : (G).modelCaps i = Rz '' d.modelCaps i := by
  change (fun q : S2 => (G).flatten ((G).filledModel q)) '' (G).modelDomain i = _
  rw [reflectedGeometry_modelDomain]
  change _ = Rz '' ((fun q : S2 => d.flatten (d.filledModel q)) '' d.modelDomain i)
  rw [image_image]
  apply image_congr
  intro q _
  exact reflectedGeometry_flatten_model M P p e d R hv Q A hl hu L q

private theorem reflected_band (I K : Set Real) (F H : Real → Set E2)
    (hI : ∀ z, z ∈ I ↔ -z ∈ K) (hF : ∀ z, F z = H (-z)) :
    (⋃ z ∈ I, Saddle.slice (F z) z) = Rz '' (⋃ z ∈ K, Saddle.slice (H z) z) := by
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, hy⟩ := mem_iUnion₂.mp hy
    refine ⟨Rz y, mem_iUnion₂.mpr ⟨-z, (hI z).mp hz, ?_⟩, Rz_involutive y⟩
    change Saddle.toE2 (Rz y) ∈ H (-z) ∧ Rz y 2 = -z
    change Saddle.toE2 y ∈ F z ∧ y 2 = z at hy
    exact ⟨by simpa only [← hF z, toE2_Rz] using hy.1, by simp [hy.2]⟩
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨z, hz, hx⟩ := mem_iUnion₂.mp hx
    refine mem_iUnion₂.mpr ⟨-z, (hI (-z)).mpr (by simpa using hz), ?_⟩
    change Saddle.toE2 (Rz x) ∈ F (-z) ∧ Rz x 2 = -z
    change Saddle.toE2 x ∈ H z ∧ x 2 = z at hx
    exact ⟨by simpa only [hF, neg_neg, toE2_Rz] using hx.1, by simp [hx.2]⟩

theorem reflectedGeometry_actualBand : (G).actualBand = Rz '' d.actualBand := by
  exact reflected_band _ _ _ _ (reflectedGeometry_mem_I M P p e d R hv Q A hl hu L)
    (reflectedGeometry_A M P p e d R hv Q A hl hu L)

theorem reflectedGeometry_modelBand : (G).modelBand = Rz '' d.modelBand := by
  exact reflected_band _ _ _ _ (reflectedGeometry_mem_I M P p e d R hv Q A hl hu L)
    (reflectedGeometry_B M P p e d R hv Q A hl hu L)

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview.Caps

end

end M38Schoenflies
