import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Review.Orientation.Planar.Geometry



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Metric Function
open scoped Manifold ContDiff Topology
namespace Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
open Poincare.Geometry.Euclidean PlaneArcs.Terminal.Reflection
private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

@[simp] theorem Rz_toE3 (x : E2) (z : Real) :
    Rz (Saddle.toE3 x z) = Saddle.toE3 x (-z) := rfl

@[simp] theorem toE2_Rz (y : E3) : Saddle.toE2 (Rz y) = Saddle.toE2 y := rfl

theorem Rz_mem_image_iff (y : E3) (S : Set E3) : Rz y ∈ Rz '' S ↔ y ∈ S :=
  Rz.injective.mem_set_image

variable {f : S2 → E3} {p : S2}
    (s : TerminalInputData f p)
    (s' : TerminalInputData s.reduction.reflectedOriginal p)
    (hv : s'.reduction.v = s.reduction.v)
    (hg : s'.leaf = heightReflection (mem_sphere_zero_iff_norm.mp s.reduction.v.property) ∘ s.leaf)
    (he : s'.chart = reflectedMorseChart s.chart)
    (d : SaddleLevel.TerminalSaddleGeometry s'.reduction s'.path p s'.chart)
    (A : SphereSurgeryCoreCap.AnnularEndFamily (s.reduction.v : E3) s.leaf
      ((fun q => inner Real (s.reduction.v : E3) (s.reduction.D (f q))) ''
        {q | mfderiv (𝓡 2) 𝓘(Real, Real)
          (fun y => inner Real (s.reduction.v : E3) (s.reduction.D (f y))) q = 0}) s.path.core)
    (hl : A.lowerCut = -d.ends.upperCut) (hu : A.upperCut = -d.ends.lowerCut)
    (L : d.ends.EndIndex ≃ A.EndIndex)

local notation "G" => reflectGeometry s s' hv hg he d A hl hu L

theorem reflectGeometry_flatten (y : E3) :
    (G).flatten y = Rz (d.flatten
      (heightReflection (mem_sphere_zero_iff_norm.mp s.reduction.v.property) y)) := by
  simp only [TerminalSaddleGeometry.flatten, reflectGeometry, Diffeomorph.coe_trans,
    comp_apply, heightReflection_heightReflection, SaddleLevel.TerminalSaddleGeometry.flatten]

theorem reflectGeometry_flatten_leaf (q : S2) :
    (G).flatten (s.leaf q) = Rz (d.flatten (s'.leaf q)) := by
  rw [reflectGeometry_flatten]
  exact congrArg (fun y => Rz (d.flatten y)) (congrFun hg q).symm

theorem reflectGeometry_filledModel (y : E3) :
    (G).filledModel y = heightReflection
      (mem_sphere_zero_iff_norm.mp s.reduction.v.property) (d.filledModel y) := by
  simp only [TerminalSaddleGeometry.filledModel, reflectGeometry, Diffeomorph.coe_trans,
    comp_apply, Rz_involutive, SaddleLevel.TerminalSaddleGeometry.filledModel]

theorem reflectGeometry_flatten_model (y : E3) :
    (G).flatten ((G).filledModel y) = Rz (d.flatten (d.filledModel y)) := by
  rw [reflectGeometry_flatten, reflectGeometry_filledModel,
    heightReflection_heightReflection]

alias reflectGeometry_flatten_filledModel := reflectGeometry_flatten_model

theorem reflectGeometry_mem_I (z : Real) : z ∈ (G).I ↔ -z ∈ d.I := by
  change (A.lowerCut ≤ z ∧ z ≤ A.upperCut) ↔
    (d.ends.lowerCut ≤ -z ∧ -z ≤ d.ends.upperCut)
  rw [hl, hu]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem reflectGeometry_actual_image :
    (G).flatten '' range s.leaf = Rz '' (d.flatten '' range s'.leaf) := by
  rw [← image_univ, ← image_univ, image_image, image_image, image_image]
  apply image_congr
  intro q _
  exact reflectGeometry_flatten_leaf s s' hv hg he d A hl hu L q

theorem reflectGeometry_model_image :
    (G).flatten '' ((G).filledModel '' sphere (0 : E3) 1) =
      Rz '' (d.flatten '' (d.filledModel '' sphere (0 : E3) 1)) := by
  simp only [image_image]
  apply image_congr
  intro y _
  exact reflectGeometry_flatten_model s s' hv hg he d A hl hu L y

theorem reflectGeometry_A (z : Real) : (G).A z = d.A (-z) := by
  ext x
  change Saddle.toE3 x z ∈ (G).flatten '' range s.leaf ↔ _
  rw [reflectGeometry_actual_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    change Saddle.toE3 x (-z) ∈ d.flatten '' range s'.leaf
    rw [← Rz_toE3, ← heq, Rz_involutive]
    exact hy
  · intro hx
    exact ⟨Saddle.toE3 x (-z), hx, by simp⟩

theorem reflectGeometry_B (z : Real) : (G).B z = d.B (-z) := by
  ext x
  change Saddle.toE3 x z ∈ (G).flatten '' ((G).filledModel '' sphere (0 : E3) 1) ↔ _
  rw [reflectGeometry_model_image]
  constructor
  · rintro ⟨y, hy, heq⟩
    change Saddle.toE3 x (-z) ∈ d.flatten '' (d.filledModel '' sphere (0 : E3) 1)
    rw [← Rz_toE3, ← heq, Rz_involutive]
    exact hy
  · intro hx
    exact ⟨Saddle.toE3 x (-z), hx, by simp⟩

theorem reflectGeometry_C
    (hcaps : ∀ i, terminalEndCap A (L i) = SaddleLevel.terminalEndCap d.ends i)
    (i : Fin 3) : (G).C i = Rz '' d.C i := by
  change ((G).flatten ∘ s.leaf) '' terminalEndCap A (L (d.labels i)) = _
  rw [hcaps]
  change _ = Rz '' ((d.flatten ∘ s'.leaf) '' SaddleLevel.terminalEndCap d.ends (d.labels i))
  rw [image_image]
  apply image_congr
  intro q _
  exact reflectGeometry_flatten_leaf s s' hv hg he d A hl hu L q

theorem reflectGeometry_modelDomain (i : Fin 3) : (G).modelDomain i = d.modelDomain i := by
  have hset : {q : S2 | inner Real (s.reduction.v : E3) ((G).filledModel q) ∉ (G).I} =
      {q : S2 | inner Real (s'.reduction.v : E3) (d.filledModel q) ∉ d.I} := by
    ext q
    rw [mem_ofPred_eq, mem_ofPred_eq, reflectGeometry_mem_I, reflectGeometry_filledModel,
      inner_heightReflection, neg_neg, hv]
  change closure (connectedComponentIn _ (d.modelSeed i)) =
    closure (connectedComponentIn _ (d.modelSeed i))
  rw [hset]

theorem reflectGeometry_modelCaps (i : Fin 3) : (G).modelCaps i = Rz '' d.modelCaps i := by
  change (fun q : S2 => (G).flatten ((G).filledModel q)) '' (G).modelDomain i = _
  rw [reflectGeometry_modelDomain]
  change _ = Rz '' ((fun q : S2 => d.flatten (d.filledModel q)) '' d.modelDomain i)
  rw [image_image]
  apply image_congr
  intro q _
  exact reflectGeometry_flatten_model s s' hv hg he d A hl hu L q

private theorem reflected_band (I J : Set Real) (F H : Real → Set E2)
    (hI : ∀ z, z ∈ I ↔ -z ∈ J) (hF : ∀ z, F z = H (-z)) :
    (⋃ z ∈ I, Saddle.slice (F z) z) = Rz '' (⋃ z ∈ J, Saddle.slice (H z) z) := by
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

theorem reflectGeometry_actualBand : (G).actualBand = Rz '' d.actualBand := by
  exact reflected_band _ _ _ _ (reflectGeometry_mem_I s s' hv hg he d A hl hu L)
    (reflectGeometry_A s s' hv hg he d A hl hu L)

theorem reflectGeometry_modelBand : (G).modelBand = Rz '' d.modelBand := by
  exact reflected_band _ _ _ _ (reflectGeometry_mem_I s s' hv hg he d A hl hu L)
    (reflectGeometry_B s s' hv hg he d A hl hu L)

end Poincare.Manifold.Schoenflies.SaddleLevel.OrientationReview
