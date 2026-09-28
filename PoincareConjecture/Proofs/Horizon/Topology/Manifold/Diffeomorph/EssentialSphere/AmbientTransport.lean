import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.AmbientReduction








set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



theorem exists_cylinder_coordinates_of_ambient_sphere_in_model
    {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace E3 Y] [IsManifold (𝓡 3) ∞ Y]
    (J : Diffeomorph (𝓡 3) (𝓡 3) Y puncturedThreeSpace ∞)
    (f : S2 → Y) (F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hF : ∀ q : S2, F q = (J (f q) : E3))
    (A B : Set Y) (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hcover : A ∪ B = (range f)ᶜ)
    (hescape : ∀ L : Set Y, IsCompact L → ¬ A ⊆ L ∧ ¬ B ⊆ L) :
    ∃ G : Diffeomorph CylModel (𝓡 3) (S2 × ℝ) Y ∞,
      ∀ q : S2, G (q, 0) = f q := by
  let j : Y → E3 := fun y => J y
  have hj : Continuous j := continuous_subtype_val.comp J.continuous
  have hinj : Function.Injective j := fun _ _ h => J.injective (Subtype.ext h)
  have hzero (y : Y) : j y ≠ 0 := (J y).property
  have hsurj {x : E3} (hx : x ≠ 0) : ∃ y, j y = x :=
    ⟨J.symm ⟨x, hx⟩, congrArg Subtype.val (J.apply_symm_apply ⟨x, hx⟩)⟩
  have hsphere : F '' Metric.sphere (0 : E3) 1 = range (j ∘ f) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨⟨q, hq⟩, (hF ⟨q, hq⟩).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.property, hF q⟩
  have havoid : (0 : E3) ∉ F '' Metric.sphere 0 1 := by
    rw [hsphere]
    rintro ⟨q, hq⟩
    exact hzero (f q) hq
  have hcover' : j '' A ∪ j '' B = {0}ᶜ \ (F '' Metric.sphere 0 1) := by
    rw [← image_union, hcover, hsphere]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hzero y, ?_⟩
      rintro ⟨q, hq⟩
      exact hy ⟨q, hinj hq⟩
    · rintro ⟨hx, hs⟩
      obtain ⟨y, rfl⟩ := hsurj hx
      refine ⟨y, ?_, rfl⟩
      rintro ⟨q, rfl⟩
      exact hs ⟨q, rfl⟩
  have hescape' : ∀ L : Set E3, IsCompact L → L ⊆ {0}ᶜ →
      ¬ j '' A ⊆ L ∧ ¬ j '' B ⊆ L := by
    intro L hL hLzero
    have hsub : IsCompact ((Subtype.val : puncturedThreeSpace → E3) ⁻¹' L) :=
      Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hL
        (fun x hx => ⟨⟨x, hLzero hx⟩, rfl⟩)
    let K := J.symm '' ((Subtype.val : puncturedThreeSpace → E3) ⁻¹' L)
    have hK : IsCompact K := hsub.image J.symm.continuous
    have hpre {y : Y} (hy : j y ∈ L) : y ∈ K :=
      ⟨J y, hy, J.symm_apply_apply y⟩
    exact ⟨fun h => (hescape K hK).1 (fun y hy => hpre (h ⟨y, hy, rfl⟩)),
      fun h => (hescape K hK).2 (fun y hy => hpre (h ⟨y, hy, rfl⟩))⟩
  obtain ⟨G, hG⟩ := exists_cylinder_coordinates_of_ambient_sphere F
    (j '' A) (j '' B) (hA.image j hj.continuousOn) (hB.image j hj.continuousOn)
    havoid hcover' hescape'
  refine ⟨G.trans J.symm, ?_⟩
  intro q
  change J.symm (G (q, 0)) = f q
  have heq : G (q, 0) = J (f q) := Subtype.ext ((hG q).trans (hF q))
  rw [heq, J.symm_apply_apply]

end Poincare
