import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Homeomorph.Lemmas

set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.PhaseCovering

theorem isLocalHomeomorph_prodMap
    {A B C D : Type*} [TopologicalSpace A] [TopologicalSpace B]
    [TopologicalSpace C] [TopologicalSpace D] {f : A → B} {g : C → D}
    (hf : IsLocalHomeomorph f) (hg : IsLocalHomeomorph g) :
    IsLocalHomeomorph (Prod.map f g) := by
  rintro ⟨x, y⟩
  obtain ⟨e, he, hfe⟩ := hf x
  obtain ⟨k, hk, hgk⟩ := hg y
  refine ⟨e.prod k, ⟨he, hk⟩, ?_⟩
  rw [hfe, hgk]
  rfl

theorem isLocalHomeomorph_signed_circle (p : ℝ) (theta : AddCircle p)
    {sigma : ℝ} (hsigma : sigma ≠ 0) :
    IsLocalHomeomorph (fun t : ℝ => theta + ((sigma * t : ℝ) : AddCircle p)) := by
  exact (Homeomorph.addLeft theta).isLocalHomeomorph.comp
    ((AddCircle.isLocalHomeomorph_coe p).comp (Homeomorph.mulLeft₀ sigma hsigma).isLocalHomeomorph)

theorem isLocalHomeomorphOn_of_fiberwise_covering
    {E X Y T : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace Y] [TopologicalSpace T]
    (p : ℝ) (Q : Y ≃ₜ T × AddCircle p) {S : Set E} {r : ℝ}
    (c : E × ℝ → X)
    (hi : IsEmbedding (fun z : S ×ˢ Icc (-r) r => c z))
    (hopen : IsOpen (c '' (S ×ˢ Ioo (-r) r)))
    (f : X → Y) (g : C(S, T)) (hg : IsCoveringMap g)
    (theta : AddCircle p) {sigma : ℝ} (hsigma : sigma ≠ 0)
    (hproduct : ∀ x : S, ∀ t ∈ Icc (-r) r,
      Q (f (c (x, t))) = (g x, theta + ((sigma * t : ℝ) : AddCircle p))) :
    IsLocalHomeomorphOn f (c '' (S ×ˢ Ioo (-r) r)) := by
  let I := Ioo (-r) r
  let k : S × I → X := fun z => c (z.1, z.2)
  have hsub : S ×ˢ I ⊆ S ×ˢ Icc (-r) r :=
    fun z hz => ⟨hz.1, hz.2.1.le, hz.2.2.le⟩
  have hk : IsEmbedding k :=
    (hi.comp (IsEmbedding.inclusion hsub)).comp (Homeomorph.Set.prod S I).symm.isEmbedding
  have hkrange : range k = c '' (S ×ˢ Ioo (-r) r) := by
    ext y
    constructor
    · rintro ⟨⟨x, t⟩, rfl⟩
      exact ⟨(x, t), ⟨x.property, t.property⟩, rfl⟩
    · rintro ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      exact ⟨(⟨x, hx⟩, ⟨t, ht⟩), rfl⟩
  have hkopen : IsOpenEmbedding k :=
    (isOpenEmbedding_iff k).mpr ⟨hk, hkrange.symm ▸ hopen⟩
  have hnormal : IsLocalHomeomorph
      (fun t : I => theta + ((sigma * (t : ℝ) : ℝ) : AddCircle p)) :=
    (isLocalHomeomorph_signed_circle p theta hsigma).comp
      isOpen_Ioo.isOpenEmbedding_subtypeVal.isLocalHomeomorph
  have hcoordinates : IsLocalHomeomorph
      (fun z : S × I => (g z.1, theta + ((sigma * (z.2 : ℝ) : ℝ) : AddCircle p))) :=
    isLocalHomeomorph_prodMap hg.isLocalHomeomorph hnormal
  have hcomp : IsLocalHomeomorph (f ∘ k) := by
    have heq : f ∘ k = (Q.symm : T × AddCircle p → Y) ∘
        (fun z : S × I => (g z.1, theta + ((sigma * (z.2 : ℝ) : ℝ) : AddCircle p))) := by
      funext z
      apply Q.injective
      simp only [Function.comp_apply, Q.apply_symm_apply]
      exact hproduct z.1 z.2 ⟨z.2.property.1.le, z.2.property.2.le⟩
    rw [heq]
    exact Q.symm.isLocalHomeomorph.comp hcoordinates
  have h := (hcomp.isLocalHomeomorphOn (s := univ)).of_comp_right
    hkopen.isLocalHomeomorph.isLocalHomeomorphOn
  simpa only [image_univ, hkrange] using h

end PoincareConjecture.M76.PhaseCovering
