import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleCurve.Components.RetainedPartner

set_option autoImplicit false
open Set Topology

namespace PoincareConjecture.M76.Dehn.Annuli

theorem exists_retained_double_locus_copy
    {E Y X : Type*} [TopologicalSpace E] [TopologicalSpace Y] [T2Space Y]
    {f : E → X} {g : Y → X} {K : Set E} {S : Set Y}
    (hK : IsCompact K) (j : K → Y) (hj : Function.Injective j) (hc : Continuous j)
    (hnew : doubleLocusOn g S =
      j '' {x : K | ∃ y : K, f x = f y ∧ (x : E) ≠ y}) :
    ∃ H : doubleLocusOn f K ≃ₜ doubleLocusOn g S,
      ∀ x, (H x : Y) = j ⟨x, x.property.1⟩ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hLK : doubleLocusOn f K ⊆ K := fun _ hx ↦ hx.1
  let J : doubleLocusOn f K → Y := j ∘ Set.inclusion hLK
  have hJ : IsEmbedding J :=
    (hc.isClosedEmbedding hj).isEmbedding.comp (IsEmbedding.inclusion hLK)
  have hrange : range J = doubleLocusOn g S := by
    rw [hnew]
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, hy, heq, hne⟩ := x.property.2
      exact ⟨⟨x, x.property.1⟩, ⟨⟨y, hy⟩, heq, hne⟩, rfl⟩
    · rintro ⟨x, ⟨y, heq, hne⟩, rfl⟩
      exact ⟨⟨x, x.property, y, y.property, heq, hne⟩, rfl⟩
  exact ⟨hJ.toHomeomorph.trans (Homeomorph.setCongr hrange), fun _ ↦ rfl⟩

theorem exists_restricted_source_partner
    {E X : Type*} [TopologicalSpace E] {f : E → X} {K S : Set E}
    (hKS : K ⊆ S) (p : doubleLocusOn f S ≃ₜ doubleLocusOn f S)
    (hp : Function.Involutive p) (hvalue : ∀ x, f (p x) = f x)
    (hfree : ∀ x, (p x : E) ≠ x)
    (hunique : ∀ (x : doubleLocusOn f S) (y : E), y ∈ S →
      f x = f y → (x : E) ≠ y → y = (p x : E)) :
    ∃ q : doubleLocusOn f K ≃ₜ doubleLocusOn f K,
      Function.Involutive q ∧ ∀ x : doubleLocusOn f K,
        ∃ hx : (x : E) ∈ doubleLocusOn f S, (q x : E) = p ⟨x, hx⟩ := by
  have hsub : doubleLocusOn f K ⊆ doubleLocusOn f S := by
    rintro x ⟨hx, y, hy, hxy, hne⟩
    exact ⟨hKS hx, y, hKS hy, hxy, hne⟩
  let inc := Set.inclusion hsub
  have hmem (x : doubleLocusOn f K) : (p (inc x) : E) ∈ doubleLocusOn f K := by
    obtain ⟨y, hy, hxy, hne⟩ := x.property.2
    have hyval := hunique (inc x) y (hKS hy) hxy hne
    exact ⟨hyval ▸ hy, x, x.property.1, hvalue (inc x), hfree (inc x)⟩
  let q (x : doubleLocusOn f K) : doubleLocusOn f K := ⟨p (inc x), hmem x⟩
  have hinc (x : doubleLocusOn f K) : inc (q x) = p (inc x) := rfl
  have hq : Function.Involutive q := by
    intro x
    apply Subtype.ext
    change (p (inc (q x)) : E) = x
    rw [hinc, hp]
  have hqc : Continuous q :=
    ((p.continuous.comp (continuous_inclusion hsub)).subtype_val).subtype_mk hmem
  exact ⟨⟨⟨q, q, hq, hq⟩, hqc, hqc⟩, hq, fun x ↦ ⟨hsub x.property, rfl⟩⟩

theorem retained_relation_unique_other_point
    {E Y X : Type*} {f : E → X} {g : Y → X} {K S : Set E} {T : Set Y}
    (hKS : K ⊆ S) (j : K → Y) (hj : Function.Injective j)
    (hrel : {v : Y × Y | v.1 ∈ T ∧ v.2 ∈ T ∧ g v.1 = g v.2 ∧ v.1 ≠ v.2} =
      (fun v : K × K ↦ (j v.1, j v.2)) ''
        {v | f v.1 = f v.2 ∧ (v.1 : E) ≠ v.2})
    (hunique : ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
      f a = f b → f a = f c → a ≠ b → a ≠ c → b = c)
    (a b c : Y) (ha : a ∈ T) (hb : b ∈ T) (hc : c ∈ T)
    (hab : g a = g b) (hac : g a = g c) (hnab : a ≠ b) (hnac : a ≠ c) : b = c := by
  have habmem : (a, b) ∈ {v : Y × Y | v.1 ∈ T ∧ v.2 ∈ T ∧
      g v.1 = g v.2 ∧ v.1 ≠ v.2} := ⟨ha, hb, hab, hnab⟩
  have hacmem : (a, c) ∈ {v : Y × Y | v.1 ∈ T ∧ v.2 ∈ T ∧
      g v.1 = g v.2 ∧ v.1 ≠ v.2} := ⟨ha, hc, hac, hnac⟩
  obtain ⟨⟨x, y⟩, hxy, heq⟩ := hrel.subset habmem
  obtain ⟨⟨x', z⟩, hxz, heq'⟩ := hrel.subset hacmem
  have hxx : x = x' := hj ((congrArg Prod.fst heq).trans (congrArg Prod.fst heq').symm)
  subst x'
  have hyz : (y : E) = z := hunique x (hKS x.property) y (hKS y.property)
    z (hKS z.property) hxy.1 hxz.1 hxy.2 hxz.2
  exact (congrArg Prod.snd heq).symm.trans
    ((congrArg j (Subtype.ext hyz)).trans (congrArg Prod.snd heq'))

end PoincareConjecture.M76.Dehn.Annuli
