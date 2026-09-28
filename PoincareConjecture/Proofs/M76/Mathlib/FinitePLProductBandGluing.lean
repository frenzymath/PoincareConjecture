import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets

set_option autoImplicit false

open Set Geometry

namespace Homeomorph

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Finite ι]

theorem exists_iUnion_height_product
    (T : ι → Set E) (A : E → ℝ) {α β : ℝ} (hαβ : α ≤ β)
    (C : ∀ i, ((T i ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ)) ≃ₜ T i)
    (hC : ∀ i, (C i).IsFinitePL)
    (hheight : ∀ i p, A (C i p) = (p : E × ℝ).2)
    (hbottom : ∀ i (x : E) (hx : x ∈ T i ∩ {x | A x = α}),
      (C i ⟨(x, α), ⟨hx, ⟨le_rfl, hαβ⟩⟩⟩ : E) = x)
    (hoverlap : ∀ i j p, (C i p : E) ∈ T j ↔ (p : E × ℝ).1 ∈ T j)
    (hinj : ∀ i j, i ≠ j → InjOn A (T i ∩ T j)) :
    ∃ H : (((⋃ i, T i) ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ)) ≃ₜ
        (⋃ i, T i),
      H.IsFinitePL ∧ (∀ p, A (H p) = (p : E × ℝ).2) ∧
      (∀ (x : E) (hx : x ∈ (⋃ i, T i) ∩ {x | A x = α}),
        (H ⟨(x, α), ⟨hx, ⟨le_rfl, hαβ⟩⟩⟩ : E) = x) ∧
      ∀ i (p : ((T i ∩ {x | A x = α}) ×ˢ Icc α β : Set (E × ℝ))),
        (H ⟨p, ⟨⟨mem_iUnion.mpr ⟨i, p.property.1.1⟩,
        p.property.1.2⟩, p.property.2⟩⟩ : E) = C i p := by
  classical
  let S : ι → Set (E × ℝ) := fun i => (T i ∩ {x | A x = α}) ×ˢ Icc α β
  have hmem : ∀ i j (p : S i), (p : E × ℝ) ∈ S j ↔ (C i p : E) ∈ T j := by
    intro i j p
    constructor
    · exact fun hp => (hoverlap i j p).mpr hp.1.1
    · exact fun hp => ⟨⟨(hoverlap i j p).mp hp, p.property.1.2⟩, p.property.2⟩
  have hagree : ∀ i j (p : E × ℝ) (hi : p ∈ S i) (hj : p ∈ S j),
      (C i ⟨p, hi⟩ : E) = C j ⟨p, hj⟩ := by
    intro i j p hi hj
    by_cases hij : i = j
    · subst j
      rfl
    apply hinj i j hij
      ⟨(C i ⟨p, hi⟩).property, (hmem i j ⟨p, hi⟩).mp hj⟩
      ⟨(hmem j i ⟨p, hj⟩).mp hi, (C j ⟨p, hj⟩).property⟩
    exact (hheight i ⟨p, hi⟩).trans (hheight j ⟨p, hj⟩).symm
  have hsource : (⋃ i, S i) = ((⋃ i, T i) ∩ {x | A x = α}) ×ˢ Icc α β := by
    ext p
    constructor
    · intro hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp
      exact ⟨⟨mem_iUnion.mpr ⟨i, hi.1.1⟩, hi.1.2⟩, hi.2⟩
    · intro hp
      obtain ⟨i, hi⟩ := mem_iUnion.mp hp.1.1
      exact mem_iUnion.mpr ⟨i, ⟨⟨hi, hp.1.2⟩, hp.2⟩⟩
  obtain ⟨G, hG, hGres⟩ := exists_iUnion_finitePL S T C hC hmem hagree
  let H := (Homeomorph.setCongr hsource.symm).trans G
  have hres (i : ι) (p : S i) :
      (H ⟨p, ⟨⟨mem_iUnion.mpr ⟨i, p.property.1.1⟩,
        p.property.1.2⟩, p.property.2⟩⟩ : E) = C i p := hGres i p
  refine ⟨H, hG.setCongr hsource rfl, ?_, ?_, hres⟩
  · intro p
    obtain ⟨i, hi⟩ := mem_iUnion.mp p.property.1.1
    have hp : (p : E × ℝ) ∈ S i := ⟨⟨hi, p.property.1.2⟩, p.property.2⟩
    exact (congrArg A (hres i ⟨p, hp⟩)).trans (hheight i ⟨p, hp⟩)
  · intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp hx.1
    exact (hres i ⟨(x, α), ⟨⟨hi, hx.2⟩, ⟨le_rfl, hαβ⟩⟩⟩).trans
      (hbottom i x ⟨hi, hx.2⟩)

end Homeomorph
