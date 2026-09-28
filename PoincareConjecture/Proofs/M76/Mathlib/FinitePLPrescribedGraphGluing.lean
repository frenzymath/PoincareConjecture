import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFamilyGluing
import PoincareConjecture.Proofs.M76.Mathlib.UnitBallPairs

set_option autoImplicit false

open Set

namespace Set

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_finitePL_marked_graph_of_maps {ι : Type*} [Finite ι]
    (S : ι → Set E) (T : ι → Set F) {a b : E} {c d : F}
    (haS : ∀ i, a ∈ S i) (hbS : ∀ i, b ∈ S i)
    (hSi : Pairwise (fun i j => S i ∩ S j = {a, b}))
    (hTi : Pairwise (fun i j => T i ∩ T j = {c, d}))
    (e : ∀ i, S i ≃ₜ T i) (he : ∀ i, (e i).IsFinitePL)
    (hea : ∀ i, (e i ⟨a, haS i⟩ : F) = c)
    (heb : ∀ i, (e i ⟨b, hbS i⟩ : F) = d) :
    ∃ H : (⋃ i, S i) ≃ₜ (⋃ i, T i), H.IsFinitePL ∧
      (∀ i (x : S i), (H ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ : F) = e i x) ∧
      (∀ i (x : ⋃ i, S i), (x : E) ∈ S i ↔ (H x : F) ∈ T i) ∧
      (∀ x : ⋃ i, S i, (H x : F) = c ↔ (x : E) = a) ∧
      (∀ x : ⋃ i, S i, (H x : F) = d ↔ (x : E) = b) := by
  have hae (i : ι) (x : S i) : (e i x : F) = c ↔ (x : E) = a := by
    constructor
    · intro hx
      exact congrArg Subtype.val ((e i).injective (Subtype.ext (hx.trans (hea i).symm)))
    · intro hx
      have heq : x = ⟨a, haS i⟩ := Subtype.ext hx
      simpa only [heq] using hea i
  have hbe (i : ι) (x : S i) : (e i x : F) = d ↔ (x : E) = b := by
    constructor
    · intro hx
      exact congrArg Subtype.val ((e i).injective (Subtype.ext (hx.trans (heb i).symm)))
    · intro hx
      have heq : x = ⟨b, hbS i⟩ := Subtype.ext hx
      simpa only [heq] using heb i
  have hoverlap (i j : ι) (x : S i) : (x : E) ∈ S j ↔ (e i x : F) ∈ T j := by
    by_cases hij : i = j
    · subst j
      exact iff_of_true x.property (e i x).property
    have hx : (x : E) ∈ S j ↔ (x : E) ∈ ({a, b} : Set E) := by
      rw [← hSi hij]
      simp only [mem_inter_iff, x.property, true_and]
    have hy : (e i x : F) ∈ ({c, d} : Set F) ↔ (e i x : F) ∈ T j := by
      rw [← hTi hij]
      simp only [mem_inter_iff, (e i x).property, true_and]
    have hmarks : (x : E) ∈ ({a, b} : Set E) ↔ (e i x : F) ∈ ({c, d} : Set F) := by
      simp only [mem_insert_iff, mem_singleton_iff, hae, hbe]
    exact hx.trans (hmarks.trans hy)
  have hagree (i j : ι) (x : E) (hi : x ∈ S i) (hj : x ∈ S j) :
      (e i ⟨x, hi⟩ : F) = e j ⟨x, hj⟩ := by
    by_cases hij : i = j
    · subst j
      rfl
    rcases (hSi hij).subset ⟨hi, hj⟩ with hx | hx
    · exact ((hae i ⟨x, hi⟩).mpr hx).trans ((hae j ⟨x, hj⟩).mpr hx).symm
    · exact ((hbe i ⟨x, hi⟩).mpr hx).trans ((hbe j ⟨x, hj⟩).mpr hx).symm
  obtain ⟨H, hH, hkeep⟩ := Homeomorph.exists_iUnion_finitePL S T e he hoverlap hagree
  refine ⟨H, hH, hkeep, ?_, ?_, ?_⟩
  · intro i
    exact H.mem_subset_iff_of_extension (e i) (subset_iUnion S i) (subset_iUnion T i)
      (fun x => Subtype.ext (hkeep i x))
  · intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    rw [hkeep i ⟨x, hi⟩]
    exact hae i ⟨x, hi⟩
  · intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp x.property
    rw [hkeep i ⟨x, hi⟩]
    exact hbe i ⟨x, hi⟩

theorem exists_finitePL_region_gluing_of_graph {ι : Type*} [Finite ι]
    (S B : ι → Set E) (T C : ι → Set F) {g : Set E} {h : Set F}
    (hSgraph : ∀ i, S i ∩ g = B i) (hTgraph : ∀ i, T i ∩ h = C i)
    (hSpair : Pairwise (fun i j => S i ∩ S j ⊆ g))
    (hTpair : Pairwise (fun i j => T i ∩ T j ⊆ h))
    (hgunion : g ⊆ ⋃ i, S i) (hhunion : h ⊆ ⋃ i, T i)
    (G : g ≃ₜ h)
    (hGmem : ∀ i (x : g), (x : E) ∈ B i ↔ (G x : F) ∈ C i)
    (e : ∀ i, S i ≃ₜ T i) (he : ∀ i, (e i).IsFinitePL)
    (hboundary : ∀ i (x : S i), (x : E) ∈ B i ↔ (e i x : F) ∈ C i)
    (hkeepG : ∀ i (x : B i),
      (e i ⟨x, ((hSgraph i).symm.subset x.property).1⟩ : F) =
        G ⟨x, ((hSgraph i).symm.subset x.property).2⟩) :
    ∃ H : (⋃ i, S i) ≃ₜ (⋃ i, T i), H.IsFinitePL ∧
      (∀ i (x : S i), (H ⟨x, mem_iUnion.mpr ⟨i, x.property⟩⟩ : F) = e i x) ∧
      (∀ x : g, H ⟨x, hgunion x.property⟩ = ⟨G x, hhunion (G x).property⟩) ∧
      ∀ i (x : ⋃ i, S i), (x : E) ∈ S i ↔ (H x : F) ∈ T i := by
  have hbS (i : ι) : B i ⊆ S i := fun x hx => ((hSgraph i).symm.subset hx).1
  have hbG (i : ι) : B i ⊆ g := fun x hx => ((hSgraph i).symm.subset hx).2
  have hcT (i : ι) : C i ⊆ T i := fun x hx => ((hTgraph i).symm.subset hx).1
  have hoverlap (i j : ι) (x : S i) : (x : E) ∈ S j ↔ (e i x : F) ∈ T j := by
    by_cases hij : i = j
    · subst j
      exact iff_of_true x.property (e i x).property
    constructor
    · intro hxj
      have hxg : (x : E) ∈ g := hSpair hij ⟨x.property, hxj⟩
      have hxiB : (x : E) ∈ B i := (hSgraph i).subset ⟨x.property, hxg⟩
      have hxjB : (x : E) ∈ B j := (hSgraph j).subset ⟨hxj, hxg⟩
      have hye : (e i x : F) = G ⟨x, hxg⟩ := hkeepG i ⟨x, hxiB⟩
      rw [hye]
      exact hcT j ((hGmem j ⟨x, hxg⟩).mp hxjB)
    · intro hyj
      have hyh : (e i x : F) ∈ h := hTpair hij ⟨(e i x).property, hyj⟩
      have hyiC : (e i x : F) ∈ C i := (hTgraph i).subset ⟨(e i x).property, hyh⟩
      have hyjC : (e i x : F) ∈ C j := (hTgraph j).subset ⟨hyj, hyh⟩
      have hxiB : (x : E) ∈ B i := (hboundary i x).mpr hyiC
      have hxg : (x : E) ∈ g := hbG i hxiB
      have hye : (e i x : F) = G ⟨x, hxg⟩ := hkeepG i ⟨x, hxiB⟩
      rw [hye] at hyjC
      exact hbS j ((hGmem j ⟨x, hxg⟩).mpr hyjC)
  have hagree (i j : ι) (x : E) (hi : x ∈ S i) (hj : x ∈ S j) :
      (e i ⟨x, hi⟩ : F) = e j ⟨x, hj⟩ := by
    by_cases hij : i = j
    · subst j
      rfl
    have hxg : x ∈ g := hSpair hij ⟨hi, hj⟩
    have hxiB : x ∈ B i := (hSgraph i).subset ⟨hi, hxg⟩
    have hxjB : x ∈ B j := (hSgraph j).subset ⟨hj, hxg⟩
    exact (hkeepG i ⟨x, hxiB⟩).trans (hkeepG j ⟨x, hxjB⟩).symm
  obtain ⟨H, hH, hHkeep⟩ := Homeomorph.exists_iUnion_finitePL S T e he hoverlap hagree
  refine ⟨H, hH, hHkeep, ?_, ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hgunion x.property)
    have hxiB : (x : E) ∈ B i := (hSgraph i).subset ⟨hi, x.property⟩
    exact Subtype.ext ((hHkeep i ⟨x, hi⟩).trans (hkeepG i ⟨x, hxiB⟩))
  · intro i
    exact H.mem_subset_iff_of_extension (e i) (subset_iUnion S i) (subset_iUnion T i)
      (fun x => Subtype.ext (hHkeep i x))

end Set
