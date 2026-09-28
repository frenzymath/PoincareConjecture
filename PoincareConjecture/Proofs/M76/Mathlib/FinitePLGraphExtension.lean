import PoincareConjecture.Proofs.M76.Mathlib.FinitePLMarkedGraph
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections










set_option autoImplicit false

open Set Geometry

namespace Set

variable {V E F : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]






theorem IsFinitePLBallPair.exists_iUnion_extension_of_graph
    {ι : Type*} [Finite ι] (S B : ι → Set E) (T C : ι → Set F)
    (hS : ∀ i, IsFinitePLBallPair V (S i) (B i))
    (hT : ∀ i, IsFinitePLBallPair V (T i) (C i))
    {g : Set E} {h : Set F}
    (hSgraph : ∀ i, S i ∩ g = B i) (hTgraph : ∀ i, T i ∩ h = C i)
    (hSpair : Pairwise (fun i j => S i ∩ S j ⊆ g))
    (hTpair : Pairwise (fun i j => T i ∩ T j ⊆ h))
    (hgunion : g ⊆ ⋃ i, S i) (hhunion : h ⊆ ⋃ i, T i)
    (e : g ≃ₜ h) (he : e.IsFinitePL)
    (hmem : ∀ i (x : g), (x : E) ∈ B i ↔ (e x : F) ∈ C i) :
    ∃ H : (⋃ i, S i) ≃ₜ (⋃ i, T i), H.IsFinitePL ∧
      (∀ x : g, H ⟨x, hgunion x.property⟩ =
        ⟨e x, hhunion (e x).property⟩) ∧
      (∀ i (x : ⋃ i, S i), (x : E) ∈ S i ↔ (H x : F) ∈ T i) := by
  classical
  have hbG (i : ι) : B i ⊆ g := by
    rw [← hSgraph i]
    exact inter_subset_right
  have hcH (i : ι) : C i ⊆ h := by
    rw [← hTgraph i]
    exact inter_subset_right
  have hex (i : ι) : ∃ f : S i ≃ₜ T i, f.IsFinitePL ∧
      (∀ x : B i, (f ⟨x, (hS i).1 x.property⟩ : F) = e ⟨x, hbG i x.property⟩) ∧
      (∀ x : S i, (x : E) ∈ B i ↔ (f x : F) ∈ C i) := by
    have hcopy := hS i
    have hecopy := he
    obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKS, _⟩, _⟩, _⟩ := hcopy
    obtain ⟨_, ⟨J, hJ, hJg, _⟩, _⟩ := hecopy
    obtain ⟨L, hL, hLB⟩ := K.exists_finite_triangulation_inter J hK hJ
    rw [hKS, hJg, hSgraph i] at hLB
    let eb := e.restrictSubsets (hbG i) (hcH i) (hmem i)
    have heb : eb.IsFinitePL :=
      he.restrictSubsets (hbG i) (hcH i) (hmem i) L hL hLB
    obtain ⟨f, hf, hfb, hboundary⟩ := (hS i).exists_extension (hT i) eb heb
    exact ⟨f, hf, fun x => congrArg Subtype.val (hfb x), hboundary⟩
  choose f hf hkeep hboundary using hex
  have hoverlap (i j : ι) (x : S i) : (x : E) ∈ S j ↔ (f i x : F) ∈ T j := by
    by_cases hij : i = j
    · subst j
      exact iff_of_true x.property (f i x).property
    constructor
    · intro hxj
      have hxg : (x : E) ∈ g := hSpair hij ⟨x.property, hxj⟩
      have hxiB : (x : E) ∈ B i := (hSgraph i).subset ⟨x.property, hxg⟩
      have hxjB : (x : E) ∈ B j := (hSgraph j).subset ⟨hxj, hxg⟩
      have hye : (f i x : F) = e ⟨x, hxg⟩ := hkeep i ⟨x, hxiB⟩
      rw [hye]
      exact (hT j).1 ((hmem j ⟨x, hxg⟩).mp hxjB)
    · intro hyj
      have hyh : (f i x : F) ∈ h := hTpair hij ⟨(f i x).property, hyj⟩
      have hyiC : (f i x : F) ∈ C i := (hTgraph i).subset ⟨(f i x).property, hyh⟩
      have hyjC : (f i x : F) ∈ C j := (hTgraph j).subset ⟨hyj, hyh⟩
      have hxiB : (x : E) ∈ B i := (hboundary i x).mpr hyiC
      have hxg : (x : E) ∈ g := hbG i hxiB
      have hye : (f i x : F) = e ⟨x, hxg⟩ := hkeep i ⟨x, hxiB⟩
      rw [hye] at hyjC
      exact (hS j).1 ((hmem j ⟨x, hxg⟩).mpr hyjC)
  have hagree (i j : ι) (x : E) (hi : x ∈ S i) (hj : x ∈ S j) :
      (f i ⟨x, hi⟩ : F) = f j ⟨x, hj⟩ := by
    by_cases hij : i = j
    · subst j
      rfl
    have hxg : x ∈ g := hSpair hij ⟨hi, hj⟩
    have hxiB : x ∈ B i := (hSgraph i).subset ⟨hi, hxg⟩
    have hxjB : x ∈ B j := (hSgraph j).subset ⟨hj, hxg⟩
    exact (hkeep i ⟨x, hxiB⟩).trans (hkeep j ⟨x, hxjB⟩).symm
  obtain ⟨H, hH, hHkeep⟩ := Homeomorph.exists_iUnion_finitePL S T f hf hoverlap hagree
  refine ⟨H, hH, ?_, ?_⟩
  · intro x
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hgunion x.property)
    have hxiB : (x : E) ∈ B i := (hSgraph i).subset ⟨hi, x.property⟩
    exact Subtype.ext ((hHkeep i ⟨x, hi⟩).trans (hkeep i ⟨x, hxiB⟩))
  · intro i x
    exact H.mem_subset_iff_of_extension (f i)
      (fun y hy => mem_iUnion.mpr ⟨i, hy⟩)
      (fun y hy => mem_iUnion.mpr ⟨i, hy⟩)
      (fun y => Subtype.ext (hHkeep i y)) x

end Set
