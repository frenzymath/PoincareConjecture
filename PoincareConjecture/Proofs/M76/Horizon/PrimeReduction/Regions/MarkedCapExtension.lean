import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBoundaryPieceGluing
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages












set_option autoImplicit false
open Set Geometry

namespace Set

variable {V W X Y ι : Type*}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

theorem IsFinitePLBallPair.exists_marked_cap_extension
    {b d q : Set X} {B D Q : Set Y}
    (hb : IsFinitePLBallPair V b q) (hB : IsFinitePLBallPair V B Q)
    (hinter : b ∩ d = q) (hInter : B ∩ D = Q)
    (e : d ≃ₜ D) (he : e.IsFinitePL)
    (hmem : ∀ x : d, (x : X) ∈ q ↔ (e x : Y) ∈ Q)
    (f : X → Y) (hval : ∀ x : d, (e x : Y) = f x)
    (a r : ι → Set X) (ha : ∀ i, IsFinitePLBallPair W (a i) (r i))
    (had : ∀ i, a i ⊆ d)
    (hdis : Pairwise fun i j => Disjoint (a i) (a j)) :
    ∃ H : (b ∪ d : Set X) ≃ₜ (B ∪ D : Set Y), H.IsFinitePL ∧
      (∀ x : d, (H ⟨x, Or.inr x.property⟩ : Y) = f x) ∧
      (∀ x : (b ∪ d : Set X), (x : X) ∈ b ↔ (H x : Y) ∈ B) ∧
      (∀ x : (b ∪ d : Set X), (x : X) ∈ d ↔ (H x : Y) ∈ D) ∧
      (∀ i, IsFinitePLBallPair W (f '' a i) (f '' r i)) ∧
      Pairwise (fun i j => Disjoint (f '' a i) (f '' a j)) ∧
      (∀ c : Set X, c ⊆ d →
        (∀ x : (b ∪ d : Set X), (x : X) ∈ c ↔ (H x : Y) ∈ f '' c) ∧
        (fun x : (b ∪ d : Set X) => (H x : Y)) ''
          ((Subtype.val : (b ∪ d : Set X) → X) ⁻¹' c) = f '' c) ∧
      let p := (b ∪ d) \ ⋃ i, a i \ r i
      let P := (B ∪ D) \ ⋃ i, (f '' a i) \ (f '' r i)
      ∃ F : p ≃ₜ P,
        (∀ x : p, (F x : Y) = H ⟨x, x.property.1⟩) ∧
        (∀ x : p, (x : X) ∈ d → (F x : Y) = f x) ∧
        (∀ i (x : p), (x : X) ∈ r i ↔ (F x : Y) ∈ f '' r i) ∧
        (∀ i, (fun x : p => (F x : Y)) ''
          ((Subtype.val : p → X) ⁻¹' r i) = f '' r i) ∧
        ∀ (K : SimplicialComplex ℝ X), K.faces.Finite → K.space = p → F.IsFinitePL := by
  classical
  obtain ⟨H, hH, hkeep, hHb, hHd⟩ :=
    hb.exists_union_homeomorph_of_boundary_piece hB hinter hInter e he hmem
  have hHval (x : d) : (H ⟨x, Or.inr x.property⟩ : Y) = f x :=
    (congrArg Subtype.val (hkeep x)).trans (hval x)
  have hmarked (c : Set X) (hcd : c ⊆ d) (x : (b ∪ d : Set X)) :
      (x : X) ∈ c ↔ (H x : Y) ∈ f '' c := by
    constructor
    · intro hx
      exact ⟨x, hx, (hHval ⟨x, hcd hx⟩).symm⟩
    · rintro ⟨y, hy, hyx⟩
      have hEq : H ⟨y, Or.inr (hcd hy)⟩ = H x :=
        Subtype.ext ((hHval ⟨y, hcd hy⟩).trans hyx)
      have hyx' : y = (x : X) := congrArg Subtype.val (H.injective hEq)
      exact hyx' ▸ hy
  have hf : FinitePiecewiseAffineOn f d := by
    obtain ⟨g, hg, hge⟩ := he
    exact hg.congr (fun x hx => (hge ⟨x, hx⟩).symm.trans (hval ⟨x, hx⟩))
  have hfi : InjOn f d := by
    intro x hx y hy hxy
    have hh : e ⟨x, hx⟩ = e ⟨y, hy⟩ :=
      Subtype.ext ((hval ⟨x, hx⟩).trans (hxy.trans (hval ⟨y, hy⟩).symm))
    exact congrArg Subtype.val (e.injective hh)
  have hballs (i : ι) := (ha i).image_of_subset hf (had i) hfi
  have hdisImages : Pairwise fun i j => Disjoint (f '' a i) (f '' a j) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro y ⟨x, hx, hxy⟩ ⟨z, hz, hzy⟩
    have hxz := hfi (had i hx) (had j hz) (hxy.trans hzy.symm)
    exact disjoint_left.mp (hdis hij) hx (hxz.symm ▸ hz)
  let p := (b ∪ d) \ ⋃ i, a i \ r i
  let P := (B ∪ D) \ ⋃ i, (f '' a i) \ (f '' r i)
  have hp : p ⊆ b ∪ d := sdiff_subset
  have hP : P ⊆ B ∪ D := sdiff_subset
  have hrp (i : ι) : r i ⊆ p := by
    intro x hx
    refine ⟨Or.inr (had i ((ha i).1 hx)), ?_⟩
    rintro hxholes
    obtain ⟨j, hxj, hxr⟩ := mem_iUnion.mp hxholes
    by_cases hij : i = j
    · exact hxr (hij ▸ hx)
    · exact disjoint_left.mp (hdis hij) ((ha i).1 hx) hxj
  have hpuncture (x : (b ∪ d : Set X)) : (x : X) ∈ p ↔ (H x : Y) ∈ P := by
    have hholes : (x : X) ∈ ⋃ i, a i \ r i ↔
        (H x : Y) ∈ ⋃ i, (f '' a i) \ (f '' r i) := by
      simp only [mem_iUnion, mem_sdiff, ← hmarked (a _) (had _),
        ← hmarked (r _) ((ha _).1.trans (had _))]
    simp only [p, P, mem_sdiff, x.property, (H x).property, true_and, hholes]
  let F := H.restrictSubsets hp hP hpuncture
  refine ⟨H, hH, hHval, hHb, hHd, hballs, hdisImages, ?_, F, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hcd
    refine ⟨hmarked c hcd, ?_⟩
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hmarked c hcd x).mp hx
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨⟨x, Or.inr (hcd hx)⟩, hx, hHval ⟨x, hcd hx⟩⟩
  · intro x
    rfl
  · intro x hx
    exact hHval ⟨x, hx⟩
  · intro i x
    exact hmarked (r i) ((ha i).1.trans (had i)) ⟨x, hp x.property⟩
  · intro i
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (hmarked (r i) ((ha i).1.trans (had i)) ⟨x, hp x.property⟩).mp hx
    · rintro y ⟨x, hx, rfl⟩
      exact ⟨⟨x, hrp i hx⟩, hx, hHval ⟨x, had i ((ha i).1 hx)⟩⟩
  · intro K hK hKs
    exact hH.restrictSubsets hp hP hpuncture K hK hKs

end Set
