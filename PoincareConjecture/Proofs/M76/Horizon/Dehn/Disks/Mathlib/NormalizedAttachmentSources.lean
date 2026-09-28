import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.PrescribedIntervalSourceFibers
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoIntervalDiskNormalization

set_option autoImplicit false

open Set Metric Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "I01" => Icc (0 : ℝ) 1
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)
local notation "TE" => segment ℝ ((0, 1) : P2) (0, 0)

theorem exists_normalization_homeomorph_of_map
    {d : V2 → P2} (hd : FinitePiecewiseAffineOn d D)
    (hemb : Topology.IsEmbedding (fun x : D ↦ d x)) (him : d '' D = T) :
    ∃ H : D ≃ₜ T, H.IsFinitePL ∧ ∀ x : D, (H x : P2) = d x := by
  have hinj : InjOn d D := by
    intro x hx y hy heq
    exact congrArg Subtype.val
      (hemb.injective (show d (⟨x, hx⟩ : D) = d (⟨y, hy⟩ : D) from heq))
  obtain ⟨H, hH, hval⟩ := hd.exists_homeomorph_image hinj
  let H' := H.trans (Homeomorph.setCongr him)
  exact ⟨H', ⟨d, hd, hval⟩, hval⟩

theorem normalized_attachment_source_properties
    {E0 E1 X : Type*} [TopologicalSpace E0] [TopologicalSpace E1]
    {S0 W0 : Set E0} {S1 W1 : Set E1}
    (hW0S : W0 ⊆ S0) (hW1S : W1 ⊆ S1)
    (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL) (H : D ≃ₜ T)
    (p0 : I01 ≃ₜ W0) (p1 : I01 ≃ₜ W1) (p : I01 ≃ₜ TE)
    (h0 : ∀ t : I01, (n0 ⟨p0 t, hW0S (p0 t).property⟩ : P2) = p t)
    (h1 : ∀ t : I01, (n1 ⟨p1 t, hW1S (p1 t).property⟩ : P2) = p t)
    {f0 : E0 → X} {f1 : E1 → X} {f : P2 → X} {g : V2 → X}
    (hg : ∀ x : D, g x = f (H x))
    (hf0 : ∀ x : S0, f (n0 x) = f0 x) (hf1 : ∀ x : S1, f (n1 x) = f1 x) :
    let j0 := fun x : S0 ↦ (H.symm ⟨n0 x, Or.inl (n0 x).property⟩ : V2)
    let j1 := fun x : S1 ↦ (H.symm ⟨n1 x, Or.inr (n1 x).property⟩ : V2)
    Topology.IsEmbedding j0 ∧ Topology.IsEmbedding j1 ∧ range j0 ∪ range j1 = D ∧
    (∀ x : S0, g (j0 x) = f0 x) ∧ (∀ x : S1, g (j1 x) = f1 x) ∧
    (∀ (x : S0) (y : S1), j0 x = j1 y ↔
      ∃! t : I01, (x : E0) = p0 t ∧ (y : E1) = p1 t) ∧
    ∀ U : Set X, D ∩ g ⁻¹' U =
      j0 '' {x : S0 | f0 x ∈ U} ∪ j1 '' {x : S1 | f1 x ∈ U} := by
  let j0 := fun x : S0 ↦ (H.symm ⟨n0 x, Or.inl (n0 x).property⟩ : V2)
  let j1 := fun x : S1 ↦ (H.symm ⟨n1 x, Or.inr (n1 x).property⟩ : V2)
  have hj0 : Topology.IsEmbedding j0 := Topology.IsEmbedding.subtypeVal.comp
    (H.symm.isEmbedding.comp ((Topology.IsEmbedding.inclusion subset_union_left).comp n0.isEmbedding))
  have hj1 : Topology.IsEmbedding j1 := Topology.IsEmbedding.subtypeVal.comp
    (H.symm.isEmbedding.comp ((Topology.IsEmbedding.inclusion subset_union_right).comp n1.isEmbedding))
  have hcover : range j0 ∪ range j1 = D := by
    ext y
    constructor
    · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> exact (H.symm _).property
    · intro hy
      rcases (H ⟨y, hy⟩).property with hR | hL
      · refine Or.inl ⟨n0.symm ⟨H ⟨y, hy⟩, hR⟩, ?_⟩
        dsimp only [j0]
        simp only [n0.apply_symm_apply]
        exact congrArg Subtype.val (H.symm_apply_apply ⟨y, hy⟩)
      · refine Or.inr ⟨n1.symm ⟨H ⟨y, hy⟩, hL⟩, ?_⟩
        dsimp only [j1]
        simp only [n1.apply_symm_apply]
        exact congrArg Subtype.val (H.symm_apply_apply ⟨y, hy⟩)
  have hkeep0 (x : S0) : g (j0 x) = f0 x := by
    rw [hg (H.symm _), H.apply_symm_apply]
    exact hf0 x
  have hkeep1 (x : S1) : g (j1 x) = f1 x := by
    rw [hg (H.symm _), H.apply_symm_apply]
    exact hf1 x
  refine ⟨hj0, hj1, hcover, hkeep0, hkeep1, ?_, ?_⟩
  · intro x y
    have heq : j0 x = j1 y ↔ (n0 x : P2) = n1 y := by
      constructor
      · intro hxy
        exact congrArg Subtype.val (H.symm.injective (Subtype.ext hxy))
      · intro hxy
        exact congrArg (fun z : T ↦ (H.symm z : V2)) (Subtype.ext hxy)
    rw [heq]
    constructor
    · exact prescribed_interval_source_existsUnique hW0S hW1S n0 n1 p0 p1 p h0 h1 x y
    · rintro ⟨t, ht, _⟩
      exact (prescribed_interval_source_eq_iff hW0S hW1S n0 n1 p0 p1 p h0 h1 x y).mpr
        ⟨t, ht⟩
  · intro U
    ext y
    constructor
    · rintro ⟨hy, hyU⟩
      rcases hcover.symm.subset hy with ⟨x, rfl⟩ | ⟨x, rfl⟩
      · exact Or.inl ⟨x, by simpa only [mem_preimage, mem_ofPred_eq, hkeep0] using hyU, rfl⟩
      · exact Or.inr ⟨x, by simpa only [mem_preimage, mem_ofPred_eq, hkeep1] using hyU, rfl⟩
    · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
      · exact ⟨(H.symm _).property, by
          change g (j0 x) ∈ U
          simpa only [hkeep0, mem_ofPred_eq] using hx⟩
      · exact ⟨(H.symm _).property, by
          change g (j1 x) ∈ U
          simpa only [hkeep1, mem_ofPred_eq] using hx⟩

def rightDiskCopy {E : Type*} [TopologicalSpace E] {S : Set E}
    (n : S ≃ₜ TR) (x : S) : T := ⟨n x, Or.inl (n x).property⟩

def leftDiskCopy {E : Type*} [TopologicalSpace E] {S : Set E}
    (n : S ≃ₜ TL) (x : S) : T := ⟨n x, Or.inr (n x).property⟩

theorem rightDiskCopy_isEmbedding {E : Type*} [TopologicalSpace E] {S : Set E}
    (n : S ≃ₜ TR) : Topology.IsEmbedding (rightDiskCopy n) :=
  (Topology.IsEmbedding.inclusion subset_union_left).comp n.isEmbedding

theorem leftDiskCopy_isEmbedding {E : Type*} [TopologicalSpace E] {S : Set E}
    (n : S ≃ₜ TL) : Topology.IsEmbedding (leftDiskCopy n) :=
  (Topology.IsEmbedding.inclusion subset_union_right).comp n.isEmbedding

theorem diskCopies_cover {E0 E1 : Type*} [TopologicalSpace E0] [TopologicalSpace E1]
    {S0 : Set E0} {S1 : Set E1} (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL) (z : T) :
    (∃ x, rightDiskCopy n0 x = z) ∨ (∃ y, leftDiskCopy n1 y = z) := by
  rcases z.property with hz | hz
  · exact Or.inl ⟨n0.symm ⟨z, hz⟩, Subtype.ext (congrArg (fun x : TR ↦ (x : P2))
      (n0.apply_symm_apply ⟨z, hz⟩))⟩
  · exact Or.inr ⟨n1.symm ⟨z, hz⟩, Subtype.ext (congrArg (fun x : TL ↦ (x : P2))
      (n1.apply_symm_apply ⟨z, hz⟩))⟩

end PoincareConjecture.M76.Dehn
