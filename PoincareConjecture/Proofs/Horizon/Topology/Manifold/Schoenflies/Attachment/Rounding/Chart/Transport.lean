import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.Restriction



noncomputable section
set_option autoImplicit false

open Set TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Rounding

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  {H M : Type*} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  {I : ModelWithCorners Real E H}

def pullbackOpen (H : Diffeomorph I I M M ∞) (C : Opens M) : Opens M :=
  ⟨H ⁻¹' C, C.isOpen.preimage H.continuous⟩


def pullbackDiffeomorph (H : Diffeomorph I I M M ∞) (C : Opens M) :
    Diffeomorph I I (pullbackOpen H C) C ∞ :=
  H.restrictOpens (pullbackOpen H C) C (fun _ => Iff.rfl)

@[simp] theorem pullbackDiffeomorph_apply
    (H : Diffeomorph I I M M ∞) (C : Opens M) (x : pullbackOpen H C) :
    (pullbackDiffeomorph H C x : M) = H x := rfl

@[simp] theorem pullbackDiffeomorph_symm_apply
    (H : Diffeomorph I I M M ∞) (C : Opens M) (x : C) :
    ((pullbackDiffeomorph H C).symm x : M) = H.symm x := rfl


theorem pullback_image_inter
    (H : Diffeomorph I I M M ∞) (C : Opens M)
    {X : Type*} (q : X → C) {A B : Set M} {S : Set X}
    (hAB : H '' A = B) (hB : B ∩ C = (fun x => (q x : M)) '' S) :
    A ∩ pullbackOpen H C =
      (fun x => H.symm (q x : M)) '' S := by
  ext y
  constructor
  · rintro ⟨hyA, hyC⟩
    have hyB : H y ∈ B := hAB ▸ mem_image_of_mem H hyA
    obtain ⟨x, hx, hxy⟩ := hB ▸ (show H y ∈ B ∩ C from ⟨hyB, hyC⟩)
    refine ⟨x, hx, ?_⟩
    change H.symm (q x : M) = y
    change (q x : M) = H y at hxy
    rw [hxy, H.symm_apply_apply]
  · rintro ⟨x, hx, rfl⟩
    have hqB : (q x : M) ∈ B := (show (q x : M) ∈ B ∩ C from
      hB.symm ▸ mem_image_of_mem (fun x => (q x : M)) hx).1
    rw [← hAB] at hqB
    obtain ⟨z, hz, hzx⟩ := hqB
    refine ⟨?_, ?_⟩
    · change H.symm (q x : M) ∈ A
      rwa [← hzx, H.symm_apply_apply]
    · change H (H.symm (q x : M)) ∈ C
      rw [H.apply_symm_apply]
      exact (q x).property

end Poincare.Manifold.Schoenflies.Rounding
