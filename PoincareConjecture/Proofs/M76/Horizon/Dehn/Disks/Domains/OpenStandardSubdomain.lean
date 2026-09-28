import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Domains.CompactSubdomain
import Mathlib.Topology.OpenPartialHomeomorph.Constructions











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)



theorem PLDomain.standard_open_image
    (U : TopologicalSpace.Opens V3) (hU : Nonempty U) {K : Set U}
    (hK : PLDomain (fun _ : Unit => U.openPartialHomeomorphSubtypeCoe hU) K)
    (hcompact : IsCompact K) :
    PLDomain (fun _ : Unit => OpenPartialHomeomorph.refl V3)
      ((Subtype.val : U → V3) '' K) := by
  let j := U.openPartialHomeomorphSubtypeCoe hU
  have hjs : j.source = univ := rfl
  have himage : IsCompact ((Subtype.val : U → V3) '' K) :=
    hcompact.image continuous_subtype_val
  refine ⟨fun _ => ⟨(), mem_univ _⟩, ?_, himage.isClosed, ?_⟩
  · intro i k
    simpa using (piecewiseAffineGroupoid V3).id_mem
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := himage.isClosed.frontier_subset hx
    have hpre : (Subtype.val : U → V3) ⁻¹' ((Subtype.val : U → V3) '' K) = K :=
      preimage_image_eq K Subtype.val_injective
    have hopen : IsOpenMap (Subtype.val : U → V3) := U.isOpen.isOpenMap_subtype_val
    have hfront := hopen.preimage_frontier_eq_frontier_preimage
      (continuous_subtype_val : Continuous (Subtype.val : U → V3))
      ((Subtype.val : U → V3) '' K)
    rw [hpre] at hfront
    have hyfront : y ∈ frontier K := hfront.subset hx
    obtain ⟨ell, v, B, hv, hyB, hyzero, hB, hhalf⟩ := hK.halfspace y hyfront
    let C := j.symm.trans B
    have hyj : j y ∈ j.target := j.mapsTo (hjs.symm ▸ mem_univ y)
    have hyC : (y : V3) ∈ C.source := by
      refine ⟨hyj, ?_⟩
      change j.symm (j y) ∈ B.source
      rw [j.left_inv (hjs.symm ▸ mem_univ y)]
      exact hyB
    have hCy : C y = B y := by
      change B (j.symm (j y)) = B y
      rw [j.left_inv (hjs.symm ▸ mem_univ y)]
    refine ⟨ell, v, C, hv, hyC, hCy ▸ hyzero, ?_, ?_⟩
    · intro i
      simpa only [OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_trans]
        using hB ()
    · intro z hz
      have hjz : ((j.symm z : U) : V3) = z := j.right_inv hz.1
      change z ∈ (Subtype.val : U → V3) '' K ↔ 0 ≤ ell (B (j.symm z))
      rw [← hhalf (j.symm z) hz.2]
      constructor
      · rintro ⟨w, hw, hwz⟩
        have heq : w = j.symm z := Subtype.ext (hwz.trans hjz.symm)
        exact heq ▸ hw
      · intro hzK
        exact ⟨j.symm z, hzK, hjz⟩






theorem exists_compact_standard_subdomain_in_open
    (U : TopologicalSpace.Opens V3) (hU : Nonempty U) {R A : Set U} {W : Set V3}
    (hR : PLDomain (fun _ : Unit => U.openPartialHomeomorphSubtypeCoe hU) R)
    (hA : IsCompact A) (hAR : A ⊆ R) (hW : IsOpen W)
    (hAW : (Subtype.val : U → V3) '' A ⊆ W) :
    ∃ K V : Set V3, IsCompact K ∧
      PLDomain (fun _ : Unit => OpenPartialHomeomorph.refl V3) K ∧
      (Subtype.val : U → V3) '' A ⊆ K ∧
      K ⊆ ((Subtype.val : U → V3) '' R) ∩ W ∧
      IsOpen V ∧ (Subtype.val : U → V3) '' A ⊆ V ∧ V ⊆ (U : Set V3) ∩ W ∧
      K ∩ V = ((Subtype.val : U → V3) '' R) ∩ V ∧
      frontier K ∩ V = frontier ((Subtype.val : U → V3) '' R) ∩ V := by
  obtain ⟨K0, V0, hK0, hKPL, hAK, hKW, hV0, hAV, hVW, hlocal, _, _⟩ :=
    hR.exists_compact_subdomain_near hA hAR (hW.preimage continuous_subtype_val)
      (fun x hx => hAW (mem_image_of_mem Subtype.val hx))
  let K : Set V3 := Subtype.val '' K0
  let V : Set V3 := Subtype.val '' V0
  have hV : IsOpen V := U.isOpen.isOpenMap_subtype_val V0 hV0
  have hlocal' : K ∩ V = (Subtype.val '' R) ∩ V := by
    rw [← image_inter Subtype.val_injective, hlocal, image_inter Subtype.val_injective]
  refine ⟨K, V, hK0.image continuous_subtype_val, hKPL.standard_open_image U hU hK0,
    image_mono hAK, ?_, hV, image_mono hAV, ?_, hlocal', ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨mem_image_of_mem Subtype.val (hKW hy).1, (hKW hy).2⟩
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨y.property, hVW hy⟩
  · calc
      frontier K ∩ V = frontier (K ∩ V) ∩ V := (frontier_inter_open_inter hV).symm
      _ = frontier ((Subtype.val '' R) ∩ V) ∩ V :=
        congrArg (fun S => frontier S ∩ V) hlocal'
      _ = frontier (Subtype.val '' R) ∩ V := frontier_inter_open_inter hV

end PoincareConjecture.M76
