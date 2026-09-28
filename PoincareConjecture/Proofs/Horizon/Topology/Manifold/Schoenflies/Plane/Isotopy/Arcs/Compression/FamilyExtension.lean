import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.CompactSupport
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.BallExtension.ParametricInverse

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Compression

private abbrev E2 := EuclideanSpace Real (Fin 2)

theorem exists_supported_family_extension
    (U : Opens E2)
    (F : Real → Diffeomorph (𝓡 2) (𝓡 2) U U ∞)
    (hF : ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : Real × U => F z.1 z.2))
    {K : Set E2} (hK : IsCompact K) (hKU : K ⊆ U)
    (hfix : ∀ (t : Real) (x : U), (x : E2) ∉ K → F t x = x) :
    ∃ Phi : Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞,
      ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) ∧
      ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) ∧
      (∀ (t : Real) (x : U), Phi t x = (F t x : E2)) ∧
      ∀ (t : Real) (x : E2), x ∉ K → Phi t x = x := by
  classical
  have hex (t : Real) := Diffeomorph.exists_extension_of_isCompact U (F t) hK hKU (hfix t)
  choose Phi hPhi hPhifix using hex
  have hsmooth : ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
      (fun z : Real × E2 => Phi z.1 z.2) := by
    intro p
    by_cases hp : p.2 ∈ U
    · let C : Opens (Real × E2) := ⟨univ ×ˢ (U : Set E2), isOpen_univ.prod U.isOpen⟩
      let arg : C → Real × U := fun z => (z.val.1, ⟨z.val.2, z.property.2⟩)
      have harg : ContMDiff (𝓘(Real, Real).prod (𝓡 2))
          (𝓘(Real, Real).prod (𝓡 2)) ∞ arg := by
        apply ContMDiff.prodMk
        · exact contMDiff_fst.comp contMDiff_subtype_val
        · apply (ContMDiff.subtypeVal_comp_iff U
            (fun z : C => (⟨z.val.2, z.property.2⟩ : U))).mp
          exact contMDiff_snd.comp contMDiff_subtype_val
      have hlocal : ContMDiff (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
          (fun z : C => (F z.val.1 ⟨z.val.2, z.property.2⟩ : E2)) :=
        contMDiff_subtype_val.comp (hF.comp harg)
      have heq : (fun z : C => Phi z.val.1 z.val.2) =
          (fun z : C => (F z.val.1 ⟨z.val.2, z.property.2⟩ : E2)) :=
        funext (fun z => hPhi z.val.1 ⟨z.val.2, z.property.2⟩)
      apply (contMDiffAt_subtype_iff (x := (⟨p, ⟨mem_univ _, hp⟩⟩ : C))).mp
      change ContMDiffAt (𝓘(Real, Real).prod (𝓡 2)) (𝓡 2) ∞
        (fun z : C => Phi z.val.1 z.val.2) _
      rw [heq]
      exact hlocal.contMDiffAt
    · have hpK : p.2 ∉ K := fun hx => hp (hKU hx)
      apply contMDiffAt_snd.congr_of_eventuallyEq
      filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
        (hK.isClosed.isOpen_compl.mem_nhds hpK)] with z hz
      exact hPhifix z.1 z.2 hz
  have hinverse := Poincare.Manifold.contMDiff_diffeomorph_family_symm Phi hsmooth
  have hs : ContDiff Real ∞ (fun z : Real × E2 => Phi z.1 z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hsmooth
    exact hsmooth.contDiff
  have hi : ContDiff Real ∞ (fun z : Real × E2 => (Phi z.1).symm z.2) := by
    rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hinverse
    exact hinverse.contDiff
  exact ⟨Phi, hs, hi, hPhi, hPhifix⟩

end Poincare.Manifold.Schoenflies.PlaneArcs.Compression
