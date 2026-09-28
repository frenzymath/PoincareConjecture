import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothEmbedding.Hyperplane
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.OpenInclusion
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Collar.Differential
import Mathlib.Geometry.Manifold.LocalDiffeomorph







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.SaddleLevel

open Poincare.Geometry.Manifold
open Poincare.Geometry.Manifold.RegularLevel

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
local notation "IR" => 𝓘(Real, Real)
local notation "IR2" => 𝓘(Real, Real × Real)



theorem contMDiffOn_projected_strip
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (v : E3) (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source) :
    ContMDiffOn IR2 𝓘(Real, (Real ∙ v)ᗮ) ∞
      (fun z => (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (F z))) F.source :=
  ((Real ∙ v)ᗮ.orthogonalProjectionOnto.contMDiff.comp hg.contMDiff).comp_contMDiffOn hF



theorem projected_strip_slice_geometry
    {g : S2 → E3} (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {v : E3} (hv : ‖v‖ = 1) (F : OpenPartialHomeomorph (Real × Real) S2)
    {a b δ c : Real} (hsource : F.source = Ioo a b ×ˢ Ioo (-δ) δ)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) IR2 ∞ F.symm F.target)
    (hheight : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo (-δ) δ,
      inner Real v (g (F (s, t))) = c + t)
    (t : Real) (ht : t ∈ Ioo (-δ) δ) :
    let q : Real → (Real ∙ v)ᗮ :=
      fun s => (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (F (s, t)))
    ContMDiffOn IR 𝓘(Real, (Real ∙ v)ᗮ) ∞ q (Ioo a b) ∧
      InjOn q (Ioo a b) ∧
      ∀ s ∈ Ioo a b, Injective (mfderiv IR 𝓘(Real, (Real ∙ v)ᗮ) q s) := by
  dsimp only
  let U : Opens Real := ⟨Ioo a b, isOpen_Ioo⟩
  have hst (s : U) : ((s : Real), t) ∈ F.source := by
    rw [hsource]
    exact ⟨s.property, ht⟩
  have hpair : ContMDiff IR IR2 ∞ (fun s : U => ((s : Real), t)) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiff_subtype_val.prodMk contMDiff_const
  have hpairder (s : U) :
      Injective (mfderiv IR IR2 (fun s : U => ((s : Real), t)) s) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    rw [mfderiv_prodMk ((contMDiff_subtype_val (n := ∞)).mdifferentiable (by simp) s)
      mdifferentiableAt_const, mfderiv_opens_subtypeVal, mfderiv_const]
    intro x y hxy
    exact congrArg Prod.fst hxy
  let k : U → S2 := fun s => F ((s : Real), t)
  have hk : ContMDiff IR (𝓡 2) ∞ k := by
    intro s
    exact (hF.contMDiffAt (F.open_source.mem_nhds (hst s))).comp s (hpair s)
  have hki : Injective k := by
    intro s u hsu
    exact Subtype.ext (congrArg Prod.fst (F.injOn (hst s) (hst u) hsu))
  have hFD : F.MDifferentiable IR2 (𝓡 2) :=
    ⟨hF.mdifferentiableOn (by simp), hFi.mdifferentiableOn (by simp)⟩
  have hkd (s : U) : Injective (mfderiv IR (𝓡 2) k s) := by
    change Injective (mfderiv IR (𝓡 2) (F ∘ fun s : U => ((s : Real), t)) s)
    rw [mfderiv_comp s (hFD.mdifferentiableAt (hst s))
      (hpair.mdifferentiable (by simp) s)]
    exact (hFD.mfderiv_bijective (hst s)).1.comp (hpairder s)
  have hgk : ContMDiff IR (𝓡 3) ∞ (g ∘ k) := hg.contMDiff.comp hk
  have hlev (s : U) : inner Real v ((g ∘ k) s) = c + t := hheight s s.property t ht
  have hgkd (s : U) : Injective (mfderiv IR (𝓡 3) (g ∘ k) s) := by
    rw [mfderiv_comp s (hg.contMDiff.mdifferentiable (by simp) (k s))
      (hk.mdifferentiable (by simp) s)]
    exact (injective_mfderiv_sphere_embedding hg (k s)).comp (hkd s)
  have hpi := injective_projection_of_height_eq hv hlev (hg.isEmbedding.injective.comp hki)
  have hpd := injective_mfderiv_projection_of_height_eq hv hgk hlev hgkd
  let q : Real → (Real ∙ v)ᗮ :=
    fun s => (Real ∙ v)ᗮ.orthogonalProjectionOnto (g (F (s, t)))
  have hq : ContMDiffOn IR 𝓘(Real, (Real ∙ v)ᗮ) ∞ q (Ioo a b) := by
    intro s hs
    have hsF : (s, t) ∈ F.source := by rw [hsource]; exact ⟨hs, ht⟩
    exact ((contMDiffOn_projected_strip hg v F hF).contMDiffAt
      (F.open_source.mem_nhds hsF)).comp s
      (((contDiff_id.prodMk (contDiff_const (c := t))).contMDiff) s) |>.contMDiffWithinAt
  refine ⟨hq, ?_, ?_⟩
  · intro s hs u hu hsu
    have heq : (⟨s, hs⟩ : U) = ⟨u, hu⟩ := hpi hsu
    exact congrArg Subtype.val heq
  · intro s hs
    have hd := hpd (⟨s, hs⟩ : U)
    change Injective (mfderiv IR 𝓘(Real, (Real ∙ v)ᗮ) (fun s : U => q s) ⟨s, hs⟩) at hd
    rw [mfderiv_opens_restrict U q
      ((hq.contMDiffAt (isOpen_Ioo.mem_nhds hs)).mdifferentiableAt (by simp))] at hd
    exact hd

end Poincare.Manifold.Schoenflies.SaddleLevel
