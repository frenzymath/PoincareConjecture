import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Strips.Projection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.LevelGraph.Planar.Clearance










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function TopologicalSpace
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior

open SaddleLevel Poincare.Geometry.Manifold Poincare.Geometry.Manifold.RegularLevel

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
local notation "IR" => 𝓘(Real, Real)
local notation "IR2" => 𝓘(Real, Real × Real)


def correctedStrip {v : E3} (g : S2 → E3)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (R : Real → Real ≃ₘ[Real] Real) (z : Real × Real) : E2 :=
  planarProjection J (D (g (F (R z.1 z.2, z.1))))

theorem contDiffOn_correctedStrip
    {v : E3} {g : S2 → E3}
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source)
    (R : Real → Real ≃ₘ[Real] Real)
    (hR : ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2)) :
    ContDiffOn Real ∞ (correctedStrip g D J F R)
      ((fun z : Real × Real => (R z.1 z.2, z.1)) ⁻¹' F.source) := by
  have hp := hF.comp (hR.prodMk contDiff_fst).contMDiff.contMDiffOn (fun z hz => hz)
  have hπ := J.symm.contDiff.contMDiff.comp
    ((Real ∙ v)ᗮ.orthogonalProjectionOnto.contMDiff.comp (D.contMDiff.comp hg.contMDiff))
  exact (hπ.comp_contMDiffOn hp).contDiffOn



theorem correctedStrip_slice_geometry
    {v : E3} {g : S2 → E3}
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g) (hv : ‖v‖ = 1)
    (D : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hDheight : ∀ y, inner Real v (D y) = inner Real v y)
    (J : E2 ≃ₗᵢ[Real] (Real ∙ v)ᗮ)
    (F : OpenPartialHomeomorph (Real × Real) S2)
    (hF : ContMDiffOn IR2 (𝓡 2) ∞ F F.source)
    (hFi : ContMDiffOn (𝓡 2) IR2 ∞ F.symm F.target)
    {c : Real} (hheight : ∀ z ∈ F.source, inner Real v (g (F z)) = c + z.2)
    (R : Real → Real ≃ₘ[Real] Real)
    (hR : ContDiff Real ∞ (fun z : Real × Real => R z.1 z.2)) (t : Real) :
    InjOn (fun s => correctedStrip g D J F R (t, s))
      {s | (R t s, t) ∈ F.source} ∧
      ∀ s, (R t s, t) ∈ F.source →
        deriv (fun y => correctedStrip g D J F R (t, y)) s ≠ 0 := by
  let U : Opens Real := ⟨{s | (R t s, t) ∈ F.source},
    F.open_source.preimage ((R t).continuous.prodMk continuous_const)⟩
  have hst (s : U) : (R t s, t) ∈ F.source := s.property
  have hRs : ContMDiff IR IR ∞ (fun s : U => R t s) :=
    (R t).contMDiff.comp contMDiff_subtype_val
  have hpair : ContMDiff IR IR2 ∞ (fun s : U => (R t s, t)) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hRs.prodMk contMDiff_const
  have hpairder (s : U) : Injective (mfderiv IR IR2 (fun s : U => (R t s, t)) s) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    rw [mfderiv_prodMk (hRs.mdifferentiable (by simp) s) mdifferentiableAt_const]
    intro x y hxy
    have heq := congrArg Prod.fst hxy
    change mfderiv IR IR (fun s : U => R t s) s x =
      mfderiv IR IR (fun s : U => R t s) s y at heq
    rw [mfderiv_opens_restrict U (R t)
      ((R t).contMDiff.mdifferentiable (by simp) s)] at heq
    exact (R t).mfderivToContinuousLinearEquiv (by simp) s |>.injective heq
  let k : U → S2 := fun s => F (R t s, t)
  have hk : ContMDiff IR (𝓡 2) ∞ k := by
    intro s
    exact (hF.contMDiffAt (F.open_source.mem_nhds (hst s))).comp s (hpair s)
  have hki : Injective k := by
    intro s u heq
    exact Subtype.ext ((R t).injective (congrArg Prod.fst (F.injOn (hst s) (hst u) heq)))
  have hFD : F.MDifferentiable IR2 (𝓡 2) :=
    ⟨hF.mdifferentiableOn (by simp), hFi.mdifferentiableOn (by simp)⟩
  have hkd (s : U) : Injective (mfderiv IR (𝓡 2) k s) := by
    change Injective (mfderiv IR (𝓡 2) (F ∘ fun s : U => (R t s, t)) s)
    rw [mfderiv_comp s (hFD.mdifferentiableAt (hst s)) (hpair.mdifferentiable (by simp) s)]
    exact (hFD.mfderiv_bijective (hst s)).1.comp (hpairder s)
  let G : U → E3 := D ∘ (g ∘ k)
  have hgk : ContMDiff IR (𝓡 3) ∞ (g ∘ k) := hg.contMDiff.comp hk
  have hG : ContMDiff IR (𝓡 3) ∞ G := D.contMDiff.comp hgk
  have hGi : Injective G := D.injective.comp (hg.isEmbedding.injective.comp hki)
  have hGheight (s : U) : inner Real v (G s) = c + t :=
    (hDheight _).trans (hheight _ (hst s))
  have hGd (s : U) : Injective (mfderiv IR (𝓡 3) G s) := by
    have hgkd : Injective (mfderiv IR (𝓡 3) (g ∘ k) s) := by
      rw [mfderiv_comp s (hg.contMDiff.mdifferentiable (by simp) (k s))
        (hk.mdifferentiable (by simp) s)]
      exact (injective_mfderiv_sphere_embedding hg (k s)).comp (hkd s)
    rw [show G = D ∘ (g ∘ k) from rfl,
      mfderiv_comp s (D.contMDiff.mdifferentiable (by simp) ((g ∘ k) s))
        (hgk.mdifferentiable (by simp) s)]
    exact (D.mfderivToContinuousLinearEquiv (by simp) _).injective.comp hgkd
  let q : U → (Real ∙ v)ᗮ := fun s => (Real ∙ v)ᗮ.orthogonalProjectionOnto (G s)
  have hq : ContMDiff IR 𝓘(Real, (Real ∙ v)ᗮ) ∞ q :=
    (Real ∙ v)ᗮ.orthogonalProjectionOnto.contMDiff.comp hG
  have hqi : Injective q := injective_projection_of_height_eq hv hGheight hGi
  have hqd (s : U) : Injective (mfderiv IR 𝓘(Real, (Real ∙ v)ᗮ) q s) :=
    injective_mfderiv_projection_of_height_eq hv hG hGheight hGd s
  have hJ : ContMDiff 𝓘(Real, (Real ∙ v)ᗮ) (𝓡 2) ∞ J.symm.toContinuousLinearEquiv :=
    J.symm.contDiff.contMDiff
  have hpd (s : U) : Injective (mfderiv IR (𝓡 2) (J.symm ∘ q) s) := by
    change Injective (mfderiv IR (𝓡 2) (J.symm.toContinuousLinearEquiv ∘ q) s)
    rw [mfderiv_comp s (hJ.mdifferentiable (by simp) (q s))
      (hq.mdifferentiable (by simp) s)]
    exact (J.symm.toContinuousLinearEquiv.toDiffeomorph.mfderivToContinuousLinearEquiv
      (by simp) (q s)).injective.comp (hqd s)
  have hopen : IsOpen ((fun z : Real × Real => (R z.1 z.2, z.1)) ⁻¹' F.source) :=
    F.open_source.preimage (hR.continuous.prodMk continuous_fst)
  have hfull := contDiffOn_correctedStrip hg D J F hF R hR
  refine ⟨?_, ?_⟩
  · intro s hs u hu heq
    have hh : (⟨s, hs⟩ : U) = ⟨u, hu⟩ := hqi (J.symm.injective heq)
    exact congrArg Subtype.val hh
  · intro s hs
    have hfs : ContDiffAt Real ∞ (fun y => correctedStrip g D J F R (t, y)) s :=
      (hfull.contDiffAt (hopen.mem_nhds hs)).comp s
        (contDiff_const.prodMk contDiff_id).contDiffAt
    have hd := hpd (⟨s, hs⟩ : U)
    change Injective (mfderiv IR (𝓡 2)
      (fun s : U => correctedStrip g D J F R (t, s)) ⟨s, hs⟩) at hd
    rw [mfderiv_opens_restrict U (fun s => correctedStrip g D J F R (t, s))
      (hfs.contMDiffAt.mdifferentiableAt (by simp)), mfderiv_eq_fderiv] at hd
    change Injective (fderiv Real (fun y => correctedStrip g D J F R (t, y)) s) at hd
    intro hz
    have h10 : (1 : Real) = 0 := hd (by
      simpa only [map_zero, fderiv_apply_one_eq_deriv] using hz)
    exact one_ne_zero h10

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior
