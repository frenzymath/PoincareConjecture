import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneBoundary.Minimum
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Surgery.Iteration.Core.OneBoundary.Reflection



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

open Poincare.Geometry.Euclidean

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1



theorem exists_filling_of_negative_cap_complement
    {v : E3} {g : S2 → E3}
    (hg : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ g)
    {B : Set Real} (D : SphereSurgeryCoreCap v g B) (hs : D.scale < 0)
    (p : S2) (hp : p ∉ D.chart '' ball (0 : E2) 1)
    (hpheight : D.center < inner Real v (g p))
    (hunique : ∀ q ∉ D.chart '' ball (0 : E2) 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun y => inner Real v (g y)) q = 0 → q = p)
    (χ : OpenPartialHomeomorph E2 S2) (hχ0 : 0 ∈ χ.source) (hχp : χ 0 = p)
    (hχ : ContMDiffOn (𝓡 2) (𝓡 2) ∞ χ χ.source)
    (hχi : ContMDiffOn (𝓡 2) (𝓡 2) ∞ χ.symm χ.target)
    (hχtarget : χ.target ⊆ (D.chart '' ball (0 : E2) 1)ᶜ)
    (hχform : ∀ x ∈ χ.source,
      inner Real v (g (χ x)) = inner Real v (g p) - ‖x‖ ^ 2) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 = range g := by
  let R := heightReflection D.unit_v
  let G : S2 → E3 := fun q => R (g q)
  have hG : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ G := by
    apply Poincare.Geometry.Manifold.isSmoothEmbedding_of_injective_mfderiv
      (R.contMDiff.comp hg.contMDiff) (R.injective.comp hg.isEmbedding.injective)
    intro q
    rw [mfderiv_comp q (R.contMDiff.mdifferentiable (by simp) _)
      (hg.contMDiff.mdifferentiable (by simp) q)]
    exact (R.mfderivToContinuousLinearEquiv (by simp) (g q)).injective.comp
      (injective_mfderiv_sphere_embedding hg q)
  have hheight (q : S2) : inner Real v (G q) = -inner Real v (g q) :=
    inner_heightReflection D.unit_v _
  have huniq : ∀ q ∉ D.reflected.chart '' ball (0 : E2) 1,
      mfderiv (𝓡 2) 𝓘(Real, Real) (fun y => inner Real v (G y)) q = 0 → q = p := by
    intro q hq hc
    have heq : (fun y => inner Real v (G y)) = -(fun y => inner Real v (g y)) :=
      funext hheight
    rw [heq, mfderiv_neg, neg_eq_zero] at hc
    exact hunique q hq hc
  obtain ⟨A, hA⟩ := exists_filling_of_positive_cap_complement hG D.reflected
    (show 0 < D.reflected.scale from neg_pos.mpr hs) p hp
    (show inner Real v (G p) < D.reflected.center by rw [hheight]; exact neg_lt_neg hpheight)
    huniq χ hχ0 hχp hχ hχi hχtarget
    (fun x hx => by rw [hheight, hχform x hx, hheight]; ring)
  refine ⟨A.trans R, ?_⟩
  change (R ∘ A) '' sphere (0 : E3) 1 = _
  rw [image_comp, hA]
  change R '' range (R ∘ g) = _
  rw [range_comp, image_image]
  simp only [R, heightReflection_heightReflection, image_id']

namespace SphereMorseReduction

variable {f : S2 → E3} (M : SphereMorseReduction f)



theorem exists_filling_of_one_negative_cap {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    {B : Set Real} (D : SphereSurgeryCoreCap (M.v : E3) g B)
    (hcore : P.core = (D.chart '' ball (0 : E2) 1)ᶜ) (hs : D.scale < 0) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 = range g := by
  obtain ⟨p, hp, hpheight, _, hunique, χ, hχ0, hχp, hχ, hχi, hχtarget, hχform⟩ :=
    M.exists_maximum_chart_of_one_cap hg P hP D hcore hs
  apply exists_filling_of_negative_cap_complement (M.tree.embedding_of_mem_leaves hg) D hs
    p (by simpa only [hcore, mem_compl_iff] using interior_subset hp) hpheight
    (fun q hq hc => hunique q (by simpa only [hcore, mem_compl_iff] using hq) hc)
    χ hχ0 hχp hχ hχi _ hχform
  intro q hq
  simpa only [hcore] using interior_subset (hχtarget hq)



theorem exists_filling_of_one_cap {g : S2 → E3} (hg : g ∈ M.tree.leaves)
    (P : SphereSurgeryPath (M.v : E3) (fun p => M.D (f p)) g)
    (hP : P.Protects ((fun p => inner Real (M.v : E3) (M.D (f p))) ''
      {p | mfderiv (𝓡 2) 𝓘(Real, Real)
        (fun q => inner Real (M.v : E3) (M.D (f q))) p = 0}))
    {B : Set Real} (D : SphereSurgeryCoreCap (M.v : E3) g B)
    (hcore : P.core = (D.chart '' ball (0 : E2) 1)ᶜ) :
    ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      F '' sphere (0 : E3) 1 = range g := by
  rcases lt_or_gt_of_ne D.scale_ne_zero with hs | hs
  · exact M.exists_filling_of_one_negative_cap hg P hP D hcore hs
  · exact M.exists_filling_of_one_positive_cap hg P hP D hcore hs

end SphereMorseReduction

end Poincare.Manifold.Schoenflies
