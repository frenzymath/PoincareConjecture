import PoincareConjecture.Proofs.M63.Mathlib.ImmersedCurveComposition
import PoincareConjecture.Proofs.M63.Mathlib.SmoothRetractionDifferentials
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessEmbeddedCurve










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι





theorem smoothShrinkingCurve_of_fixed_relabeling_and_smooth_slice
    (F : RicciFlow n M (Icc a b))
    {e : M → W} (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {U : Set W} (hU : IsOpen U) (heU : range e ⊆ U) {ρ : W → M}
    (hρ : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ ρ U) (hρe : ∀ p, ρ (e p) = p)
    {J : Set ℝ} {s : ℝ} (hs : s ∈ J) {c d : ℝ → ℝ → M}
    (hc : M63C2ShrinkingCurveOn F c J) (hd : M63SmoothShrinkingCurveOn F d J)
    (hcs : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => c x s))
    (hds : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) ∞ (fun x => d x s))
    {phi : ℝ → ℝ} (hphi : Continuous phi)
    (hrel : ∀ t ∈ J, ∀ x, c x t = d (phi x) t) :
    ContDiff ℝ ∞ phi ∧ M63SmoothShrinkingCurveOn F c J := by
  let f : ℝ → W := fun y => e (d y s)
  have hf : ContDiff ℝ ∞ f := (he.comp hds).contDiff
  have hdata := (c2ShrinkingCurve_embedded_closed_data hd.1 he).2.1
  have hleft := (smooth_retraction_differentials he hU heU hρ hρe).2.2
  have hne (y : ℝ) : deriv f y ≠ 0 := by
    have hder : HasDerivAt f
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (d y s)
          (curveVelocity (n := n) (fun z => d z s) y)) y := hdata s hs y
    rw [hder.deriv]
    intro hz
    have h := hleft (d y s) (curveVelocity (n := n) (fun z => d z s) y)
    erw [hz, map_zero] at h
    exact hd.1.immersed s hs y h.symm
  have hfc : ContDiff ℝ ∞ (f ∘ phi) := by
    have heq : f ∘ phi = fun x => e (c x s) :=
      funext fun x => congrArg e (hrel s hs x).symm
    rw [heq]
    exact (he.comp hcs).contDiff
  have hphis : ContDiff ℝ ∞ phi := contDiff_iff_contDiffAt.mpr fun x =>
    contDiffAt_of_comp_immersed_curve (by simp) (hphi.continuousAt)
      hf.contDiffAt (hne (phi x)) hfc.contDiffAt
  have hmap : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞
      (fun z : ℝ × ℝ => (phi z.1, z.2)) :=
    ((hphis.comp contDiff_fst).prodMk contDiff_snd).contMDiff
  refine ⟨hphis, hc, ?_⟩
  apply (hd.2.comp hmap.contMDiffOn (fun z hz => ⟨mem_univ _, hz.2⟩)).congr
  intro z hz
  exact hrel z.2 (interior_subset hz.2) z.1

end PoincareConjecture.M63
