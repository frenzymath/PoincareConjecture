import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.RegularLevel.UniversalProperty
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Algebra.Structures

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle Topology

namespace Poincare.Geometry.Manifold.RegularLevel

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [IsManifold (𝓡 (n + 1)) ∞ M] {f : M → ℝ}

private def productEquivOfFlow (Φ : ℝ → M → M)
    (h0 : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hscalar : ∀ t x, f (Φ t x) = f x + t) :
    (openLevelSet f (⊤ : Opens M) 0 × ℝ) ≃ M where
  toFun z := Φ z.2 (openLevelIncl f (⊤ : Opens M) 0 z.1)
  invFun x := (⟨⟨Φ (-f x) x, mem_univ _⟩, by simp [hscalar]⟩, f x)
  left_inv z := by
    have hz : f (openLevelIncl f (⊤ : Opens M) 0 z.1) = 0 := z.1.2
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      change Φ (-f (Φ z.2 (openLevelIncl f (⊤ : Opens M) 0 z.1)))
          (Φ z.2 (openLevelIncl f (⊤ : Opens M) 0 z.1)) =
        openLevelIncl f (⊤ : Opens M) 0 z.1
      rw [hscalar, hz, zero_add, ← hadd, neg_add_cancel, h0]
    · change f (Φ z.2 (openLevelIncl f (⊤ : Opens M) 0 z.1)) = z.2
      rw [hscalar, hz, zero_add]
  right_inv x := by
    change Φ (f x) (Φ (-f x) x) = x
    rw [← hadd, add_neg_cancel, h0]

def productDiffeomorphOfFlow
    (hf : ContMDiff (𝓡 (n + 1)) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) f x ≠ 0)
    (Φ : ℝ → M → M)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 (n + 1))) (𝓡 (n + 1)) ∞
      (fun z : ℝ × M => Φ z.1 z.2))
    (h0 : ∀ x, Φ 0 x = x) (hadd : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hscalar : ∀ t x, f (Φ t x) = f x + t) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openLevelSetChartedSpace hf (⊤ : Opens M) (fun x _ => hreg x) n 0
    letI := isManifold_openLevelSet hf (⊤ : Opens M) (fun x _ => hreg x) n 0
    (openLevelSet f (⊤ : Opens M) 0 × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let hregular := fun x (_ : x ∈ (⊤ : Opens M)) => hreg x
  letI := openLevelSetChartedSpace hf (⊤ : Opens M) hregular n 0
  letI := isManifold_openLevelSet hf (⊤ : Opens M) hregular n 0
  let e := productEquivOfFlow Φ h0 hadd hscalar
  have he : ContMDiff ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) ∞ e :=
    hs.comp (contMDiff_snd.prodMk
      ((contMDiff_openLevelIncl hf (⊤ : Opens M) hregular n 0).comp contMDiff_fst))
  have hr : ContMDiff (𝓡 (n + 1)) (𝓡 n) ∞ (fun x => (e.symm x).1) := by
    intro x
    apply (contMDiffAt_into_openLevelSet_iff hf n 0 (⊤ : Opens M) hregular
      (fun x => (e.symm x).1) x).mpr
    exact (hs.comp (hf.neg.prodMk contMDiff_id)) x
  exact ⟨e, he, hr.prodMk hf⟩

end Poincare.Geometry.Manifold.RegularLevel
