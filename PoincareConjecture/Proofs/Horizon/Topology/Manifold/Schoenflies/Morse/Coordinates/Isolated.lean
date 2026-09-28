import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Critical
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Coordinates.Surface
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.Morse.SignedSquares









noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1
private abbrev P := E2 × Real



theorem mfderiv_eq_zero_iff_eq_zero_in_morse_coordinates
    {h : S2 -> Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h)
    (e : OpenPartialHomeomorph E2 S2)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (c : Real) (σ : Fin 2 -> Real) (hσ : ∀ i, σ i ≠ 0)
    (hform : ∀ x ∈ e.source, h (e x) = c + ∑ i : Fin 2, σ i * x i ^ 2)
    {x : E2} (hx : x ∈ e.source) :
    mfderiv (𝓡 2) 𝓘(Real, Real) h (e x) = 0 ↔ x = 0 := by
  rw [mfderiv_eq_zero_iff_fderiv_of_sphere_coordinates_eqOn hh e he hei hx hform]
  exact Poincare.Analysis.Calculus.Morse.fderiv_diagonal_quadratic_eq_zero_iff c σ hσ x



theorem height_critical_iff_eq_of_exact_morse_coordinates
    {f : S2 -> E3} (hf : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ f)
    (v p : S2)
    (e : OpenPartialHomeomorph E2 S2) (he0 : 0 ∈ e.source) (hep : e 0 = p)
    (he : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target)
    (σ : Fin 2 -> Real) (hσ : ∀ i, σ i = -1 ∨ σ i = 1)
    (hform : ∀ x ∈ e.source, inner Real (v : E3) (f (e x)) =
      inner Real (v : E3) (f p) + ∑ i : Fin 2, σ i * x i ^ 2)
    (F : OpenPartialHomeomorph P E3) (hFs : F.source ⊆ e.source ×ˢ univ)
    (hFeq : ∀ z ∈ F.source, F z = f (e z.1) + z.2 • (v : E3))
    (hsection : range f ∩ F.target = F '' (F.source ∩ {z : P | z.2 = 0}))
    (q : S2) (hq : f q ∈ F.target) :
    mfderiv (𝓡 2) 𝓘(Real, Real) (fun r => inner Real (v : E3) (f r)) q = 0 ↔
      q = p := by
  have hqsection : f q ∈ F '' (F.source ∩ {z : P | z.2 = 0}) := by
    rw [← hsection]
    exact ⟨⟨q, rfl⟩, hq⟩
  obtain ⟨z, ⟨hz, hzt⟩, hzq⟩ := hqsection
  have heq : e z.1 = q := hf.isEmbedding.injective (by
    rw [hFeq z hz, hzt, zero_smul, add_zero] at hzq
    exact hzq)
  have hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞
      (fun r => inner Real (v : E3) (f r)) :=
    (innerSL Real (v : E3)).contMDiff.comp hf.contMDiff
  have hσne (i : Fin 2) : σ i ≠ 0 := by
    rcases hσ i with hi | hi <;> simp [hi]
  rw [← heq, mfderiv_eq_zero_iff_eq_zero_in_morse_coordinates hh e he hei
    (inner Real (v : E3) (f p)) σ hσne hform (hFs hz).1]
  constructor
  · intro hz0
    rw [hz0, hep]
  · intro hp
    exact e.injOn (hFs hz).1 he0 (hp.trans hep.symm)

end Poincare.Manifold.Schoenflies
