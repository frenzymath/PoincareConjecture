import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.SmoothAnnulusAdmission
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusLipschitzSeed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

universe u

variable {n m : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem m64FreeReplacement_admit_ownObservedSeed
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    {f : LoopPlane → M} {U : Set LoopPlane}
    (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U)
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hlower : ∀ x, f (annulusPoint x 0) = c0 x)
    (hupper : ∀ x, f (annulusPoint x 1) = c1 x)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) :
    ∃ A : M64Annulus g c0 c1, A.map = f ∧
      ∃ W : M64ObservedWeakAnnulus (n := n) e c0 c1,
        W.map = f ∧
          ∀ i, ∀ᵐ p ∂volume.restrict (interior m64AnnulusDomain),
            W.column i p =
              fderiv ℝ (e ∘ f) p (EuclideanSpace.single i 1) := by
  obtain ⟨A, hA⟩ := m64Annulus_exists_eq_of_contMDiffOn g hU hdom hf
    hperiodic hlower hupper
  obtain ⟨W, hW, hcolumn⟩ := m64ObservedWeakAnnulus_of_annulus A e he
  refine ⟨A, hA, W, ?_, ?_⟩
  · simpa only [hA] using hW
  · intro i
    filter_upwards [hcolumn i] with p hp
    simpa only [hA] using hp

end PoincareConjecture
