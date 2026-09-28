import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeUniformizationCertificate
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeakAnnulusLipschitzSeed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture

universe u

variable {n m : ℕ} {M : Type u} [TopologicalSpace M]
  [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem m64FreeMorreyCandidate_ownObservedWeakMap
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    {A : M64Annulus g c0 c1} {eps : ℝ}
    (C : M64FreeMorreyUniformizationCandidate g c0 c1 A eps)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) :
    ∃ W : M64ObservedWeakAnnulus (n := n) e
        (c0 ∘ C.sigma0.map) (c1 ∘ C.sigma1.map),
      W.map = C.annulus.map ∧
      ∀ i, ∀ᵐ p ∂volume.restrict (interior m64AnnulusDomain),
        W.column i p =
          fderiv ℝ (e ∘ C.annulus.map) p
            (EuclideanSpace.single i 1) := by
  obtain ⟨W, hW, hcolumn⟩ := m64ObservedWeakAnnulus_of_annulus C.annulus e he
  exact ⟨W, hW, hcolumn⟩

end PoincareConjecture
