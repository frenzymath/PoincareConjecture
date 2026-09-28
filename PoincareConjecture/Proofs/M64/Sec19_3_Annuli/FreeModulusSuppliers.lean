import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.ModulusFreeBoundaryTransport
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFreeModulusApproximation














set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]





theorem m64C2ShrinkingCurves_free_modulus_suppliers
    {a b : ℝ} (F : RicciFlow n M (Icc a b))
    {c0 c1 : ℝ → ℝ → M}
    (hc0 : M63C2ShrinkingCurveOn F c0 (Icc a b))
    (hc1 : M63C2ShrinkingCurveOn F c1 (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    M64FreeConformalModulusApproximation (F.metric t)
        (fun x => c0 x t) (fun x => c1 x t) ∧
      M64FreeBoundaryAreaTransport (F.metric t)
        (fun x => c0 x t) (fun x => c1 x t) := by
  have h0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun x => c0 x t) :=
    (hc0.spatial_regular t ht).of_le (by norm_num)
  have h1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 1 (fun x => c1 x t) :=
    (hc1.spatial_regular t ht).of_le (by norm_num)
  refine ⟨?_, ?_⟩
  · exact M64Uniformization.m64FreeConformalModulusApproximation_of_C1
      (F.metric t) h0 h1
  · exact m64C2ShrinkingCurves_freeBoundaryAreaTransport F hc0 hc1 ht

end PoincareConjecture
