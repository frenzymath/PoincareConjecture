import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.MFDeriv.Atlas








set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem inverseChartVector_smooth (p : M) (v : E) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y : E ↦ Bundle.TotalSpace.mk' E ((chartAt E p).symm y)
        (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y v))
      (chartAt E p).target := by
  have hc : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chartAt E p).symm (chartAt E p).target :=
    contMDiffOn_chart_symm
  have ht := hc.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
    (chartAt E p).open_target.uniqueMDiffOn
  have hv : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞
      (fun y : E ↦ (⟨y, v⟩ : TangentBundle (𝓡 n) E)) :=
    (contMDiff_vectorSpace_iff_contDiff (V := fun _ : E ↦ v)).mpr contDiff_const
  have h := ht.comp hv.contMDiffOn (fun y hy ↦ hy)
  apply h.congr
  intro y hy
  change Bundle.TotalSpace.mk' E ((chartAt E p).symm y)
      (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y v) =
    Bundle.TotalSpace.mk' E ((chartAt E p).symm y)
      (mfderivWithin (𝓡 n) (𝓡 n) (chartAt E p).symm (chartAt E p).target y v)
  rw [mfderivWithin_of_isOpen (chartAt E p).open_target hy]

theorem inverseChartDifferential_bijective (p : M) (y : E)
    (hy : y ∈ (chartAt E p).target) :
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) (chartAt E p).symm y) :=
  (mdifferentiable_chart (I := 𝓡 n) p).symm.mfderiv_bijective hy

end PoincareConjecture.Proofs.M09
