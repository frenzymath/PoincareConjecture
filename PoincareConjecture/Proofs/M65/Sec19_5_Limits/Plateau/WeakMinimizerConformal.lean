import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.WeakMinimizerClass












set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M65WeakDisk

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}




def Conformal (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M) : Prop :=
  ∀ᵐ z ∂volume.restrict loopDiskSet,
    let H := m65EmbeddingMetric g e (F.value z)
    H (F.derivative 0 z) (F.derivative 0 z) = H (F.derivative 1 z) (F.derivative 1 z) ∧
      H (F.derivative 0 z) (F.derivative 1 z) = 0




def areaDensity (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M) (z : LoopPlane) : ℝ :=
  let H := m65EmbeddingMetric g e (F.value z)
  Real.sqrt (H (F.derivative 0 z) (F.derivative 0 z) *
    H (F.derivative 1 z) (F.derivative 1 z) - (H (F.derivative 0 z) (F.derivative 1 z)) ^ 2)



def area (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M) : ℝ :=
  ∫ z in loopDiskSet, F.areaDensity g z





theorem energy_eq_area (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M)
    (hF : F.Conformal g) : F.energy g = F.area g := by
  unfold energy area
  apply integral_congr_ae
  filter_upwards [hF] with z hz
  dsimp only [areaDensity, m65EmbeddedEnergyDensity]
  rw [Fin.sum_univ_two, ← hz.1, hz.2, zero_pow (by norm_num), sub_zero, ← pow_two,
    Real.sqrt_sq (m65EmbeddingMetric_nonneg g e (F.value z) (F.derivative 0 z))]
  ring

end PoincareConjecture.M65WeakDisk
