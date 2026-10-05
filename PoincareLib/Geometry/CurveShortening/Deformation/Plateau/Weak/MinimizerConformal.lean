import PoincareLib.Geometry.CurveShortening.Deformation.Plateau.Weak.MinimizerClass

/-!
# Literal weak conformality and area

The coefficients are the actual embedding metric evaluated on the same
weak derivative classes as the energy. Pointwise conformality makes
the literal Gram area equal to half-energy, including zero derivatives.
This file does not assert vanishing of the Hopf differential.
Source: Morgan--Tian Lemma 19.2, printed pp. 437-438, and Morrey ICM
1950, pp. 183-185; M65 derivation 39.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M65WeakDisk

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M] {N : ℕ} {e : M → EuclideanSpace ℝ (Fin N)} {γ : LoopCircle → M}

/-- Literal weak conformality of the actual derivative fields, with
their original target points and the actual embedding metric.
Source: MT Lemma 19.2, pp. 437-438; derivation 39. -/
def Conformal (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M) : Prop :=
  ∀ᵐ z ∂volume.restrict loopDiskSet,
    let H := m65EmbeddingMetric g e (F.value z)
    H (F.derivative 0 z) (F.derivative 0 z) = H (F.derivative 1 z) (F.derivative 1 z) ∧
      H (F.derivative 0 z) (F.derivative 1 z) = 0

/-- The actual weak Gram area density of the same disk. No regular
representative or first derivative of such a representative is assumed.
Source: MT Lemma 19.2, pp. 437-438; derivation 39. -/
def areaDensity (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M) (z : LoopPlane) : ℝ :=
  let H := m65EmbeddingMetric g e (F.value z)
  Real.sqrt (H (F.derivative 0 z) (F.derivative 0 z) *
    H (F.derivative 1 z) (F.derivative 1 z) - (H (F.derivative 0 z) (F.derivative 1 z)) ^ 2)

/-- Literal weak area is the integral of the actual Gram density.
Source: MT Lemma 19.2, pp. 437-438; derivation 39. -/
def area (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M) : ℝ :=
  ∫ z in loopDiskSet, F.areaDensity g z

/-- Proved weak conformality gives literal energy equal to literal
area, including the points where both derivatives vanish. The actual
conformality producer is a separate variational theorem.
Source: MT Lemma 19.2, pp. 437-438; derivation 39. -/
theorem energy_eq_area (F : M65WeakDisk e γ) (g : RiemannianMetric 3 M)
    (hF : F.Conformal g) : F.energy g = F.area g := by
  unfold energy area
  apply integral_congr_ae
  filter_upwards [hF] with z hz
  dsimp only [areaDensity, m65EmbeddedEnergyDensity]
  rw [Fin.sum_univ_two, ← hz.1, hz.2, zero_pow (by norm_num), sub_zero, ← pow_two,
    Real.sqrt_sq (m65EmbeddingMetric_nonneg g e (F.value z) (F.derivative 0 z))]
  ring

end PoincareMT.M65WeakDisk
