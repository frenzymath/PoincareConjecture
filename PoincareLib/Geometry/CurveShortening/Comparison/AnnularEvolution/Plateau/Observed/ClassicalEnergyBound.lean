import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.AnnulusEnergyIdentity

/-! The original bounded observed metric controls the actual classical
column energy density. Source: Morrey's coordinate energy estimates;
M64 finite-boundary-regularity derivation.
Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareMT

/-- The original intrinsic energy is bounded by the squared actual observed columns, using
the original tangent-diagonal identity. Proof expansion for Morgan-Tian (2007), Lemma 19.15,
pp. 447-449. -/
theorem m64ObservedMetric_energyDensity_le_columns {n m : ℕ} {M : Type*}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (e : M → EuclideanSpace ℝ (Fin m))
    (he : ContMDiff (𝓡 n) (𝓡 m) 1 e)
    (B : M → EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (hdiag : ∀ (q : M) (v : TangentSpace (𝓡 n) q),
      B q (mfderiv (𝓡 n) (𝓡 m) e q v) (mfderiv (𝓡 n) (𝓡 m) e q v) = g.inner q v v)
    {f : LoopPlane → M} {p : LoopPlane} (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f p)
    {bound : ℝ} (hb : ‖B (f p)‖ ≤ bound) :
    m60EnergyDensity g f p ≤ (bound / 2) *
      ∑ i : Fin 2, ‖fderiv ℝ (e ∘ f) p (EuclideanSpace.single i 1)‖ ^ 2 := by
  have hterm (i : Fin 2) : m60AreaGram g f p i i ≤
      bound * ‖fderiv ℝ (e ∘ f) p (EuclideanSpace.single i 1)‖ ^ 2 := by
    rw [← m64ObservedMetric_diagonal_of_mDifferentiableAt g e he B hdiag hf i]
    let v := fderiv ℝ (e ∘ f) p (EuclideanSpace.single i 1)
    calc
      B (f p) v v ≤ |B (f p) v v| := le_abs_self _
      _ ≤ ‖B (f p)‖ * ‖v‖ * ‖v‖ := (B (f p)).le_opNorm₂ v v
      _ = ‖B (f p)‖ * ‖v‖ ^ 2 := by ring
      _ ≤ bound * ‖v‖ ^ 2 := mul_le_mul_of_nonneg_right hb (sq_nonneg ‖v‖)
  simp only [m60EnergyDensity, Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  linarith [hterm 0, hterm 1]

end PoincareMT
