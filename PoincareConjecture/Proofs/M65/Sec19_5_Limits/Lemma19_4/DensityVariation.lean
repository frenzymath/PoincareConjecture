import PoincareConjecture.Definitions.M60Area
import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Proofs.M07.Analysis.Matrix.Determinant
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m65AreaGram_det_nonneg (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) :
    0 ≤ (m60AreaGram g f z).det := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact (Matrix.posSemidef_gram ℝ
    (fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 n) f z
      (EuclideanSpace.basisFun (Fin 2) ℝ i))).det_nonneg

theorem m65AreaGram_det_ne_zero_iff (g : RiemannianMetric n M)
    (f : LoopPlane → M) (z : LoopPlane) :
    (m60AreaGram g f z).det ≠ 0 ↔
      LinearIndependent ℝ (fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 n) f z
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)
    (v := fun i : Fin 2 => mfderiv (𝓡 2) (𝓡 n) f z
      (EuclideanSpace.basisFun (Fin 2) ℝ i))

noncomputable def m65PlaneRicciTraceDensity {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : LoopPlane → M) (z : LoopPlane) : ℝ :=
  let e : Fin 2 → TangentSpace (𝓡 n) (f z) := fun i =>
    mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let G := m60AreaGram g f z
  if G.det = 0 then 0
  else Matrix.trace (G⁻¹ * Matrix.of (fun i j => D.ricci (f z) (e i) (e j))) *
    m60AreaDensity g f z

theorem m65AreaDensity_metric_hasDerivAt {J : Set ℝ}
    (F : RicciFlow n M J) (f : LoopPlane → M) (z : LoopPlane)
    {t : ℝ} (ht : t ∈ interior J) :
    HasDerivAt (fun s => m60AreaDensity (F.metric s) f z)
      (-m65PlaneRicciTraceDensity (F.connection t) f z) t := by
  classical
  let e : Fin 2 → TangentSpace (𝓡 n) (f z) := fun i =>
    mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  let G : ℝ → Matrix (Fin 2) (Fin 2) ℝ := fun s => m60AreaGram (F.metric s) f z
  let R : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.of (fun i j => (F.connection t).ricci (f z) (e i) (e j))
  by_cases hzero : (G t).det = 0
  · have hall (s : ℝ) : (G s).det = 0 := by
      by_contra hs
      have hlin := (m65AreaGram_det_ne_zero_iff (F.metric s) f z).mp hs
      exact ((m65AreaGram_det_ne_zero_iff (F.metric t) f z).mpr hlin) hzero
    have hfun : (fun s => m60AreaDensity (F.metric s) f z) = fun _ => 0 := by
      funext s
      simp only [m60AreaDensity, show (m60AreaGram (F.metric s) f z).det = 0 from hall s,
        max_self, Real.sqrt_zero]
    rw [hfun]
    simpa only [m65PlaneRicciTraceDensity,
      show (m60AreaGram (F.metric t) f z).det = 0 from hzero, if_pos, neg_zero] using
      hasDerivAt_const t (0 : ℝ)
  · have hpos : 0 < (G t).det :=
      lt_of_le_of_ne (m65AreaGram_det_nonneg (F.metric t) f z) (Ne.symm hzero)
    have hG (i j : Fin 2) : HasDerivAt (fun s => G s i j) (((-2 : ℝ) • R) i j) t := by
      exact (F.equation t (interior_subset ht) (f z) (e i) (e j)).hasDerivAt
        (mem_interior_iff_mem_nhds.mp ht)
    have h := Poincare.Matrix.hasDerivAt_sqrt_det_eq_half_trace_inv_mul
      G ((-2 : ℝ) • R) t hG hpos
    have hfun : (fun s => m60AreaDensity (F.metric s) f z) =
        fun s => Real.sqrt (G s).det := by
      funext s
      exact congrArg Real.sqrt (max_eq_right (m65AreaGram_det_nonneg (F.metric s) f z))
    rw [hfun]
    convert h using 1
    simp only [m65PlaneRicciTraceDensity, show (m60AreaGram (F.metric t) f z).det ≠ 0
      from hzero, if_false, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
      m60AreaDensity, max_eq_right (m65AreaGram_det_nonneg (F.metric t) f z)]
    change -(Matrix.trace ((G t)⁻¹ * R) * Real.sqrt (G t).det) = _
    ring

end PoincareConjecture
