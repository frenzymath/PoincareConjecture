import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.ConformalRicci
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.GaussContraction

noncomputable section

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Manifold Bundle InnerProductSpace BigOperators

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem m65PlaneRicciTraceDensity_eq_scalar_sub_normal
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (f : LoopPlane → M) (z : LoopPlane) {c : ℝ} (hc : 0 < c)
    (hconf : m60AreaGram g f z = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (N : TangentSpace (𝓡 3) (f z)) (hN : g.inner (f z) N N = 1)
    (hNT : ∀ i : Fin 2, g.inner (f z) N
      (mfderiv (𝓡 2) (𝓡 3) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)) = 0) :
    m65PlaneRicciTraceDensity D f z =
      c * (D.scalarCurvature (f z) - D.ricci (f z) N N) := by
  classical
  let e : Fin 2 → TangentSpace (𝓡 3) (f z) := fun i =>
    mfderiv (𝓡 2) (𝓡 3) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have he (i j : Fin 2) : g.inner (f z) (e i) (e j) = if i = j then c else 0 := by
    have hh := congrArg (fun G : Matrix (Fin 2) (Fin 2) ℝ => G i j) hconf
    simpa only [m60AreaGram, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero, e] using hh
  let r := Real.sqrt c
  have hr : r ≠ 0 := (Real.sqrt_pos.2 hc).ne'
  have hr2 : r ^ 2 = c := Real.sq_sqrt hc.le
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 3) (f z)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) (f z)
  let v : Option (Fin 2) → TangentSpace (𝓡 3) (f z) :=
    fun i => i.elim N (fun j => r⁻¹ • e j)
  have hv : Orthonormal ℝ v := by
    rw [orthonormal_iff_ite]
    intro i j
    cases i with
    | none =>
      cases j with
      | none => exact hN
      | some j =>
        change g.inner (f z) N (r⁻¹ • e j) = 0
        simp only [map_smul, smul_eq_mul, hNT, e, mul_zero]
    | some i =>
      cases j with
      | none =>
        change g.inner (f z) (r⁻¹ • e i) N = 0
        rw [g.symm]
        simp only [map_smul, smul_eq_mul, hNT, e, mul_zero]
      | some j =>
        change g.inner (f z) (r⁻¹ • e i) (r⁻¹ • e j) =
          if some i = some j then 1 else 0
        simp only [map_smul, smul_apply, smul_eq_mul, he, Option.some.injEq]
        split_ifs with hij
        · rw [← hr2]
          field_simp
        · simp
  have hcard : Fintype.card (Option (Fin 2)) =
      Module.finrank ℝ (TangentSpace (𝓡 3) (f z)) := by
    rw [VectorBundle.finrank_eq ℝ (EuclideanSpace ℝ (Fin 3)), finrank_euclideanSpace]
    simp
  let a := basisOfOrthonormalOfCardEqFinrank hv hcard
  let b := a.toOrthonormalBasis (show Orthonormal ℝ a by simpa [a] using hv)
  have hb0 : b none = N := by simp [b, a, v]
  have hbi (i : Fin 2) : b (some i) = r⁻¹ • e i := by simp [b, a, v]
  have hs := M13.scalarCurvature_eq_sum_basis D (f z) b
  have hscale (i : Fin 2) : D.ricci (f z) (r⁻¹ • e i) (r⁻¹ • e i) =
      r⁻¹ * r⁻¹ * D.ricci (f z) (e i) (e i) := by
    simp only [← M13.ricciLinear_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  simp only [Fintype.sum_option, hb0, hbi, hscale, ← Finset.mul_sum] at hs
  rw [m65PlaneRicciTraceDensity_eq_sum_of_conformal D f z c hconf]
  change (∑ i : Fin 2, D.ricci (f z) (e i) (e i)) = _
  rw [hs, add_sub_cancel_left, ← hr2]
  field_simp

end PoincareConjecture
