import PoincareConjecture.Definitions.M62Geometry
import PoincareConjecture.Proofs.M62.Mathlib.LinearChartTransport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

noncomputable section

namespace PoincareConjecture.M62

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem nonempty_circleProductCharts {circumference : ℝ}
    (C : CircleGeometry circumference) :
    Nonempty (CircleProductCharts C n M) := by
  classical
  let : NormedAddCommGroup
      (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin 1))) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)))
  let : NormedSpace ℝ
      (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin 1))) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)))
  let : FiniteDimensional ℝ
      (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin 1))) :=
    inferInstanceAs (FiniteDimensional ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)))
  let productCharts : ChartedSpace
      (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin 1))) (M × C.Point) :=
    inferInstance
  have hprod : IsManifold
      𝓘(ℝ, ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin 1))) ∞ (M × C.Point) := by
    simpa [ModelProd, modelWithCornersSelf_prod] using
      (inferInstance : IsManifold ((𝓡 n).prod (𝓡 1)) ∞ (M × C.Point))
  let e : ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin 1)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (n + 1)) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      change Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin 1)) = _
      simp [Module.finrank_prod])
  obtain ⟨C', hC, hfrom, hto⟩ :=
    ContinuousLinearEquiv.exists_compatibleChartedSpace (r := ∞) e (M × C.Point)
  let Φ : Diffeomorph (𝓡 (n + 1)) ((𝓡 n).prod (𝓡 1)) (M × C.Point) (M × C.Point) ∞ :=
    { toEquiv := Equiv.refl _
      contMDiff_toFun := by simpa [ModelProd, modelWithCornersSelf_prod] using hto
      contMDiff_invFun := by simpa [ModelProd, modelWithCornersSelf_prod] using hfrom }
  let splitMap : ∀ q : M × C.Point, TangentSpace (𝓡 (n + 1)) q ≃L[ℝ]
      TangentSpace (𝓡 n) q.1 × TangentSpace (𝓡 1) q.2 :=
    fun q => Φ.mfderivToContinuousLinearEquiv (by simp) q
  refine ⟨{
    chartedSpace := C'
    isManifold := hC
    from_product_smooth := by simpa [ModelProd, modelWithCornersSelf_prod] using hfrom
    to_product_smooth := by simpa [ModelProd, modelWithCornersSelf_prod] using hto
    split := splitMap
    split_space := ?_
    split_circle := ?_ }⟩
  · intro q V
    have hcomp := mfderiv_comp_apply (f := Φ) (g := (Prod.fst : M × C.Point → M))
      q mdifferentiableAt_fst (Φ.contMDiff.mdifferentiableAt (x := q) (by simp)) V
    change ((mfderiv (𝓡 (n + 1)) ((𝓡 n).prod (𝓡 1)) Φ q) V).1 = _
    rw [mfderiv_fst] at hcomp
    exact hcomp.symm
  · intro q V
    have hcomp := mfderiv_comp_apply (f := Φ) (g := (Prod.snd : M × C.Point → C.Point))
      q mdifferentiableAt_snd (Φ.contMDiff.mdifferentiableAt (x := q) (by simp)) V
    change ((mfderiv (𝓡 (n + 1)) ((𝓡 n).prod (𝓡 1)) Φ q) V).2 = _
    rw [mfderiv_snd] at hcomp
    exact hcomp.symm

end PoincareConjecture.M62
