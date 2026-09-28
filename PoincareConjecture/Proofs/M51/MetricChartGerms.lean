import PoincareConjecture.Definitions.Ch15.SurgeryFlow
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.LocalIsometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M51

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem mfderiv_translatedChart (q : M) (z y : EuclideanSpace ℝ (Fin 3))
    (hy : y + z ∈ (extChartAt (𝓡 3) q).target) :
    mfderiv (𝓡 3) (𝓡 3) (fun w => (extChartAt (𝓡 3) q).symm (w + z)) y =
      mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm (y + z) := by
  have hc := (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).contMDiffAt
    ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hy)
  have ht : ContDiff ℝ ∞ (fun w : EuclideanSpace ℝ (Fin 3) => w + z) :=
    contDiff_id.add contDiff_const
  rw [show (fun w => (extChartAt (𝓡 3) q).symm (w + z)) =
    (extChartAt (𝓡 3) q).symm ∘ (fun w => w + z) from rfl,
    mfderiv_comp y (hc.mdifferentiableAt (by simp))
      (ht.contMDiff.mdifferentiable (by simp) y)]
  simp only [mfderiv_eq_fderiv, fderiv_add_const, fderiv_fun_id]
  ext v
  rfl

theorem exists_shiftedChartMetric (g : RiemannianMetric 3 M) (q : M)
    (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ (extChartAt (𝓡 3) q).target) :
    ∃ (G : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (DG : LeviCivitaData G),
      (∀ D : LeviCivitaData g,
        DG.curvatureTensorNorm 0 = D.curvatureTensorNorm ((extChartAt (𝓡 3) q).symm z)) ∧
      ∀ k : ℕ, ∀ a b : Fin 3,
        iteratedFDeriv ℝ k (fun y => G.inner y
          (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) 0 =
        iteratedFDeriv ℝ k (singularMetricCoefficient g q a b) z := by
  let c := extChartAt (𝓡 3) q
  let U := (fun y : EuclideanSpace ℝ (Fin 3) => y + z) ⁻¹' c.target
  let B := fun y => g.pullbackCoefficients c.symm (y + z)
  have hU : IsOpen U := (isOpen_extChartAt_target (I := 𝓡 3) q).preimage
    (continuous_id.add continuous_const)
  have hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ U := by
    change 0 + z ∈ c.target
    rw [zero_add]
    exact hz
  have hB : ContDiffOn ℝ ∞ B U := by
    intro y hy
    apply ContDiffAt.contDiffWithinAt
    exact ((g.contDiffOn_chartCoefficients q).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hy)).comp y
        (contDiffAt_id.add contDiffAt_const)
  have hsymm : ∀ y ∈ U, ∀ v w, B y v w = B y w v := by
    intro y _ v w
    exact g.symm _ _ _
  have hpos : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < B y v v := by
    intro y hy v hv
    apply g.pos
    intro hzero
    have hinv := isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 3) hy
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hinv
    apply hv
    apply hinv.injective
    rw [map_zero]
    exact hzero
  obtain ⟨G, DG, V, hV, hzeroV, hVU, hG⟩ :=
    RiemannianMetric.exists_local_realization hU hzero B hB hsymm hpos
  have hgerm : G.euclideanCoefficients =ᶠ[𝓝 0] B :=
    Filter.mem_of_superset (hV.mem_nhds hzeroV) hG
  have hcoeff : G.euclideanCoefficients =ᶠ[𝓝 0]
      g.pullbackCoefficients (fun y => c.symm (y + z)) := by
    filter_upwards [hgerm, hU.mem_nhds hzero] with y hy hyU
    rw [hy]
    ext v w
    change g.inner _ (mfderiv (𝓡 3) (𝓡 3) c.symm (y + z) v)
        (mfderiv (𝓡 3) (𝓡 3) c.symm (y + z) w) =
      g.inner _ (mfderiv (𝓡 3) (𝓡 3) (fun y => c.symm (y + z)) y v)
        (mfderiv (𝓡 3) (𝓡 3) (fun y => c.symm (y + z)) y w)
    rw [mfderiv_translatedChart q z y hyU]
    rfl
  refine ⟨G, DG, ?_, ?_⟩
  · intro D
    have hc := (contMDiffOn_extChartAt_symm (I := 𝓡 3) (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hz)
    have he : ContMDiffAt (𝓡 3) (𝓡 3) ∞ (fun y => c.symm (y + z)) 0 := by
      apply hc.comp_of_eq (x := (0 : EuclideanSpace ℝ (Fin 3)))
        ((contDiffAt_id.add contDiffAt_const).contMDiffAt)
      simp
    simpa only [zero_add] using DG.curvatureTensorNorm_eq_of_pullback_germ D he hcoeff
  · intro k a b
    have heq : (fun y => G.inner y (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 0]
        (fun y => singularMetricCoefficient g q a b (y + z)) := by
      filter_upwards [hgerm] with y hy
      exact congrArg (fun C => C (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) hy
    rw [(heq.iteratedFDeriv ℝ k).eq_of_nhds,
      iteratedFDeriv_comp_add_right, zero_add]

end PoincareConjecture.M51
