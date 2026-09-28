import PoincareConjecture.Proofs.M10.PullbackJacobian
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.Atlas










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem mfderiv_bijective_of_pullbackJacobian_pos (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hJ : 0 < pullbackJacobian g f x) :
    Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) (f x)) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) (f x)
  let D : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] TangentSpace (𝓡 n) (f x) :=
    (mfderiv (𝓡 n) (𝓡 n) f x).toLinearMap
  rw [pullbackJacobian_eq_normDet] at hJ
  have hker : D.ker = ⊥ := by
    by_contra hne
    exact hJ.ne' (LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hne)
  have hinj : Function.Injective D := LinearMap.ker_eq_bot.mp hker
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by rfl) (f := D)).mp hinj⟩

set_option backward.isDefEq.respectTransparency false in

theorem isOpenMap_of_mfderiv_bijective {f : EuclideanSpace ℝ (Fin n) → M}
    (hf : ContMDiff (𝓡 n) (𝓡 n) ∞ f)
    (hD : ∀ x, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x)) :
    IsOpenMap f := by
  apply isOpenMap_iff_nhds_le.mpr
  intro x
  let c := chartAt (EuclideanSpace ℝ (Fin n)) (f x)
  let H : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := c ∘ f
  have hc : f x ∈ c.source := mem_chart_source _ _
  have hH : ContDiffAt ℝ ∞ H x := by
    have hh := ((contMDiffAt_extChartAt' (I := 𝓡 n) (n := ∞) hc).comp x (hf x)).contDiffAt
    simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] using hh
  have hdH : Function.Bijective (fderiv ℝ H x) := by
    have hd := mfderiv_comp x (mdifferentiableAt_extChartAt hc)
      ((hf x).mdifferentiableAt (by simp))
    rw [mfderiv_eq_fderiv, mfderiv_extChartAt_self, ContinuousLinearMap.id_comp] at hd
    have heq : fderiv ℝ H x = mfderiv (𝓡 n) (𝓡 n) f x := by
      simpa only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp] using hd
    rw [heq]
    exact hD x
  let L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.ofBijective (fderiv ℝ H x).toLinearMap hdH).toContinuousLinearEquiv
  have hder : HasFDerivAt H (L : EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n)) x := (hH.differentiableAt (by simp)).hasFDerivAt
  let e := hH.toOpenPartialHomeomorph H hder (by simp)
  have he : x ∈ e.source := hH.mem_toOpenPartialHomeomorph_source hder (by simp)
  have hmap : map H (𝓝 x) = 𝓝 (H x) := e.map_nhds_eq he
  have heq : (c.symm ∘ H) =ᶠ[𝓝 x] f := by
    filter_upwards [(hf x).continuousAt (c.open_source.mem_nhds hc)] with y hy
    exact c.left_inv hy
  have hmapf : map f (𝓝 x) = 𝓝 (f x) := by
    calc
      map f (𝓝 x) = map c.symm (map H (𝓝 x)) := by
        rw [map_map]
        exact Filter.map_congr heq.symm
      _ = map c.symm (𝓝 (H x)) := congrArg (map c.symm) hmap
      _ = 𝓝 (f x) := c.symm_map_nhds_eq hc
  exact hmapf.ge

end PoincareConjecture.M10
