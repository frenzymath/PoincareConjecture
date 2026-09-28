import PoincareConjecture.Proofs.M05.Geometry.Riemannian.Metric.Pullback
import PoincareConjecture.Definitions.Ch09.RoundCylinderGeometry
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

set_option autoImplicit false

open Set Manifold IsManifold
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.Proofs.M28.NeckAnalysis

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

private theorem contDiffAt_pullback_inner
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : RiemannianMetric 3 M) {f : E → M} {x : E}
    (hf : ContMDiffAt 𝓘(ℝ, E) (𝓡 3) ∞ f x) (v w : E) :
    ContDiffAt ℝ ∞ (fun y => g.inner (f y)
      (mfderiv 𝓘(ℝ, E) (𝓡 3) f y v)
      (mfderiv 𝓘(ℝ, E) (𝓡 3) f y w)) x := by
  have hg := (g.contMDiff (f x)).comp x hf
  have h := hg.clm_bundle_apply₂ (F₃ := ℝ) (E₃ := Bundle.Trivial M ℝ)
    (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf v)
    (RiemannianMetric.contMDiffAt_mfderiv_const_vector hf w)
  apply contMDiffAt_iff_contDiffAt.mp
  simpa using (Bundle.contMDiffAt_totalSpace.mp h).2

theorem roundCylinderPullback_smooth
    (g : RiemannianMetric 3 M) {epsilon : ℝ} {f : RoundCylinderSpace → M}
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f
      (univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹)) :
    RoundCylinderTensorSmoothOn epsilon (roundCylinderPullback g f) := by
  intro q a b p hp
  let c := chartAt (EuclideanSpace ℝ (Fin 2)) q
  let h : RoundCylinderCoordinates → RoundCylinderSpace := Prod.map c.symm id
  have hcs : ContMDiffAt (𝓡 2) (𝓡 2) ∞ c.symm p.1 :=
    contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas q) hp.1
  have hh : ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates)
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ h p := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hcs.prodMap (contMDiffAt_id (I := 𝓘(ℝ, ℝ)) (x := p.2))
  have hf' : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f (h p) :=
    hf.contMDiffAt ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hp.2⟩)
  have hs := contDiffAt_pullback_inner g (hf'.comp p hh)
    (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b)
  have heq : (fun y => g.inner ((f ∘ h) y)
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (f ∘ h) y
        (roundCylinderCoordinateBasis a))
      (mfderiv 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) (f ∘ h) y
        (roundCylinderCoordinateBasis b))) =ᶠ[𝓝 p]
      (fun y => roundCylinderTensorCoefficient (roundCylinderPullback g f) c y a b) := by
    filter_upwards [(c.open_target.prod isOpen_Ioo).mem_nhds hp] with y hy
    have hcy : ContMDiffAt (𝓡 2) (𝓡 2) ∞ c.symm y.1 :=
      contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas q) hy.1
    have hhy : ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates)
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ h y := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      exact hcy.prodMap (contMDiffAt_id (I := 𝓘(ℝ, ℝ)) (x := y.2))
    have hfy := hf.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds (show h y ∈
        univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ from ⟨mem_univ _, hy.2⟩))
    rw [mfderiv_comp y (hfy.mdifferentiableAt (by simp))
      (hhy.mdifferentiableAt (by simp))]
    have hderiv : mfderiv 𝓘(ℝ, RoundCylinderCoordinates)
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) h y =
        (mfderiv (𝓡 2) (𝓡 2) c.symm y.1).prodMap
          (ContinuousLinearMap.id ℝ ℝ) := by
      rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
      dsimp only [h]
      rw [mfderiv_prodMap (hcy.mdifferentiableAt (by simp)) mdifferentiableAt_id,
        mfderiv_id]
      rfl
    rw [hderiv]
    rfl
  exact (hs.congr_of_eventuallyEq heq.symm).contDiffWithinAt

end PoincareConjecture.Proofs.M28.NeckAnalysis
