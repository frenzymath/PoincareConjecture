import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.PlaneMapRegularity
import Mathlib.Geometry.Manifold.MFDeriv.Tangent

set_option autoImplicit false

open Set Bundle Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable def m65ChartJacobian (g : RiemannianMetric n M) (p : M)
    (d : EuclideanSpace ℝ (Fin n) × (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n))) : ℝ :=
  let inv := (chartAt (EuclideanSpace ℝ (Fin n)) p).symm
  let v : Fin 2 → TangentSpace (𝓡 n) (inv d.1) := fun i =>
    mfderiv (𝓡 n) (𝓡 n) inv d.1 (d.2 (EuclideanSpace.basisFun (Fin 2) ℝ i))
  Real.sqrt (max 0 (Matrix.det fun i j => g.inner (inv d.1) (v i) (v j)))

theorem m65ChartJacobian_continuousOn (g : RiemannianMetric n M) (p : M) :
    ContinuousOn (m65ChartJacobian g p)
      (Prod.fst ⁻¹' (chartAt (EuclideanSpace ℝ (Fin n)) p).target) := by
  let chi := chartAt (EuclideanSpace ℝ (Fin n)) p
  let : RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hinv : ContMDiffOn (𝓡 n) (𝓡 n) 1 chi.symm chi.target := contMDiffOn_chart_symm
  have htan : ContinuousOn (tangentMap (𝓡 n) (𝓡 n) chi.symm)
      (Bundle.TotalSpace.proj ⁻¹' chi.target) := by
    apply (hinv.continuousOn_tangentMapWithin le_rfl chi.open_target.uniqueMDiffOn).congr
    intro v hv
    exact (tangentMapWithin_eq_tangentMap (chi.open_target.uniqueMDiffOn v.1 hv)
      (mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) hv)).symm
  have hcol (i : Fin 2) : ContinuousOn
      (fun d : EuclideanSpace ℝ (Fin n) × (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n)) =>
        (⟨chi.symm d.1, mfderiv (𝓡 n) (𝓡 n) chi.symm d.1
          (d.2 (EuclideanSpace.basisFun (Fin 2) ℝ i))⟩ : TangentBundle (𝓡 n) M))
      (Prod.fst ⁻¹' chi.target) := by
    exact htan.comp
      (((tangentBundleModelSpaceHomeomorph (𝓡 n)).symm.continuous.comp
        (continuous_fst.prodMk (by fun_prop))).continuousOn) (fun _ hd => hd)
  have hgram : ContinuousOn
      (fun d : EuclideanSpace ℝ (Fin n) × (LoopPlane →L[ℝ] EuclideanSpace ℝ (Fin n)) =>
        fun i j : Fin 2 => g.inner (chi.symm d.1)
          (mfderiv (𝓡 n) (𝓡 n) chi.symm d.1 (d.2 (EuclideanSpace.basisFun (Fin 2) ℝ i)))
          (mfderiv (𝓡 n) (𝓡 n) chi.symm d.1 (d.2 (EuclideanSpace.basisFun (Fin 2) ℝ j))))
      (Prod.fst ⁻¹' chi.target) :=
    continuousOn_pi.mpr fun i => continuousOn_pi.mpr fun j => (hcol i).inner_bundle (hcol j)
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hgram' := continuousOn_iff_continuous_domRestrict.mp hgram
  exact (continuous_const.max hgram'.matrix_det).sqrt

theorem m65AreaDensity_eq_chartJacobian (g : RiemannianMetric n M) (p : M)
    {f : LoopPlane → M} {z : LoopPlane} (hf : MDifferentiableAt (𝓡 2) (𝓡 n) f z)
    (hz : f z ∈ (chartAt (EuclideanSpace ℝ (Fin n)) p).source) :
    m60AreaDensity g f z = m65ChartJacobian g p
      ((chartAt (EuclideanSpace ℝ (Fin n)) p) (f z),
        fderiv ℝ ((chartAt (EuclideanSpace ℝ (Fin n)) p) ∘ f) z) := by
  let chi := chartAt (EuclideanSpace ℝ (Fin n)) p
  have hc : MDifferentiableAt (𝓡 2) (𝓡 n) (chi ∘ f) z :=
    (mdifferentiableAt_atlas (chart_mem_atlas _ _) hz).comp z hf
  have hi : MDifferentiableAt (𝓡 n) (𝓡 n) chi.symm (chi (f z)) :=
    mdifferentiableAt_atlas_symm (chart_mem_atlas _ _) (chi.map_source hz)
  have heq : chi.symm ∘ (chi ∘ f) =ᶠ[𝓝 z] f := by
    filter_upwards [hf.continuousAt.preimage_mem_nhds (chi.open_source.mem_nhds hz)] with x hx
    exact chi.left_inv hx
  have hd : mfderiv (𝓡 2) (𝓡 n) f z =
      (mfderiv (𝓡 n) (𝓡 n) chi.symm (chi (f z))).comp (fderiv ℝ (chi ∘ f) z) := by
    rw [← heq.mfderiv_eq, mfderiv_comp z hi hc, mfderiv_eq_fderiv]
    rfl
  unfold m60AreaDensity m60AreaGram m65ChartJacobian
  dsimp only
  rw [chi.left_inv hz]
  congr 3
  ext i j
  rw [hd]
  rfl

end PoincareConjecture
