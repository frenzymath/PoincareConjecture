import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FiniteCurrentTraces

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem m64FiniteAnnulusCurrent_along_slice_hasDerivAt
    (g : RiemannianMetric n M) {v : ℝ → LoopPlane → M}
    {ell : ℝ → LoopPlane} {x : ℝ} (i : Fin 2)
    (hJ : DifferentiableAt ℝ (m64FiniteAnnulusCurrent g v i) (ell x))
    (hell : ∀ y, HasDerivAt ell (EuclideanSpace.basisFun (Fin 2) ℝ i) y)
    (hinside : ∀ᶠ y in 𝓝 x, ell y ∈ interior m64AnnulusDomain)
    (hbase : ∀ᶠ y in 𝓝 x, MDifferentiableAt (𝓡 2) (𝓡 n) (v 0) (ell y)) :
    HasDerivAt
      (fun y => g.inner (v 0 (ell y)) (curveVelocity (fun s => v s (ell y)) 0)
        (curveVelocity (fun z => v 0 (ell z)) y))
      (fderiv ℝ (m64FiniteAnnulusCurrent g v i) (ell x)
        (EuclideanSpace.basisFun (Fin 2) ℝ i)) x := by
  have hd := hJ.hasFDerivAt.comp_hasDerivAt x (hell x)
  apply hd.congr_of_eventuallyEq
  filter_upwards [hinside, hbase] with y hy hby
  have hline : mfderiv 𝓘(ℝ, ℝ) (𝓡 2) ell y 1 =
      EuclideanSpace.basisFun (Fin 2) ℝ i := by
    rw [mfderiv_eq_fderiv, (hell y).hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ _
  have hchain := mfderiv_comp_apply y hby (hell y).differentiableAt.mdifferentiableAt (1 : ℝ)
  rw [hline] at hchain
  have hvel : curveVelocity (n := n) (fun z => v 0 (ell z)) y =
      mfderiv (𝓡 2) (𝓡 n) (v 0) (ell y) (EuclideanSpace.basisFun (Fin 2) ℝ i) := hchain
  rw [hvel]
  exact (m64FiniteAnnulusCurrent_eq_pairing g v i hy).symm

end PoincareConjecture
