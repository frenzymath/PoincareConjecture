import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.EpsilonRegularityDecay











noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff

namespace PoincareConjecture

open CoordinateExponential ConnectionVariation

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "b" => EuclideanSpace.basisFun (Fin 2) ℝ




theorem m64LocalHarmonic_scalar_observation_laplacian {g : RiemannianMetric n M}
    (D : LeviCivitaData g) {s : M → ℝ} (hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ s)
    (q : M) {u : LoopPlane → EuclideanSpace ℝ (Fin n)} {f : LoopPlane → M}
    {p : LoopPlane} (hu : ContDiffAt ℝ 2 u p)
    (hut : u p ∈ (extChartAt (𝓡 n) q).target)
    (hmap : ((extChartAt (𝓡 n) q).symm ∘ u) =ᶠ[𝓝 p] f)
    (hharm : (∑ i : Fin 2, covDerivAlong
      (christoffelBilinear (g.pullbackCoefficients (extChartAt (𝓡 n) q).symm)) u
      (fun x => fderiv ℝ u x (b i)) (b i) p) = 0) :
    (∑ i : Fin 2, fderiv ℝ (fderiv ℝ (s ∘ f)) p (b i) (b i)) =
      ∑ i : Fin 2, D.hessian s (f p)
        (mfderiv (𝓡 2) (𝓡 n) f p (b i)) (mfderiv (𝓡 2) (𝓡 n) f p (b i)) := by
  let c := extChartAt (𝓡 n) q
  let r := s ∘ c.symm
  let Gamma := christoffelBilinear (g.pullbackCoefficients c.symm)
  have hcs : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm (u p) :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target q).mem_nhds hut)
  have hr : ContDiffAt ℝ 2 r (u p) :=
    (contMDiffAt_iff_contDiffAt.mp ((hs _).comp _ hcs)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hdu : mfderiv (𝓡 2) (𝓡 n) f p =
      (mfderiv (𝓡 n) (𝓡 n) c.symm (u p)).comp (fderiv ℝ u p) := by
    have hd := mfderiv_comp p (hcs.mdifferentiableAt (by simp))
      (hu.contMDiffAt.mdifferentiableAt (by norm_num))
    rw [mfderiv_eq_fderiv] at hd
    exact hmap.mfderiv_eq.symm.trans hd
  have hvalue : c.symm (u p) = f p := hmap.self_of_nhds
  have hH (i : Fin 2) : D.hessian s (f p)
      (mfderiv (𝓡 2) (𝓡 n) f p (b i)) (mfderiv (𝓡 2) (𝓡 n) f p (b i)) =
      fderiv ℝ (fderiv ℝ r) (u p) (fderiv ℝ u p (b i)) (fderiv ℝ u p (b i)) -
        fderiv ℝ r (u p) (Gamma (u p) (fderiv ℝ u p (b i)) (fderiv ℝ u p (b i))) := by
    have hh := D.hessian_in_chart q hut (hs _)
      (fderiv ℝ u p (b i)) (fderiv ℝ u p (b i))
    change D.hessian s (c.symm (u p))
      (((mfderiv (𝓡 n) (𝓡 n) c.symm (u p)).comp (fderiv ℝ u p)) (b i))
      (((mfderiv (𝓡 n) (𝓡 n) c.symm (u p)).comp (fderiv ℝ u p)) (b i)) = _ at hh
    rw [← hdu, hvalue] at hh
    exact hh
  have heq : r ∘ u =ᶠ[𝓝 p] s ∘ f := by
    filter_upwards [hmap] with x hx
    exact congrArg s hx
  have ht : (fderiv ℝ (fderiv ℝ u) p (b 0) (b 0) +
      Gamma (u p) (fderiv ℝ u p (b 0)) (fderiv ℝ u p (b 0))) +
      (fderiv ℝ (fderiv ℝ u) p (b 1) (b 1) +
      Gamma (u p) (fderiv ℝ u p (b 1)) (fderiv ℝ u p (b 1))) = 0 := by
    change (∑ i : Fin 2, covDerivAlong Gamma u
      (fun x => fderiv ℝ u x (b i)) (b i) p) = 0 at hharm
    simp only [covDerivAlong, M60.fderiv_column hu, Fin.sum_univ_two] at hharm
    exact hharm
  have ht' := congrArg (fderiv ℝ r (u p)) ht
  simp only [map_add, map_zero] at ht'
  rw [← heq.fderiv.fderiv_eq, Fin.sum_univ_two, Fin.sum_univ_two,
    M60.second_fderiv_comp hr hu, M60.second_fderiv_comp hr hu]
  rw [hH 0, hH 1]
  linarith only [ht']

end PoincareConjecture
