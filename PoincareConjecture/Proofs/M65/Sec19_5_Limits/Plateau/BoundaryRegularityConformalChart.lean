import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Plateau.BoundaryRegularityHarmonicChart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex
open scoped Topology ContDiff Manifold

namespace PoincareConjecture.M65Boundary

open M65StrictTrace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]

private theorem interior_conformal_norm (g : RiemannianMetric 3 M)
    (f : LoopPlane → M) {x : LoopPlane} {a : ℝ}
    (hgram : m60AreaGram g f x = a • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (v : LoopPlane) :
    g.inner (f x) (mfderiv (𝓡 2) (𝓡 3) f x v)
      (mfderiv (𝓡 2) (𝓡 3) f x v) = a * ‖v‖ ^ 2 := by
  have hcol (i j : Fin 2) :
      g.inner (f x) (mfderiv (𝓡 2) (𝓡 3) f x (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 3) f x (EuclideanSpace.basisFun (Fin 2) ℝ j)) =
          if i = j then a else 0 := by
    simpa only [m60AreaGram, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      mul_ite, mul_one, mul_zero] using congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => A i j) hgram
  have hv : v = v 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
      v 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
    ext i
    fin_cases i <;> simp [EuclideanSpace.single]
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul, hcol,
    Fin.isValue, ite_true, zero_ne_one, one_ne_zero, ite_false, mul_zero,
    add_zero, zero_add, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  ring

theorem complex_parameter_chart_conformal_norm
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 LoopAmbient) (p : M)
    {f : LoopPlane → M} {psi : ℂ → ℂ} {z d : ℂ} {a : ℝ}
    (hf : MDifferentiableAt (𝓡 2) (𝓡 3) f (orthonormalBasisOneI.repr (psi z)))
    (hpsi : HasDerivAt psi d z)
    (hsource : f (orthonormalBasisOneI.repr (psi z)) ∈ (chartAt LoopAmbient p).source)
    (hgram : m60AreaGram g f (orthonormalBasisOneI.repr (psi z)) =
      a • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hmetric :
      let c := chartAt LoopAmbient p
      let x := orthonormalBasisOneI.repr (psi z)
      ∀ u v : LoopAmbient, gE.inner (c (f x)) u v = g.inner (c.symm (c (f x)))
        (mfderiv (𝓡 3) (𝓡 3) c.symm (c (f x)) u)
        (mfderiv (𝓡 3) (𝓡 3) c.symm (c (f x)) v)) (v : ℂ) :
    let H := (chartAt LoopAmbient p) ∘ f ∘ orthonormalBasisOneI.repr ∘ psi
    gE.inner (H z) (fderiv ℝ H z v) (fderiv ℝ H z v) = a * ‖d‖ ^ 2 * ‖v‖ ^ 2 := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let P := e ∘ psi
  let c := chartAt LoopAmbient p
  let x := e (psi z)
  let H := c ∘ f ∘ P
  have hP := e.hasFDerivAt.comp z (hpsi.hasFDerivAt.restrictScalars ℝ)
  have hPmd : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 2) P z :=
    hP.differentiableAt.mdifferentiableAt
  have hcd : MDifferentiableAt (𝓡 3) (𝓡 3) c (f x) :=
    (mdifferentiable_chart (I := 𝓡 3) p).mdifferentiableAt hsource
  have hchainp := mfderiv_comp z hf hPmd
  have hchainq := mfderiv_comp z hcd (hf.comp z hPmd)
  rw [hchainp] at hchainq
  simp only [mfderiv_eq_fderiv] at hchainq
  have hPv : fderiv ℝ P z v = e (v * d) := by
    rw [hP.fderiv]
    rfl
  have hchain : fderiv ℝ H z v =
      mfderiv (𝓡 3) (𝓡 3) c (f x) (mfderiv (𝓡 2) (𝓡 3) f x (e (v * d))) := by
    have hh := congrArg (fun T : ℂ →L[ℝ] LoopAmbient => T v) hchainq
    change fderiv ℝ H z v =
      mfderiv (𝓡 3) (𝓡 3) c (f x) (mfderiv (𝓡 2) (𝓡 3) f x (fderiv ℝ P z v)) at hh
    rwa [hPv] at hh
  have hinverse (w : TangentSpace (𝓡 3) (f x)) :
      mfderiv (𝓡 3) (𝓡 3) c.symm (c (f x))
        (mfderiv (𝓡 3) (𝓡 3) c (f x) w) = w :=
    congrArg (fun A : TangentSpace (𝓡 3) (f x) →L[ℝ] TangentSpace (𝓡 3) (f x) => A w)
      ((mdifferentiable_chart (I := 𝓡 3) p).symm_comp_deriv hsource)
  have hm := hmetric (fderiv ℝ H z v) (fderiv ℝ H z v)
  change gE.inner (H z) (fderiv ℝ H z v) (fderiv ℝ H z v) =
    g.inner (c.symm (c (f x)))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c (f x)) (fderiv ℝ H z v))
      (mfderiv (𝓡 3) (𝓡 3) c.symm (c (f x)) (fderiv ℝ H z v)) at hm
  have hleft : c.symm (c (f x)) = f x := c.left_inv (show f x ∈ c.source from hsource)
  rw [hchain, hinverse, hleft] at hm
  change gE.inner (H z) (fderiv ℝ H z v) (fderiv ℝ H z v) = _
  calc
    _ = g.inner (f x) (mfderiv (𝓡 2) (𝓡 3) f x (e (v * d)))
        (mfderiv (𝓡 2) (𝓡 3) f x (e (v * d))) := by rw [hchain]; exact hm
    _ = a * ‖e (v * d)‖ ^ 2 := interior_conformal_norm g f hgram _
    _ = _ := by
      rw [show ‖e (v * d)‖ = ‖v * d‖ from orthonormalBasisOneI.repr.norm_map _, norm_mul, mul_pow]
      ring

theorem continuous_boundary_chart_conformal
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 LoopAmbient)
    {f q : LoopPlane → M} {R : ℝ} {p : ℂ} (hp : ‖p‖ = 1)
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) ∞ f (ball (0 : LoopPlane) 1))
    (hconf : ∀ w ∈ ball (0 : LoopPlane) 1,
      ∃ a : ℝ, m60AreaGram g f w = a • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (heq : EqOn q (f ∘ diskBoundaryCoordinate p)
      (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (hsource : MapsTo q (closedBall (0 : LoopPlane) R) (chartAt LoopAmbient (q 0)).source)
    (hmetric :
      let c := chartAt LoopAmbient (q 0)
      ∀ w ∈ closedBall (0 : LoopPlane) R, ∀ u v : LoopAmbient,
        gE.inner (c (q w)) u v = g.inner (c.symm (c (q w)))
          (mfderiv (𝓡 3) (𝓡 3) c.symm (c (q w)) u)
          (mfderiv (𝓡 3) (𝓡 3) c.symm (c (q w)) v)) :
    let K := (chartAt LoopAmbient (q 0)) ∘ q ∘ orthonormalBasisOneI.repr
    ∀ z ∈ ball (0 : ℂ) R ∩ {z | 0 < z.im}, ∃ a : ℝ,
      ∀ v : ℂ, gE.inner (K z) (fderiv ℝ K z v) (fderiv ℝ K z v) = a * ‖v‖ ^ 2 := by
  dsimp only
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let c := chartAt LoopAmbient (q 0)
  let K := c ∘ q ∘ e
  let J := c ∘ f ∘ e ∘ boundaryCoordinate p
  let U := ball (0 : ℂ) R ∩ {z | 0 < z.im}
  have hU : IsOpen U := isOpen_ball.inter (isOpen_lt continuous_const continuous_im)
  have heU (z : ℂ) (hz : z ∈ U) :
      e z ∈ ball (0 : LoopPlane) R ∩ {w | 0 < w 1} := by
    constructor
    · simpa only [mem_ball_zero_iff, e, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        orthonormalBasisOneI.repr.norm_map] using hz.1
    · change 0 < (orthonormalBasisOneI.repr z) 1
      simpa only [orthonormalBasisOneI_repr_apply, Matrix.cons_val_one,
        Matrix.cons_val_zero, mem_ofPred_eq] using hz.2
  have hpoint (z : ℂ) (hz : z ∈ U) : q (e z) = f (e (boundaryCoordinate p z)) := by
    simpa only [Function.comp_apply, diskBoundaryCoordinate, e,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv, LinearIsometryEquiv.symm_apply_apply]
      using heq (heU z hz)
  intro z hz
  let x := e (boundaryCoordinate p z)
  have hx : x ∈ ball (0 : LoopPlane) 1 := by
    rw [mem_ball_zero_iff]
    change ‖orthonormalBasisOneI.repr (boundaryCoordinate p z)‖ < 1
    rw [orthonormalBasisOneI.repr.norm_map]
    exact (boundaryCoordinate_interior_iff hp z).mpr hz.2
  obtain ⟨a, ha⟩ := hconf x hx
  have hnear : K =ᶠ[𝓝 z] J := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact congrArg c (hpoint w hw)
  have hs : f x ∈ c.source := by
    rw [← hpoint z hz]
    exact hsource (ball_subset_closedBall (heU z hz).1)
  have hm (v w : LoopAmbient) :
      gE.inner (c (f x)) v w = g.inner (c.symm (c (f x)))
        (mfderiv (𝓡 3) (𝓡 3) c.symm (c (f x)) v)
        (mfderiv (𝓡 3) (𝓡 3) c.symm (c (f x)) w) := by
    rw [← hpoint z hz]
    exact hmetric (e z) (ball_subset_closedBall (heU z hz).1) v w
  refine ⟨a * ‖I * boundaryCoordinate p z‖ ^ 2, ?_⟩
  intro v
  change gE.inner (K z) (fderiv ℝ K z v) (fderiv ℝ K z v) = _
  rw [hnear.self_of_nhds, hnear.fderiv_eq]
  exact complex_parameter_chart_conformal_norm g gE (q 0)
    ((hf.contMDiffAt (isOpen_ball.mem_nhds hx)).mdifferentiableAt (by simp))
    (hasDerivAt_boundaryCoordinate p z) hs ha hm v

end PoincareConjecture.M65Boundary
