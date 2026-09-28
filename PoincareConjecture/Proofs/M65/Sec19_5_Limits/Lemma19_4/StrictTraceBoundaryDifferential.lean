import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceBoundaryMap
import PoincareConjecture.Proofs.M65.Sec19_5_Limits.Lemma19_4.StrictTraceDifferential











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Complex Metric
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.M65StrictTrace

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]




theorem complex_parameter_within_chart
    (p : M) {f : LoopPlane → M} {psi : ℂ → ℂ} {K : Set ℂ} {z d : ℂ}
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hK : UniqueDiffWithinAt ℝ K z) (hz : z ∈ K)
    (hpsi : HasDerivAt psi d z)
    (hmap : MapsTo (orthonormalBasisOneI.repr ∘ psi) K loopDiskSet)
    (hsource : f (orthonormalBasisOneI.repr (psi z)) ∈ (chartAt LoopAmbient p).source)
    (v : ℂ) :
    fderivWithin ℝ ((chartAt LoopAmbient p) ∘ f ∘ orthonormalBasisOneI.repr ∘ psi)
        K z v =
      mfderiv (𝓡 3) (𝓡 3) (chartAt LoopAmbient p)
        (f (orthonormalBasisOneI.repr (psi z)))
        (mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet (orthonormalBasisOneI.repr (psi z))
          (orthonormalBasisOneI.repr (v * d))) := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let P := e ∘ psi
  let q := chartAt LoopAmbient p
  have hP := e.hasFDerivAt.comp z (hpsi.hasFDerivAt.restrictScalars ℝ)
  have hPmd : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 2) P z :=
    hP.differentiableAt.mdifferentiableAt
  have hmap' : MapsTo P K loopDiskSet := hmap
  have hfd : MDifferentiableWithinAt (𝓡 2) (𝓡 3) f loopDiskSet (P z) :=
    (hf _ (hmap' hz)).mdifferentiableWithinAt one_ne_zero
  have hq : MDifferentiableAt (𝓡 3) (𝓡 3) q (f (P z)) :=
    (mdifferentiable_chart (I := 𝓡 3) p).mdifferentiableAt hsource
  have hfp : MDifferentiableWithinAt (𝓘(ℝ, ℂ)) (𝓡 3) (f ∘ P) K z :=
    hfd.comp z hPmd.mdifferentiableWithinAt hmap'
  have hchainp := mfderivWithin_comp z hfd hPmd.mdifferentiableWithinAt hmap'
    hK.uniqueMDiffWithinAt
  have hchainq := mfderiv_comp_mfderivWithin z hq hfp hK.uniqueMDiffWithinAt
  rw [hchainp] at hchainq
  simp only [mfderivWithin_eq_fderivWithin] at hchainq
  have hPd : fderivWithin ℝ P K z v = e (v * d) := by
    rw [hP.hasFDerivWithinAt.fderivWithin hK]
    rfl
  have hh := congrArg (fun T : ℂ →L[ℝ] LoopAmbient => T v) hchainq
  change fderivWithin ℝ (q ∘ f ∘ P) K z v =
    mfderiv (𝓡 3) (𝓡 3) q (f (P z))
      (mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet (P z) (fderivWithin ℝ P K z v)) at hh
  rw [hPd] at hh
  exact hh




theorem complex_parameter_within_zero_iff
    (p : M) {f : LoopPlane → M} {psi : ℂ → ℂ} {K : Set ℂ} {z d : ℂ}
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hK : UniqueDiffWithinAt ℝ K z) (hz : z ∈ K)
    (hpsi : HasDerivAt psi d z) (hd : d ≠ 0)
    (hmap : MapsTo (orthonormalBasisOneI.repr ∘ psi) K loopDiskSet)
    (hsource : f (orthonormalBasisOneI.repr (psi z)) ∈ (chartAt LoopAmbient p).source) :
    fderivWithin ℝ ((chartAt LoopAmbient p) ∘ f ∘ orthonormalBasisOneI.repr ∘ psi)
        K z = 0 ↔
      mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet (orthonormalBasisOneI.repr (psi z)) = 0 := by
  let e := orthonormalBasisOneI.repr.toContinuousLinearEquiv
  let q := chartAt LoopAmbient p
  have hinv : (mfderiv (𝓡 3) (𝓡 3) q
      (f (orthonormalBasisOneI.repr (psi z)))).IsInvertible :=
    ⟨(mdifferentiable_chart (I := 𝓡 3) p).mfderiv hsource, rfl⟩
  constructor
  · intro hzero
    ext v
    have hh := complex_parameter_within_chart p hf hK hz hpsi hmap hsource
      (e.symm v / d)
    rw [hzero, zero_apply, div_mul_cancel₀ _ hd] at hh
    have hh' := congrArg (mfderiv (𝓡 3) (𝓡 3) q
      (f (orthonormalBasisOneI.repr (psi z)))).inverse hh
    change (mfderiv (𝓡 3) (𝓡 3) q (f (orthonormalBasisOneI.repr (psi z)))).inverse 0 =
      (mfderiv (𝓡 3) (𝓡 3) q (f (orthonormalBasisOneI.repr (psi z)))).inverse
        ((mfderiv (𝓡 3) (𝓡 3) q (f (orthonormalBasisOneI.repr (psi z))))
          ((mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet
            (orthonormalBasisOneI.repr (psi z))) (e (e.symm v)))) at hh'
    simpa only [map_zero, hinv.inverse_apply_self, e.apply_symm_apply, zero_apply]
      using hh'.symm
  · intro hzero
    ext v
    rw [complex_parameter_within_chart p hf hK hz hpsi hmap hsource, hzero,
      zero_apply, map_zero]
    rfl




theorem complex_parameter_within_conformal_norm
    (g : RiemannianMetric 3 M) (gE : RiemannianMetric 3 LoopAmbient) (p : M)
    {f : LoopPlane → M} {psi : ℂ → ℂ} {K : Set ℂ} {z d : ℂ}
    (hf : ContMDiffOn (𝓡 2) (𝓡 3) 1 f loopDiskSet)
    (hconf : ∀ w ∈ ball (0 : LoopPlane) 1,
      ∃ c : ℝ, m60AreaGram g f w = c • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hK : UniqueDiffWithinAt ℝ K z) (hz : z ∈ K)
    (hpsi : HasDerivAt psi d z)
    (hmap : MapsTo (orthonormalBasisOneI.repr ∘ psi) K loopDiskSet)
    (hsource : f (orthonormalBasisOneI.repr (psi z)) ∈ (chartAt LoopAmbient p).source)
    (hmetric :
      let q := chartAt LoopAmbient p
      let x := orthonormalBasisOneI.repr (psi z)
      ∀ a b : LoopAmbient, gE.inner (q (f x)) a b = g.inner (q.symm (q (f x)))
        (mfderiv (𝓡 3) (𝓡 3) q.symm (q (f x)) a)
        (mfderiv (𝓡 3) (𝓡 3) q.symm (q (f x)) b)) (v : ℂ) :
    let q := chartAt LoopAmbient p
    let x := orthonormalBasisOneI.repr (psi z)
    let T := fderivWithin ℝ (q ∘ f ∘ orthonormalBasisOneI.repr ∘ psi) K z
    gE.inner (q (f x)) (T v) (T v) =
      diskConformalFactor g f x * ‖d‖ ^ 2 * ‖v‖ ^ 2 := by
  let q := chartAt LoopAmbient p
  let x := orthonormalBasisOneI.repr (psi z)
  let T := fderivWithin ℝ (q ∘ f ∘ orthonormalBasisOneI.repr ∘ psi) K z
  have hc (w : TangentSpace (𝓡 3) (f x)) :
      mfderiv (𝓡 3) (𝓡 3) q.symm (q (f x))
        (mfderiv (𝓡 3) (𝓡 3) q (f x) w) = w := by
    exact congrArg (fun A : TangentSpace (𝓡 3) (f x) →L[ℝ]
      TangentSpace (𝓡 3) (f x) => A w)
      ((mdifferentiable_chart (I := 𝓡 3) p).symm_comp_deriv hsource)
  have hchain : T v = mfderiv (𝓡 3) (𝓡 3) q (f x)
      (mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet x
        (orthonormalBasisOneI.repr (v * d))) :=
    complex_parameter_within_chart p hf hK hz hpsi hmap hsource v
  have hm := hmetric (T v) (T v)
  change gE.inner (q (f x)) (T v) (T v) =
    g.inner (q.symm (q (f x)))
      (mfderiv (𝓡 3) (𝓡 3) q.symm (q (f x)) (T v))
      (mfderiv (𝓡 3) (𝓡 3) q.symm (q (f x)) (T v)) at hm
  rw [hchain, hc, q.left_inv hsource] at hm
  change gE.inner (q (f x)) (T v) (T v) = _
  calc
    _ = g.inner (f x)
        (mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet x (orthonormalBasisOneI.repr (v * d)))
        (mfderivWithin (𝓡 2) (𝓡 3) f loopDiskSet x
          (orthonormalBasisOneI.repr (v * d))) := by rw [hchain]; exact hm
    _ = diskConformalFactor g f x * ‖orthonormalBasisOneI.repr (v * d)‖ ^ 2 :=
      diskDifferential_inner_self g f hf hconf (show x ∈ loopDiskSet from hmap hz) _
    _ = _ := by
      rw [orthonormalBasisOneI.repr.norm_map, norm_mul, mul_pow]
      ring

end PoincareConjecture.M65StrictTrace
