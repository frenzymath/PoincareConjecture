import PoincareConjecture.Proofs.M63.Mathlib.InnerProductNormalConstraint
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessAmbientAcceleration
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessGraphComparison
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.AmbientCurveCoefficients
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.UniquenessEmbeddedCurve

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology RealInnerProductSpace

universe u v

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {ι : Type v} [Fintype ι] {a b : ℝ}

local notation "W" => EuclideanSpace ℝ ι

theorem normalGraph_curvature_projection
    (F : RicciFlow n M (Icc a b)) {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {N : Set W} (hN : IsOpen N) (heN : range e ⊆ N) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho N) (hret : ∀ p, rho (e p) = p)
    (q : ℝ → ℝ → M) {t : ℝ}
    (hspace : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => q y t))
    (himm : ∀ y, curveVelocity (n := n) (fun z => q z t) y ≠ 0)
    {r : ℝ → W} (hr : ContDiff ℝ ∞ r)
    (hnormal : ∀ y, ⟪e (q y t) - r y, deriv r y⟫ = 0)
    (x : ℝ) (htrans : ⟪deriv (fun y => e (q y t)) x, deriv r x⟫ ≠ 0) :
    let U : ℝ → W := fun y => e (q y t) - r y
    let V := deriv (fun y => e (q y t)) x
    let eta : W := mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t) (m62CurvatureVector F q t x)
    let A := ambientCurvePrincipal F rho t (e (q x t)) V
    let B0 := ambientCurveLower F e rho t (e (q x t)) V
    eta - (⟪eta, deriv r x⟫ / ⟪V, deriv r x⟫) • V =
      A • deriv (deriv U) x + curveGraphLower A B0
        (deriv r x) (deriv (deriv r) x) (deriv (deriv (deriv r)) x)
        (U x) (deriv U x) := by
  dsimp only
  let f : ℝ → W := fun y => e (q y t)
  let U : ℝ → W := fun y => f y - r y
  let X := curveVelocity (n := n) (fun y => q y t) x
  let V := deriv f x
  let eta : W := mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t) (m62CurvatureVector F q t x)
  let A := ambientCurvePrincipal F rho t (e (q x t)) V
  let B0 := ambientCurveLower F e rho t (e (q x t)) V
  have hf : ContDiff ℝ 2 f :=
    ((he.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp hspace).contDiff
  have hr2 : ContDiff ℝ 2 r := hr.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hU : ContDiff ℝ 2 U := hf.sub hr2
  have hfirst : deriv U = fun y => deriv f y - deriv r y :=
    funext fun y => deriv_sub (hf.differentiable (by norm_num) y)
      (hr2.differentiable (by norm_num) y)
  have hV : V = deriv r x + deriv U x := by
    rw [hfirst]
    dsimp only [V]
    abel
  have hsecond : deriv (deriv f) x = deriv (deriv r) x + deriv (deriv U) x := by
    rw [hfirst, deriv_fun_sub (hf.differentiable_deriv_two x) (hr2.differentiable_deriv_two x)]
    abel
  have hpush : V = mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t) X := by
    have hchain : fderiv ℝ f x =
        (mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t)).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun y => q y t) x) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp x (he.mdifferentiable (by simp)).mdifferentiableAt
        ((hspace x).mdifferentiableAt (by norm_num))
    exact congrArg (fun L : ℝ →L[ℝ] W => L 1) hchain
  have hleft := (smooth_retraction_differentials he hN heN hrho hret).2.2
  have hA : A = (curveSpeed F q t x ^ 2)⁻¹ := by
    dsimp only [A, ambientCurvePrincipal]
    rw [hpush]
    erw [hleft (q x t) X, hret (q x t)]
    rw [M62.speed_sq]
  have hB0 : B0 = -(A • coordinateHessian (F.connection t) e (q x t) X X) := by
    dsimp only [B0, ambientCurveLower]
    have hH : coordinateHessian (F.connection t) e (rho (e (q x t)))
        (mfderiv 𝓘(ℝ, W) (𝓡 n) rho (e (q x t)) V)
        (mfderiv 𝓘(ℝ, W) (𝓡 n) rho (e (q x t)) V) =
          coordinateHessian (F.connection t) e (q x t) X X := by
      rw [hpush]
      erw [hleft (q x t) X, hret (q x t)]
    rw [hH]
  have hcurv : eta = A • (deriv (deriv r) x + deriv (deriv U) x) + B0 -
      (deriv (curveSpeed F q t) x / curveSpeed F q t x ^ 3) •
        (deriv r x + deriv U x) := by
    have h := embedded_curvature_eq_acceleration_sub_tangent F he q hspace himm x
    change eta = (curveSpeed F q t x ^ 2)⁻¹ •
      (deriv (deriv f) x - coordinateHessian (F.connection t) e (q x t) X X) -
        (deriv (curveSpeed F q t) x / curveSpeed F q t x ^ 3) • V at h
    rw [← hA, hsecond, hV, smul_sub] at h
    rw [hB0]
    simpa only [sub_eq_add_neg, add_assoc] using h
  have hden : ⟪deriv r x + deriv U x, deriv r x⟫ ≠ 0 := by
    rw [← hV]
    exact htrans
  have hproj := graph_acceleration_projection hden
    (secondDeriv_normal_constraint hU hr hnormal x) hcurv
  rw [← hV] at hproj
  exact hproj

theorem normalGraph_hasDerivAt_time
    {F : RicciFlow n M (Icc a b)} {e : M → W}
    (he : ContMDiff (𝓡 n) 𝓘(ℝ, W) ∞ e)
    {N : Set W} (hN : IsOpen N) (heN : range e ⊆ N) {rho : W → M}
    (hrho : ContMDiffOn 𝓘(ℝ, W) (𝓡 n) ∞ rho N) (hret : ∀ p, rho (e p) = p)
    {c : ℝ → ℝ → M} {J : Set ℝ} (hc : M63C2ShrinkingCurveOn F c J)
    {r : ℝ → W} (hr : ContDiff ℝ ∞ r) (psi : ℝ → ℝ → ℝ)
    {t x : ℝ} (ht : t ∈ interior J)
    (hlabels : ContDiff ℝ 2 (fun y => psi y t))
    (hpos : ∀ y, 0 < deriv (fun z => psi z t) y)
    (htime : DifferentiableAt ℝ (psi x) t)
    (hnormal : ∀ s ∈ J, ∀ y, ⟪e (c (psi y s) s) - r y, deriv r y⟫ = 0)
    (htrans : ⟪deriv (fun y => e (c (psi y t) t)) x, deriv r x⟫ ≠ 0) :
    let q : ℝ → ℝ → M := fun y s => c (psi y s) s
    let U : ℝ → ℝ → W := fun y s => e (q y s) - r y
    let V := deriv (fun y => e (q y t)) x
    let A := ambientCurvePrincipal F rho t (e (q x t)) V
    let B0 := ambientCurveLower F e rho t (e (q x t)) V
    HasDerivAt (U x)
      (A • deriv (deriv (fun y => U y t)) x + curveGraphLower A B0
        (deriv r x) (deriv (deriv r) x) (deriv (deriv (deriv r)) x)
        (U x t) (deriv (fun y => U y t) x)) t := by
  dsimp only
  let q : ℝ → ℝ → M := fun y s => c (psi y s) s
  let U : ℝ → ℝ → W := fun y s => e (q y s) - r y
  let V := deriv (fun y => e (q y t)) x
  let eta : W := mfderiv (𝓡 n) 𝓘(ℝ, W) e (q x t) (m62CurvatureVector F q t x)
  let A := ambientCurvePrincipal F rho t (e (q x t)) V
  let B0 := ambientCurveLower F e rho t (e (q x t)) V
  let delta := deriv (fun y => psi y t) x
  let w := deriv (psi x) t
  let beta := w / delta
  let Y := deriv (fun y => e (c y t)) (psi x t)
  have htJ : t ∈ J := interior_subset ht
  have hspatial := hc.spatial_regular t htJ
  have hlabelDiff : Differentiable ℝ (fun y => psi y t) :=
    hlabels.differentiable (by norm_num)
  have hqspace : ContMDiff 𝓘(ℝ, ℝ) (𝓡 n) 2 (fun y => q y t) :=
    hspatial.comp hlabels.contMDiff
  have hqimm (y : ℝ) : curveVelocity (n := n) (fun z => q z t) y ≠ 0 := by
    have hvel := curveVelocity_comp (phi := fun z => psi z t) (x := y)
      ((hspatial (psi y t)).mdifferentiableAt (by norm_num))
      (hlabelDiff y).hasDerivAt
    change curveVelocity (n := n) (fun z => q z t) y = _ at hvel
    rw [hvel]
    exact smul_ne_zero (hpos y).ne' (hc.immersed t htJ (psi y t))
  have hprojection := normalGraph_curvature_projection F he hN heN hrho hret q
    hqspace hqimm hr (hnormal t htJ) x htrans
  change eta - (⟪eta, deriv r x⟫ / ⟪V, deriv r x⟫) • V =
    A • deriv (deriv (fun y => U y t)) x + curveGraphLower A B0
      (deriv r x) (deriv (deriv r) x) (deriv (deriv (deriv r)) x)
      (U x t) (deriv (fun y => U y t) x) at hprojection
  have hS := unitTangent_contMDiff_of_c2 F c hspatial (hc.immersed t htJ)
  have hcurvature : m62CurvatureVector F q t x = m62CurvatureVector F c t (psi x t) :=
    curvatureVector_comp F c (hspatial.mdifferentiable (by norm_num))
      hlabelDiff hpos ((hS (psi x t)).mdifferentiableAt (by simp))
  have heta : eta = (mfderiv (𝓡 n) 𝓘(ℝ, W) e (c (psi x t) t)
      (m62CurvatureVector F c t (psi x t)) : W) := by
    dsimp only [eta, q]
    rw [hcurvature]
  obtain ⟨hC1, hCtime⟩ := c2ShrinkingCurve_embedded_interior_equation hc he
  have hCspace : ContDiff ℝ 2 (fun y => e (c y t)) :=
    (c2ShrinkingCurve_embedded_closed_data hc he).1 t htJ
  have hy : HasDerivAt (fun y => e (c y t)) Y (psi x t) :=
    (hCspace.differentiable (by norm_num) (psi x t)).hasDerivAt
  have hV : V = delta • Y := by
    have hd := hy.scomp (h := fun y => psi y t) x (hlabelDiff x).hasDerivAt
    exact hd.deriv
  let C : ℝ × ℝ → W := fun z => e (c z.1 z.2)
  let D := fderiv ℝ C (psi x t, t)
  have hD : HasFDerivAt C D (psi x t, t) :=
    ((hC1.contDiffAt ((isOpen_univ.prod isOpen_interior).mem_nhds
      ⟨mem_univ _, ht⟩)).differentiableAt (by norm_num)).hasFDerivAt
  have hDx : D (1, 0) = Y :=
    (hD.comp_hasDerivAt (f := fun y : ℝ => (y, t)) (psi x t)
      ((hasDerivAt_id (psi x t)).prodMk (hasDerivAt_const (psi x t) t))).unique hy
  have hDt : D (0, 1) = eta := by
    have hd := (hD.comp_hasDerivAt (f := fun s : ℝ => (psi x t, s)) t
      ((hasDerivAt_const t (psi x t)).prodMk (hasDerivAt_id t))).unique
        (hCtime t ht (psi x t))
    exact hd.trans heta.symm
  have hsum : D (w, 1) = w • Y + eta := by
    have hp : (w, (1 : ℝ)) = w • ((1 : ℝ), (0 : ℝ)) + (0, 1) := by
      ext <;> simp
    rw [hp, map_add, map_smul, hDx, hDt]
  have hbetaV : beta • V = w • Y := by
    rw [hV, smul_smul]
    dsimp only [beta]
    rw [div_mul_cancel₀ w (hpos x).ne']
  have hUtime : HasDerivAt (U x) (eta + beta • V) t := by
    have hd : HasDerivAt (fun s => e (q x s)) (D (w, 1)) t :=
      hD.comp_hasDerivAt (f := fun s => (psi x s, s)) t
        (htime.hasDerivAt.prodMk (hasDerivAt_id t))
    apply (hd.sub_const (r x)).congr_deriv
    rw [hsum, hbetaV, add_comm]
  have hzero : HasDerivAt (fun s => ⟪U x s, deriv r x⟫) 0 t := by
    apply (hasDerivAt_const t (0 : ℝ)).congr_of_eventuallyEq
    filter_upwards [isOpen_interior.mem_nhds ht] with s hs
    exact hnormal s (interior_subset hs) x
  have hinner : ⟪eta, deriv r x⟫ + beta * ⟪V, deriv r x⟫ = 0 := by
    have h := (hUtime.inner ℝ (hasDerivAt_const t (deriv r x))).unique hzero
    simpa only [inner_zero_right, zero_add, inner_add_left, real_inner_smul_left] using h
  have hbeta : beta = -(⟪eta, deriv r x⟫ / ⟪V, deriv r x⟫) := by
    apply (eq_neg_iff_add_eq_zero).mpr
    apply (mul_right_cancel₀ htrans)
    rw [add_mul, div_mul_cancel₀ _ htrans, zero_mul]
    linarith only [hinner]
  apply hUtime.congr_deriv
  rw [hbeta, neg_smul, ← sub_eq_add_neg]
  exact hprojection

end PoincareConjecture.M63
