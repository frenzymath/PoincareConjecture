import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.GeodesicEquation
import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.RelabelingGeometry
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.MinimizingGeodesic
import PoincareConjecture.Definitions.M63Polygon

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem RiemannianMetric.tangentNorm_smul (g : RiemannianMetric n M)
    (p : M) (r : ℝ) (v : TangentSpace (𝓡 n) p) :
    g.tangentNorm p (r • v) = |r| * g.tangentNorm p v := by
  simp only [RiemannianMetric.tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

theorem M63.minimizingGeodesicSide_nonempty [T2Space M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) {ell : ℝ} (hell : 0 < ell)
    (p q : M) {R : ℝ} (hR : 0 < R) (hcompact : IsCompact (closure (g.ball p R)))
    (hq : q ∈ g.ball p R) : Nonempty (M63MinimizingGeodesicSide g D ell p q) := by
  obtain ⟨epsilon, hepsilon, gamma, hgamma, hstart, hfinish, hmin⟩ :=
    g.exists_minimizing_geodesic_of_precompact_ball p q hR hcompact hq
  obtain ⟨C, hC⟩ := hgamma.exists_constant_tangentNorm (by linarith)
  let alpha : ℝ → M := fun s => gamma (ell⁻¹ * s)
  let U : Set ℝ := (fun s : ℝ => ell⁻¹ * s) ⁻¹' Ioo (-epsilon) (1 + epsilon)
  have hU : IsOpen U := isOpen_Ioo.preimage (continuous_const.mul continuous_id)
  have hunit : Icc (0 : ℝ) 1 ⊆ Ioo (-epsilon) (1 + epsilon) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hscale (s : ℝ) (hs : s ∈ Icc 0 ell) : ell⁻¹ * s ∈ Icc (0 : ℝ) 1 := by
    refine ⟨mul_nonneg (inv_nonneg.mpr hell.le) hs.1, ?_⟩
    calc
      ell⁻¹ * s ≤ ell⁻¹ * ell := mul_le_mul_of_nonneg_left hs.2 (inv_nonneg.mpr hell.le)
      _ = 1 := inv_mul_cancel₀ hell.ne'
  have hsub : Icc 0 ell ⊆ U := fun s hs => hunit (hscale s hs)
  have halpha : g.IsGeodesicOn alpha U := hgamma.comp_mul ell⁻¹
  have hspeed (s : ℝ) (hs : s ∈ Icc 0 ell) :
      g.tangentNorm (alpha s) (curveVelocity alpha s) = (C : ℝ) / ell := by
    have hdiff := (hgamma.contMDiffAt_infty (hsub hs)).mdifferentiableAt (by simp)
    have hparam : HasDerivAt (fun r : ℝ => ell⁻¹ * r) ell⁻¹ s := by
      simpa using (hasDerivAt_id s).const_mul ell⁻¹
    have hCs : g.tangentNorm (gamma (ell⁻¹ * s))
        (curveVelocity gamma (ell⁻¹ * s)) = (C : ℝ) := hC _ (hsub hs)
    change g.tangentNorm (gamma (ell⁻¹ * s))
      (curveVelocity (fun r => gamma (ell⁻¹ * r)) s) = _
    rw [M63.curveVelocity_comp hdiff hparam, g.tangentNorm_smul,
      abs_of_nonneg (inv_nonneg.mpr hell.le), hCs]
    exact (div_eq_inv_mul _ _).symm
  have hlength : g.pathELength alpha 0 ell = ENNReal.ofReal (C : ℝ) := by
    rw [g.pathELength_eq_of_tangentNorm_eq hspeed, sub_zero]
    calc
      _ = ENNReal.ofReal (((C : ℝ) / ell) * ell) :=
        (ENNReal.ofReal_mul (div_nonneg C.2 hell.le)).symm
      _ = _ := congrArg ENNReal.ofReal (div_mul_cancel₀ (C : ℝ) hell.ne')
  have horiginal : g.pathELength gamma 0 1 = ENNReal.ofReal (C : ℝ) := by
    simpa using g.pathELength_eq_of_tangentNorm_eq (fun s hs => hC s (hunit hs))
  refine ⟨{
    map := alpha
    domain := U
    domain_open := hU
    interval_subset := hsub
    smooth := halpha.contMDiffOn_infty
    start := by simpa [alpha] using hstart
    finish := by simpa [alpha, inv_mul_cancel₀ hell.ne'] using hfinish
    speed := (C : ℝ) / ell
    speed_nonnegative := div_nonneg C.2 hell.le
    constant_speed := hspeed
    equation := fun _ hs => halpha.pullback_velocity_eq_zero D hs
    minimizing := hlength.trans (horiginal.symm.trans
      (hgamma.pathELength_eq_of_edist_segment hepsilon hstart hmin)) }⟩

end PoincareConjecture
