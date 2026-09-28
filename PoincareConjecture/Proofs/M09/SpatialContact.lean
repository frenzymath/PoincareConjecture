import PoincareConjecture.Proofs.M09.SquareEndpointFamily
import PoincareConjecture.Proofs.M09.SmoothSquareActionDifferential
import PoincareConjecture.Proofs.M09.PathComparison
import PoincareConjecture.Proofs.M09.FamilySquareVelocity
import PoincareConjecture.Proofs.M09.CenteredChartOperators
import PoincareConjecture.Proofs.M09.ActionCongruence
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]

local notation "E" => EuclideanSpace ℝ (Fin n)

set_option maxHeartbeats 1200000 in
set_option backward.isDefEq.respectTransparency false in
theorem lExponentialFamily_spatial_differential_of_lower_contact
    {J : Set ℝ} {F : RicciFlow n M J}
    (hM04 : RicciFlowCurvatureTheory.{u}) {T τmax : ℝ}
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) {p : M}
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (f : M → ℝ)
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) ∞ f (A.gamma Z b))
    (hvalue : f (A.gamma Z b) = A.action Z b / (2 * Real.sqrt b))
    (hlower : ∀ᶠ x in 𝓝 (A.gamma Z b), f x ≤ reducedLength F T p x b)
    (v : TangentSpace (𝓡 n) (A.gamma Z b)) :
    mvfderiv (𝓡 n) f (A.gamma Z b) v =
      (F.metric (T - b)).inner (A.gamma Z b) (curveVelocity (A.gamma Z) b) v := by
  let q := A.gamma Z b
  let H := Real.sqrt b
  let e := chartAt E q
  let y0 := e q
  let v' : E := v
  have hH : 0 < H := Real.sqrt_pos.mpr hb
  have hden : 2 * H ≠ 0 := (mul_pos zero_lt_two hH).ne'
  have hqsrc : q ∈ e.source := mem_chart_source E q
  have hytarget : y0 ∈ e.target := e.map_source hqsrc
  have heq : e.symm y0 = q := e.left_inv hqsrc
  obtain ⟨Φ, U, V, hU, hV, hyV, hVe, hVU, hΦ, hstart, hend, hcenter⟩ :=
    lExponentialFamily_exists_square_endpoint_family A Z b hb hmax
  let B : E → ℝ := fun y ↦ backwardLLength F T 0 b (fun t ↦ Φ (y, Real.sqrt t))
  have hB : ContDiffAt ℝ ∞ B y0 := by
    have h := contDiffAt_smoothSquareFamily_action F hM04 T τmax hτmax hwindow
      Φ U hU hΦ (y0, b) ⟨hb, hmax⟩ (fun r hr ↦ hVU
        ⟨hyV, mul_nonneg hH.le hr.1, mul_le_of_le_one_right hH.le hr.2⟩)
    exact h.comp y0 (contDiffAt_id.prodMk contDiffAt_const)
  have hB0 : B y0 = A.action Z b := by
    apply backwardLLength_congr_Ioo F T 0 b hb.le
    intro t ht
    change Φ ((chartAt E (A.gamma Z b)) (A.gamma Z b), Real.sqrt t) = A.gamma Z t
    rw [hcenter (Real.sqrt t) ⟨Real.sqrt_nonneg t, Real.sqrt_le_sqrt ht.2.le⟩,
      A.square_agrees Z (Real.sqrt t) ⟨Real.sqrt_nonneg t,
        Real.sqrt_lt_sqrt ht.1.le (ht.2.trans hmax)⟩, Real.sq_sqrt ht.1.le]
  have hcompare (y : E) (hy : y ∈ V) :
      reducedLength F T p (e.symm y) b ≤ B y / (2 * H) := by
    let D := (fun s : ℝ ↦ (y, s)) ⁻¹' U
    have hD : IsOpen D := hU.preimage (continuous_const.prodMk continuous_id)
    have hφ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞ (fun s ↦ Φ (y, s)) D :=
      hΦ.comp (contDiff_const.prodMk contDiff_id).contMDiff.contMDiffOn (fun s hs ↦ hs)
    obtain ⟨P, hP, _⟩ := exists_backwardPath_of_smoothSquareCurve F hM04 T τmax hτmax
      hwindow b hb hmax (fun s ↦ Φ (y, s)) D hD (fun s hs ↦ hVU ⟨hy, hs⟩) hφ
    have hP0 : P.curve 0 = p := by simpa only [hP, Real.sqrt_zero] using hstart y
    have hPb : P.curve b = e.symm y := by simpa only [hP] using hend y
    simpa only [hP] using reducedLength_le_path hL hb hmax.le P hP0 hPb
  have hinv := (mdifferentiable_chart (I := 𝓡 n) q).mdifferentiableAt_symm hytarget
  have hf' : MDifferentiableAt (𝓡 n) (𝓘(ℝ, ℝ)) f (e.symm y0) := by
    rw [heq]
    exact hf.mdifferentiableAt (by simp)
  have hfc : DifferentiableAt ℝ (fun y ↦ f (e.symm y)) y0 :=
    (hf'.comp y0 hinv).differentiableAt
  have hnear : ∀ᶠ y in 𝓝 y0, f (e.symm y) ≤ reducedLength F T p (e.symm y) b := by
    exact hinv.continuousAt.tendsto.eventually
      (p := fun x : M ↦ f x ≤ reducedLength F T p x b) (by
        change ∀ᶠ x in 𝓝 (e.symm y0), f x ≤ reducedLength F T p x b
        rw [heq]
        exact hlower)
  have hmin : IsLocalMin (fun y ↦ B y - 2 * H * f (e.symm y)) y0 := by
    have hzero : B y0 - 2 * H * f (e.symm y0) = 0 := by
      rw [heq, hvalue, hB0, mul_div_cancel₀ _ hden, sub_self]
    filter_upwards [hV.mem_nhds hyV, hnear] with y hy hl
    rw [hzero]
    exact sub_nonneg.mpr (by
      simpa only [mul_comm] using
        (le_div_iff₀ (mul_pos zero_lt_two hH)).mp (hl.trans (hcompare y hy)))
  have hd := hmin.hasFDerivAt_eq_zero
    ((hB.differentiableAt (by simp)).hasFDerivAt.sub (hfc.hasFDerivAt.const_mul (2 * H)))
  have hstat := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hd
  change fderiv ℝ B y0 v - (2 * H) * fderiv ℝ (fun y ↦ f (e.symm y)) y0 v = 0 at hstat
  have hcoord := mvfderiv_chartVectorField q f y0 v hytarget hf'
  rw [heq, chartVectorField_self] at hcoord
  have hterminal : (curveVelocity (n := n) (fun r : ℝ ↦ Φ (y0 + r • v', H)) 0 : E) = v' := by
    have hext : (fun r : ℝ ↦ Φ (y0 + r • v', H)) = fun r ↦ e.symm (y0 + r • v') :=
      funext (fun r ↦ hend (y0 + r • v'))
    rw [hext, curveVelocity_comp_initial_line e.symm y0 v' hinv,
      ← chartVectorField_at_inverse q v' y0 hytarget, heq, chartVectorField_self]
  have hinitial : (curveVelocity (n := n) (fun r : ℝ ↦ Φ (y0 + r • v', 0)) 0 : E) = 0 := by
    have hext : (fun r : ℝ ↦ Φ (y0 + r • v', 0)) = fun _ ↦ p := funext (fun r ↦ hstart _)
    rw [hext]
    simp only [curveVelocity, mfderiv_const, zero_apply]
  have hfirst := fderiv_smoothSquareFamily_action hM04 hL hτmax hwindow A Z b hb hmax
    Φ U hU hΦ y0 v' (fun s hs ↦ hVU ⟨hyV, hs⟩) hcenter
  have hsmax : H ∈ Set.Ioo 0 (Real.sqrt τmax) := ⟨hH, Real.sqrt_lt_sqrt hb.le hmax⟩
  have hbase : A.squareFamily Z H = q := by
    rw [A.square_agrees Z H ⟨hH.le, hsmax.2⟩, Real.sq_sqrt hb.le]
  have hvel := lExponentialFamily_square_velocity_eq A Z H hsmax
  rw [Real.sq_sqrt hb.le] at hvel
  rw [hterminal, hinitial, map_zero, sub_zero, hbase, hvel, map_smul,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at hfirst
  rw [← hcoord, hfirst] at hstat
  exact (mul_left_cancel₀ hden (sub_eq_zero.mp hstat)).symm

end PoincareConjecture.Proofs.M09
