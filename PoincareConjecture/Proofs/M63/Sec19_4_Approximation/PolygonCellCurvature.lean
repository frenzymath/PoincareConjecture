import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.HorizontalLift
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.ParallelFrameDensity
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.FlattenedPolygonGeometry
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.CanonicalRampLength
import PoincareConjecture.Proofs.M63.Sec19_4_Approximation.CurveGermGeometry










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}




theorem m63FlattenedPolygon_graph_cell_density (P : M62.CircleProductData F circumference)
    (t : ℝ) {N : ℕ} (polygon : M63GeodesicPolygon (F.metric t) (F.connection t) N)
    (hN : 0 < N) (j : Fin N) {x : ℝ}
    (hx : x ∈ Ioo (m63CellLeft N j) (m63CellLeft N j + m63CellLength N)) :
    let gamma := m63CanonicalRamp P (m63FlattenedPolygon polygon)
    let A := (polygon.side j).speed
    let B := circumference / curvePeriod
    m62Curvature P.flow (fun s _ => gamma s) t x *
      curveSpeed P.flow (fun s _ => gamma s) t x =
        A * B * |deriv (m63Profile N) x| / (A ^ 2 * m63Profile N x ^ 2 + B ^ 2) := by
  let := P.charts.chartedSpace
  let := P.circle.chartedSpace
  let side := polygon.side j
  let phi : ℝ → ℝ := fun s => m63Flattening N s - m63CellLeft N j
  let U := Ioo (m63CellLeft N j) (m63CellLeft N j + m63CellLength N)
  let beta : ℝ → M := fun s => side.map (phi s)
  let gamma := m63CanonicalRamp P beta
  let A := side.speed
  let B := circumference / curvePeriod
  have hU : IsOpen U := isOpen_Ioo
  have hphi : ContDiff ℝ ∞ phi := (m63Flattening_smooth N).sub contDiff_const
  have hphiD (s : ℝ) : HasDerivAt phi (m63Profile N s) s :=
    (m63Flattening_hasDerivAt N s).sub_const _
  have hcell (s : ℝ) (hs : s ∈ U) : phi s ∈ Ioo 0 (m63CellLength N) := by
    have hs' : s - m63CellLeft N j ∈ Ioo 0 (m63CellLength N) := by
      have hs'' : m63CellLeft N j < s ∧ s < m63CellLeft N j + m63CellLength N := hs
      constructor <;> linarith [hs''.1, hs''.2]
    have h := m63Flattening_mem_open_cell hN (j.val : ℤ) hs'
    simpa only [Int.cast_natCast, m63CellLeft, ← add_sub_assoc, add_sub_cancel_left,
      phi] using h
  have hmap : MapsTo phi U side.domain :=
    fun s hs => side.interval_subset (Ioo_subset_Icc_self (hcell s hs))
  have hbase : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ beta U :=
    side.smooth.comp hphi.contMDiff.contMDiffOn hmap
  have hsideVel : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n).tangent ∞
      (fun s => (⟨side.map s, curveVelocity side.map s⟩ : TangentBundle (𝓡 n) M))
      side.domain := by
    have hone : ContMDiff 𝓘(ℝ, ℝ) (𝓘(ℝ, ℝ)).tangent ∞
        (fun s : ℝ => (⟨s, 1⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const
    have ht := side.smooth.contMDiffOn_tangentMapWithin (m := ∞) (by simp)
      side.domain_open.uniqueMDiffOn
    have h := ht.comp hone.contMDiffOn (fun s (hs : s ∈ side.domain) => hs)
    apply h.congr
    intro s hs
    change (⟨side.map s, mfderiv 𝓘(ℝ, ℝ) (𝓡 n) side.map s 1⟩ :
      TangentBundle (𝓡 n) M) =
        ⟨side.map s, mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) side.map side.domain s 1⟩
    rw [mfderivWithin_of_isOpen side.domain_open hs]
  have hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 (n + 1)) ∞ gamma U := by
    have htheta : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞
        (fun s : ℝ => circumference * s / curvePeriod) :=
      contMDiff_iff_contDiff.mpr ((contDiff_const.mul contDiff_id).div_const _)
    exact P.charts.from_product_smooth.comp_contMDiffOn
      (hbase.prodMk (P.circle.quotient_smooth.comp htheta).contMDiffOn)
  let Z := fun s => curveVelocity (n := n) side.map (phi s)
  have hZ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n).tangent ∞
      (fun s => (⟨(gamma s).1, Z s⟩ : TangentBundle (𝓡 n) M)) U :=
    hsideVel.comp hphi.contMDiff.contMDiffOn hmap
  let X := fun s => (P.charts.split (gamma s)).symm (Z s, 0)
  let Y := fun s => P.charts.circleUnit (gamma s)
  have hLift := M63.circleProduct_horizontalLift (F.metric t) (F.connection t)
    P.charts (P.flow.metric t) (P.flow.connection t) (P.metric_eq t) hU hgamma hZ
  have hP := M62.circleProduct_identities P
  have hYs : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 (n + 1)).tangent ∞
      (fun s => (⟨gamma s, Y s⟩ : TangentBundle (𝓡 (n + 1)) P.charts.Point)) U :=
    hP.circle_unit_smooth.comp_contMDiffOn hgamma
  have hXsplit (s : ℝ) : P.charts.split (gamma s) (X s) = (Z s, 0) :=
    (P.charts.split (gamma s)).apply_symm_apply _
  have hYsplit (s : ℝ) : P.charts.split (gamma s) (Y s) =
      (0, P.circle.frame (gamma s).2) := (P.charts.split (gamma s)).apply_symm_apply _
  have hDZ : rampHorizontalCovariantDerivative (F.connection t)
      (fun s => (gamma s).1) Z x = 0 := by
    change rampHorizontalCovariantDerivative (F.connection t)
      (fun s => side.map (phi s)) (fun s => curveVelocity side.map (phi s)) x = 0
    rw [M63.pullback_comp (F.connection t)
      ((hsideVel.contMDiffAt (side.domain_open.mem_nhds (hmap hx))).mdifferentiableAt
        (by simp)) (hphiD x), side.equation (phi x) (hmap hx), smul_zero]
  have hDX : rampHorizontalCovariantDerivative (P.flow.connection t) gamma X x = 0 := by
    apply (P.charts.split (gamma x)).injective
    rw [hLift.2 x hx, hDZ, map_zero]
    rfl
  have hDY : rampHorizontalCovariantDerivative (P.flow.connection t) gamma Y x = 0 :=
    M63.circleUnit_pullback_zero P t
      ((hgamma.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
  have hvel : ∀ᶠ s in 𝓝 x,
      curveVelocity (n := n + 1) gamma s = m63Profile N s • X s + B • Y s := by
    filter_upwards [hU.mem_nhds hx] with s hs
    apply (P.charts.split (gamma s)).injective
    rw [M63.canonicalRamp_velocity P
      ((hbase.contMDiffAt (hU.mem_nhds hs)).mdifferentiableAt (by simp)),
      map_add, map_smul, map_smul, hXsplit, hYsplit]
    have hside : MDifferentiableAt 𝓘(ℝ, ℝ) (𝓡 n) side.map (phi s) :=
      (side.smooth.contMDiffAt (side.domain_open.mem_nhds (hmap hs))).mdifferentiableAt (by simp)
    rw [M63.curveVelocity_comp hside (hphiD s)]
    simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero, zero_add]
    rfl
  have hXX : ∀ᶠ s in 𝓝 x, (P.flow.metric t).inner (gamma s) (X s) (X s) = A ^ 2 := by
    filter_upwards [hU.mem_nhds hx] with s hs
    rw [P.metric_eq, hXsplit]
    simp only [map_zero, add_zero]
    have hnorm := side.constant_speed (phi s) (Ioo_subset_Icc_self (hcell s hs))
    have hsq := congrArg (fun r : ℝ => r ^ 2) hnorm
    unfold RiemannianMetric.tangentNorm at hsq
    have hnonneg : 0 ≤ (F.metric t).inner (side.map (phi s))
        (curveVelocity side.map (phi s)) (curveVelocity side.map (phi s)) := by
      by_cases hz : curveVelocity (n := n) side.map (phi s) = 0
      · simp [hz]
      · exact ((F.metric t).pos _ _ hz).le
    rw [Real.sq_sqrt hnonneg] at hsq
    exact hsq
  have hYY : ∀ᶠ s in 𝓝 x, (P.flow.metric t).inner (gamma s) (Y s) (Y s) = 1 :=
    Filter.Eventually.of_forall (fun s => hP.circle_unit t (gamma s))
  have hXY : ∀ᶠ s in 𝓝 x, (P.flow.metric t).inner (gamma s) (X s) (Y s) = 0 := by
    filter_upwards [] with s
    rw [P.metric_eq, hXsplit, hYsplit]
    simp only [map_zero, zero_apply, add_zero]
  have hdensity := M63.curvature_density_of_parallel_frame P.flow t
    (gamma := gamma) (X := X) (Y := Y) (A := A) (B := B) side.speed_nonnegative
    (div_pos P.circle.positive Real.two_pi_pos)
    (((m63Profile_smooth N).differentiable (by simp) x).hasDerivAt)
    ((hLift.1.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    ((hYs.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    hDX hDY hvel hXX hYY hXY
  have hEq : m63CanonicalRamp P (m63FlattenedPolygon polygon) =ᶠ[𝓝 x] gamma := by
    filter_upwards [hU.mem_nhds hx] with s hs
    apply Prod.ext
    · have hs' : s - m63CellLeft N j ∈ Icc 0 (m63CellLength N) := by
        have hs'' : m63CellLeft N j < s ∧ s < m63CellLeft N j + m63CellLength N := hs
        constructor <;> linarith [hs''.1, hs''.2]
      have h := m63FlattenedPolygon_cell_agreement polygon hN j hs'
      simpa only [← add_sub_assoc, add_sub_cancel_left, phi, side, gamma, beta,
        m63CanonicalRamp] using h
    · rfl
  dsimp only
  rw [M63.curvature_congr_germ P.flow t hEq, M63.curveSpeed_congr_germ P.flow t hEq]
  exact hdensity

end PoincareConjecture
