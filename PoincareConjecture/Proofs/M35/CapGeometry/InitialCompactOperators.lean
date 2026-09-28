import PoincareConjecture.Proofs.M35.CapGeometry.JointScalarOperators
import PoincareConjecture.Proofs.M35.RawFlow.ArclengthSlabContinuity










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness



theorem exists_initial_radial_carrier_compact
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta : ℝ}
    (htheta : theta ∈ Ico 0 E.flow.base.lifetime) (R : ℝ) :
    ∃ K : Set StandardCapSpace, IsCompact K ∧ ∀ t ∈ Icc 0 theta,
      ∀ y : StandardCapSpace, radialArclength (E.flow.metric t) ‖y‖ ≤ R → y ∈ K := by
  have hc : ContinuousOn (fun t => rawInverseRadius P E.flow.base E.rotation_invariant t R)
      (Icc 0 theta) :=
    (rawInverseRadius_continuousOn_slab E.flow.base P E.rotation_invariant
      htheta.1 htheta.2).comp (continuousOn_id.prodMk continuousOn_const)
      (fun _ ht => ⟨ht, mem_univ _⟩)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨Metric.closedBall 0 (|B| + 1), isCompact_closedBall _ _, ?_⟩
  intro t ht y hy
  have htime : t ∈ Ico 0 E.flow.base.lifetime := ⟨ht.1, ht.2.trans_lt htheta.2⟩
  have hinverse : radialArclength (E.flow.metric t)
      (rawInverseRadius P E.flow.base E.rotation_invariant t R) = R := by
    convert! radialArclength_rawInverseRadius P E.flow.base E.rotation_invariant htime R using 1
  have hnorm : ‖y‖ ≤ rawInverseRadius P E.flow.base E.rotation_invariant t R :=
    (radialArclength_strictMono (E.flow.metric t)).le_iff_le.mp (hinverse.symm ▸ hy)
  have hh := hB t ht
  change |rawInverseRadius P E.flow.base E.rotation_invariant t R| ≤ B at hh
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (hnorm.trans (le_abs_self _)).trans (hh.trans (by linarith only [le_abs_self B]))



theorem exists_compact_initial_scalar_operator_bounds
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    {theta : ℝ} (htheta : theta ∈ Ico 0 E.flow.base.lifetime)
    {K : Set StandardCapSpace} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ t ∈ Icc 0 theta, ∀ y ∈ K,
      B⁻¹ ≤ (E.flow.connection t).scalarCurvature y ∧
      (E.flow.connection t).scalarCurvature y ≤ B ∧
      scalarGradientNorm (E.flow.metric t) (E.flow.connection t) y <
        B * (E.flow.connection t).scalarCurvature y ^ (3 / 2 : ℝ) ∧
      |(E.flow.connection t).laplacian (E.flow.connection t).scalarCurvature y +
        2 * (E.flow.connection t).ricciNormSq y| <
          B * (E.flow.connection t).scalarCurvature y ^ 2 := by
  let S : Set (ℝ × StandardCapSpace) := Icc 0 theta ×ˢ K
  let R := fun p : ℝ × StandardCapSpace => (E.flow.connection p.1).scalarCurvature p.2
  have hsub : S ⊆ Ico 0 E.flow.base.lifetime ×ˢ univ :=
    fun _ hp => ⟨⟨hp.1.1, hp.1.2.trans_lt htheta.2⟩, mem_univ _⟩
  have hpos (p : ℝ × StandardCapSpace) (hp : p ∈ S) : 0 < R p :=
    E.scalar_pos (hsub hp).1 p.2
  have hR : ContinuousOn R S :=
    E.flow.base.flow.contMDiffOn_scalarCurvature.continuousOn.mono hsub
  have hi : ContinuousOn (fun p => (R p)⁻¹) S :=
    hR.inv₀ (fun p hp => (hpos p hp).ne')
  have hg : ContinuousOn (fun p : ℝ × StandardCapSpace =>
      scalarGradientNorm (E.flow.metric p.1) (E.flow.connection p.1) p.2 /
        R p ^ (3 / 2 : ℝ)) S :=
    ((continuousOn_flow_scalarGradientNorm E.flow.base.flow).mono hsub).div
      (hR.rpow_const (fun p hp => Or.inl (hpos p hp).ne'))
      (fun p hp => (Real.rpow_pos_of_pos (hpos p hp) _).ne')
  have he : ContinuousOn (fun p : ℝ × StandardCapSpace =>
      |(E.flow.connection p.1).laplacian (E.flow.connection p.1).scalarCurvature p.2 +
        2 * (E.flow.connection p.1).ricciNormSq p.2| / R p ^ 2) S :=
    ((continuousOn_flow_scalar_evolution E.flow.base.flow).mono hsub).abs.div
      (hR.pow 2) (fun p hp => pow_ne_zero _ (hpos p hp).ne')
  have hS : IsCompact S := isCompact_Icc.prod hK
  obtain ⟨Br, hBr⟩ := hS.exists_bound_of_continuousOn hR
  obtain ⟨Bi, hBi⟩ := hS.exists_bound_of_continuousOn hi
  obtain ⟨Bg, hBg⟩ := hS.exists_bound_of_continuousOn hg
  obtain ⟨Be, hBe⟩ := hS.exists_bound_of_continuousOn he
  let B := |Br| + |Bi| + |Bg| + |Be| + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hBrB : Br < B := by
    dsimp only [B]
    linarith only [le_abs_self Br, abs_nonneg Bi, abs_nonneg Bg, abs_nonneg Be]
  have hBiB : Bi < B := by
    dsimp only [B]
    linarith only [le_abs_self Bi, abs_nonneg Br, abs_nonneg Bg, abs_nonneg Be]
  have hBgB : Bg < B := by
    dsimp only [B]
    linarith only [le_abs_self Bg, abs_nonneg Br, abs_nonneg Bi, abs_nonneg Be]
  have hBeB : Be < B := by
    dsimp only [B]
    linarith only [le_abs_self Be, abs_nonneg Br, abs_nonneg Bi, abs_nonneg Bg]
  refine ⟨B, hB, ?_⟩
  intro t ht y hy
  have hp : (t, y) ∈ S := ⟨ht, hy⟩
  have hRp : 0 < R (t, y) := hpos _ hp
  have hiB : (R (t, y))⁻¹ ≤ B :=
    (le_abs_self _).trans ((hBi (t, y) hp).trans hBiB.le)
  have hlower : B⁻¹ ≤ R (t, y) := by
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hRp) hiB
  refine ⟨hlower, (le_abs_self _).trans ((hBr (t, y) hp).trans hBrB.le), ?_, ?_⟩
  · apply (div_lt_iff₀ (Real.rpow_pos_of_pos hRp (3 / 2 : ℝ))).mp
    exact (le_abs_self _).trans ((hBg (t, y) hp)) |>.trans_lt hBgB
  · apply (div_lt_iff₀ (sq_pos_of_pos hRp)).mp
    exact (le_abs_self _).trans ((hBe (t, y) hp)) |>.trans_lt hBeB

end PoincareConjecture.M35.Uniqueness
