import PoincareConjecture.Proofs.M35.CapGeometry.SelectedAmbientBall
import PoincareConjecture.Proofs.M35.Thm12_28.CompactScalarOperators
import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.M06
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Controls

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M35.OrdinaryRealization

private theorem scalar_eq_of_metric_eq
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g h : RiemannianMetric 3 M} (heq : g = h)
    (D : LeviCivitaData g) (D' : LeviCivitaData h) (z : M) :
    D.scalarCurvature z = D'.scalarCurvature z := by
  subst h
  exact D.scalarCurvature_eq D' z

theorem blowupSequence_normalized_ball_scalar_operator_bounds
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    {kappa : ℝ} (A : BlowupAncientKappaIdentification L.limit kappa)
    {r : ℝ} (hr : 0 < r) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧ ∀ᶠ k in atTop,
      let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
      let hQ := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
      let g := E.flow.metric (t (L.subsequence k))
      let D := E.flow.connection (t (L.subsequence k))
      let G : RiemannianMetric 3 StandardCapSpace := M13.scaleSmoothMetric g Q hQ
      ∀ y ∈ G.ball (x (L.subsequence k)) r,
        m * Q ≤ D.scalarCurvature y ∧ D.scalarCurvature y ≤ M * Q ∧
        scalarGradientNorm g D y ≤ M * (Q * Real.sqrt Q) ∧
        |D.laplacian D.scalarCurvature y + 2 * D.ricciNormSq y| ≤ M * Q ^ 2 := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : MeasurableSpace L.limit.carrier.carrier := L.limit.carrier.measurableSpace
  have : BorelSpace L.limit.carrier.carrier := L.limit.carrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  have : T3Space L.limit.carrier.carrier := L.limit.carrier.t3Space
  have : SecondCountableTopology L.limit.carrier.carrier := L.limit.carrier.secondCountable
  have : ConnectedSpace L.limit.carrier.carrier := L.limit.connectedSpace
  let g := L.limit.flow.metric 0
  let D := L.limit.flow.connection 0
  let R := D.scalarCurvature
  let V := fun z => D.laplacian D.scalarCurvature z + 2 * D.ricciNormSq z
  have hpos (z : L.limit.sliceCarrier.carrier) : 0 < R z :=
    (A.solution.scalar_pos P.curvature (differentialHarnackAncientTheory P.curvature)
      0 le_rfl z).trans_eq
        (scalar_eq_of_metric_eq (A.metric_eq 0 le_rfl) (A.solution.flow.connection 0) D z)
  let K : Set L.limit.sliceCarrier.carrier := closure (g.ball L.limit.base (3 * r))
  have hK : IsCompact K := Proofs.M09.isCompact_closure_metric_ball g
    (L.limit.complete 0 L.limit.zero_mem) L.limit.base (3 * r)
  obtain ⟨j, hj⟩ := hK.elim_directed_cover L.exhaustion.space L.exhaustion.space_open
    (fun z _ => by rw [L.exhaustion.space_covers]; exact mem_univ z)
    (fun i j => ⟨max i j, L.exhaustion.space_increasing (le_max_left _ _),
      L.exhaustion.space_increasing (le_max_right _ _)⟩)
  have hscalar : Continuous R :=
    (Proofs.M09.scalarCurvature_contMDiff P.curvature D).continuous
  have hinv : Continuous (fun z => (R z)⁻¹) :=
    hscalar.inv₀ (fun z => (hpos z).ne')
  have hgrad := continuous_scalarGradientNorm D
    (Proofs.M09.scalarCurvature_contMDiff P.curvature D)
  have hevol : Continuous V := continuous_scalar_evolution_slice P L.limit.flow L.limit.zero_mem
  obtain ⟨Br, hBr⟩ := hK.exists_bound_of_continuousOn hscalar.continuousOn
  obtain ⟨Bi, hBi⟩ := hK.exists_bound_of_continuousOn hinv.continuousOn
  obtain ⟨Bg, hBg⟩ := hK.exists_bound_of_continuousOn hgrad.continuousOn
  obtain ⟨Bv, hBv⟩ := hK.exists_bound_of_continuousOn hevol.continuousOn
  let B := |Br| + |Bi| + |Bg| + |Bv| + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hrB : Br ≤ B := by
    dsimp only [B]
    linarith only [le_abs_self Br, abs_nonneg Bi, abs_nonneg Bg, abs_nonneg Bv]
  have hiB : Bi ≤ B := by
    dsimp only [B]
    linarith only [le_abs_self Bi, abs_nonneg Br, abs_nonneg Bg, abs_nonneg Bv]
  have hgB : Bg ≤ B := by
    dsimp only [B]
    linarith only [le_abs_self Bg, abs_nonneg Br, abs_nonneg Bi, abs_nonneg Bv]
  have hvB : Bv ≤ B := by
    dsimp only [B]
    linarith only [le_abs_self Bv, abs_nonneg Br, abs_nonneg Bi, abs_nonneg Bg]
  have hfloor (z) (hz : z ∈ K) : B⁻¹ ≤ R z := by
    have hi : (R z)⁻¹ ≤ B := (le_abs_self _).trans ((hBi z hz).trans hiB)
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr (hpos z)) hi
  let eta := B⁻¹ / 2
  have heta : 0 < eta := div_pos (inv_pos.mpr hB) (by norm_num)
  obtain ⟨Ns, _, hs⟩ := blowupSequence_terminal_scalar_uniform_compact
    P E t x ht hR L j K hK hj eta heta
  obtain ⟨No, _, ho⟩ := blowupSequence_terminal_scalar_operators_uniform_compact
    P E t x ht hR L j K hK hj 1 zero_lt_one
  refine ⟨eta, B + eta + 1, heta, by positivity, ?_⟩
  filter_upwards [blowupSequence_normalized_ball_retained P E t x ht hR L hr,
    eventually_ge_atTop Ns, eventually_ge_atTop No] with k hk hks hko
  let Q := (blowupSequence P E t x ht hR).scale (L.subsequence k)
  have hQ : 0 < Q := (blowupSequence P E t x ht hR).base_scalar_pos (L.subsequence k)
  let gk := E.flow.metric (t (L.subsequence k))
  let Dk := E.flow.connection (t (L.subsequence k))
  let phi (z : L.limit.sliceCarrier.carrier) := ((L.embedding k).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ z).val
  dsimp only
  intro y hy
  obtain ⟨z, hz, hzy⟩ := hk hy
  have hzK : z ∈ K := subset_closure (hz.trans_le
    (ENNReal.ofReal_le_ofReal (by linarith only [hr] : 2 * r ≤ 3 * r)))
  have heq : phi z = y := hzy
  rw [← heq]
  have herr : |Dk.scalarCurvature (phi z) / Q - R z| < eta := hs k hks z hzK
  have hoperators := ho k hko z hzK
  have hgr : |scalarGradientNorm gk Dk (phi z) / (Q * Real.sqrt Q) -
      scalarGradientNorm g D z| < 1 := hoperators.1
  have hev : |(Dk.laplacian Dk.scalarCurvature (phi z) + 2 * Dk.ricciNormSq (phi z)) /
      Q ^ 2 - V z| < 1 := hoperators.2
  have hrlower : eta ≤ Dk.scalarCurvature (phi z) / Q := by
    have hf := hfloor z hzK
    have hl := (abs_lt.mp herr).1
    dsimp only [eta] at hl ⊢
    linarith
  have hrupper : Dk.scalarCurvature (phi z) / Q ≤ B + eta + 1 := by
    have hc := (le_abs_self (R z)).trans ((hBr z hzK).trans hrB)
    have hu := (abs_lt.mp herr).2
    linarith
  have hgradupper : scalarGradientNorm gk Dk (phi z) / (Q * Real.sqrt Q) ≤
      B + eta + 1 := by
    have hc := (le_abs_self (scalarGradientNorm g D z)).trans ((hBg z hzK).trans hgB)
    have hu := (abs_lt.mp hgr).2
    linarith
  have hevolupper : |Dk.laplacian Dk.scalarCurvature (phi z) +
      2 * Dk.ricciNormSq (phi z)| / Q ^ 2 ≤ B + eta + 1 := by
    have hc : |V z| ≤ B := (hBv z hzK).trans hvB
    have hb := abs_add_le
      ((Dk.laplacian Dk.scalarCurvature (phi z) + 2 * Dk.ricciNormSq (phi z)) /
        Q ^ 2 - V z) (V z)
    rw [sub_add_cancel, abs_div, abs_of_pos (sq_pos_of_pos hQ)] at hb
    linarith
  exact ⟨(le_div_iff₀ hQ).mp hrlower, (div_le_iff₀ hQ).mp hrupper,
    (div_le_iff₀ (mul_pos hQ (Real.sqrt_pos.mpr hQ))).mp hgradupper,
    (div_le_iff₀ (sq_pos_of_pos hQ)).mp hevolupper⟩

end PoincareConjecture.M35.OrdinaryRealization
