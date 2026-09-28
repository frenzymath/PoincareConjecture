import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundFourJets
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundActualScalar
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_FiniteScalarBound
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarPullback
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_ScalarScaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M44

local notation "E" => EuclideanSpace ℝ (Fin 3)

theorem exists_round_scalar_evolution_bound (P : M44CapPersistencePredecessors.{u}) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type u} [TopologicalSpace X]
      [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X] [T2Space X]
      {g : RiemannianMetric 3 X} (D : LeviCivitaData g) {epsilon : ℝ}
      (R : SingularRoundComponent g epsilon), epsilon ≤ 1 / 200 → ∀ x ∈ R.carrier,
        |D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x| ≤
          C * D.scalarCurvature x ^ 2 := by
  obtain ⟨B, _, hB⟩ := exists_round_comparison_coordinate_bounds
  obtain ⟨C, hC, hbound⟩ := exists_scalar_evolution_bound_of_coordinate_jets 3
    (show (0 : ℝ) < 1 / 2 by norm_num) B
  refine ⟨C, hC, ?_⟩
  intro X _ _ _ _ g D epsilon R hsmall x hx
  have horder : 4 ≤ ⌊epsilon⁻¹⌋₊ := by
    have hinv : (4 : ℝ) ≤ epsilon⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ R.epsilon_pos]
      linarith
    exact Nat.le_floor hinv
  obtain ⟨f, V, gB, DB, hf0, hV, h0V, hf, hinv, hcurv, hgram, hjets⟩ :=
    hB R (by linarith) horder (R.inverse x)
  have hf0' : f 0 = x := hf0.trans (R.right_inverse hx)
  let gQ := m01RescaledMetric g R.scale R.scale_pos
  let DQ := m01RescaledMetric_connection g D R.scale R.scale_pos
  obtain ⟨gE, DE, W, hW, h0W, hWV, hmetric⟩ :=
    RiemannianMetric.exists_local_realization hV h0V (gQ.pullbackCoefficients f)
      (fun y hy => (gQ.contDiffAt_pullbackCoefficients
        (hf.contMDiffAt (hV.mem_nhds hy))).contDiffWithinAt)
      (fun y _ v w => gQ.symm (f y) _ _)
      (fun y hy v hv => by
        apply gQ.pos (f y)
        intro hz
        apply hv
        apply (hinv y hy).injective
        rw [map_zero]
        exact hz)
  have hcoeff : gE.euclideanCoefficients =ᶠ[𝓝 0]
      (fun y => R.scale • g.pullbackCoefficients f y) := by
    filter_upwards [hW.mem_nhds h0W] with y hy
    exact hmetric y hy
  obtain ⟨hfour, hell, herror⟩ := hjets gE hcoeff
  have hlocal := hbound gE DE 0 hfour hell
  have hpositive := scalarCurvature_three_le_of_round_metric_error DB DE 0
    R.epsilon_pos.le hsmall hcurv hgram (fun j hj => herror j (by omega))
  have hgeom (y : E) (hy : y ∈ W) (v w : E) :
      gE.inner y v w = gQ.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y v)
        (mfderiv (𝓡 3) (𝓡 3) f y w) :=
    congrArg (fun H => H v w) (hmetric y hy)
  have hevo := scalar_evolution_eq_of_metric_pullback DE DQ hW (hf.mono hWV)
    (fun y hy => hinv y (hWV hy)) hgeom h0W (scalar_smooth_of_predecessors P DQ (f 0))
  have hscalar := (scalar_ricciNormSq_eq_of_metric_pullback DE DQ
    (hf.contMDiffAt (hV.mem_nhds h0V))
    (eventually_of_mem (hW.mem_nhds h0W) (fun y hy => hinv y (hWV hy)))
    (eventually_of_mem (hW.mem_nhds h0W) hgeom)).1
  rw [hevo, hf0'] at hlocal
  rw [← hscalar, hf0'] at hpositive
  have hscale := rescaled_scalar_evolution D R.scale_pos x (scalar_smooth_of_predecessors P D)
  have hscaleR : DQ.scalarCurvature x = D.scalarCurvature x / R.scale :=
    M13.homothety_scalarCurvature_eq g gQ (Diffeomorph.refl (𝓡 3) X ∞)
      R.scale R.scale_pos (rescaledMetric_identity_homothety R.scale_pos) D DQ x
  change DQ.laplacian DQ.scalarCurvature x + 2 * DQ.ricciNormSq x = _ at hscale
  rw [hscale, abs_div, abs_of_pos (sq_pos_of_pos R.scale_pos)] at hlocal
  rw [hscaleR] at hpositive
  have hR := (le_div_iff₀ R.scale_pos).mp hpositive
  have hsq : R.scale ^ 2 ≤ D.scalarCurvature x ^ 2 := by nlinarith [R.scale_pos]
  exact ((div_le_iff₀ (sq_pos_of_pos R.scale_pos)).mp hlocal).trans
    (mul_le_mul_of_nonneg_left hsq hC.le)

theorem exists_round_scalar_rate_within (P : M44CapPersistencePredecessors.{u}) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X : Type u} [TopologicalSpace X]
      [ChartedSpace E X] [IsManifold (𝓡 3) ∞ X] [T2Space X]
      {J : Set ℝ} (F : RicciFlow 3 X J) {t : ℝ}, t ∈ J →
      ∀ {epsilon : ℝ} (R : SingularRoundComponent (F.metric t) epsilon),
        epsilon ≤ 1 / 200 → ∀ x ∈ R.carrier, ∃ d : ℝ,
          HasDerivWithinAt (fun s => (F.connection s).scalarCurvature x) d J t ∧
            |d| ≤ C * (F.connection t).scalarCurvature x ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_round_scalar_evolution_bound P
  refine ⟨C, hC, ?_⟩
  intro X _ _ _ _ J F t ht epsilon R hsmall x hx
  exact ⟨_, P.curvature.scalar_evolution 3 X J F t ht x,
    hbound (F.connection t) R hsmall x hx⟩

end PoincareConjecture.M44
