import PoincareConjecture.Proofs.M47.PositivePinchingPointwise
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Roundness.Preservation
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveSectionalContinuation











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47Positive

open PoincareConjecture.AncientKappaRoundness
open PoincareConjecture.M04

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [CompactSpace M]





theorem exists_initial_complement_pinching
    {J : Set ℝ} (F : RicciFlow 3 M J) {a : ℝ} (ha : a ∈ J)
    (hD : (F.connection a).CurvatureTensorCalculus)
    (hpos : ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric a) x v w →
        0 < (F.connection a).sectionalCurvature x v w) :
    ∃ c : ℝ, 1 ≤ c ∧
      ∀ x : M,
        letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
          ⟨(F.metric a).toRiemannianMetric⟩
        (F.connection a).ricciComplementTensor hD x ∈ tensorPinchingCone c := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨(F.metric a).toRiemannianMetric⟩
  obtain ⟨m, hm, hlower⟩ := PoincareConjecture.Proofs.M46.exists_initial_sectional_lower
    F ha isClosed_univ (fun x _ => hpos x)
  obtain ⟨B, hB⟩ := isCompact_univ.bddAbove_image
    (F.contMDiff_scalarCurvature a ha).continuous.continuousOn
  let B' := max 1 B
  have hB' : 0 ≤ B' := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  have hscalar (x : M) : (F.connection a).scalarCurvature x ≤ B' :=
    (hB ⟨x, mem_univ x, rfl⟩).trans (le_max_right _ _)
  let c := max 1 (B' / m)
  have hc : 1 ≤ c := le_max_left _ _
  have hcm : B' ≤ c * m := (div_le_iff₀ hm).mp (le_max_right _ _)
  refine ⟨c, hc, fun x => (ricciComplement_mem_iff _ hD x c).mpr ?_⟩
  have hsec (v w : TangentSpace (𝓡 3) x) :
      0 ≤ (F.connection a).curvatureTensor x v w v w := by
    have hgram : 0 ≤ metricGram (F.metric a) x v w := by
      change 0 ≤ inner ℝ v v * inner ℝ w w - (inner ℝ v w) ^ 2
      nlinarith only [real_inner_mul_inner_self_le v w]
    exact (mul_nonneg hm.le hgram).trans (hlower x (mem_univ x) v w)
  have hmin (v : TangentSpace (𝓡 3) x) (hv : (F.metric a).inner x v v = 1) :
      m ≤ (F.connection a).ricciComplementEvaluation x ![v, v] :=
    ricciComplement_lower_of_sectional_lower _ hD x m
      (hlower x (mem_univ x)) v hv
  refine ⟨fun v hv => hm.le.trans (hmin v hv), fun v w hv hw => ?_⟩
  have hmax := ricciComplement_le_half_scalar (F.connection a) x hsec v hv
  calc
    (F.connection a).ricciComplementEvaluation x ![v, v] ≤ B' := by
      linarith [hscalar x]
    _ ≤ c * m := hcm
    _ ≤ c * (F.connection a).ricciComplementEvaluation x ![w, w] :=
      mul_le_mul_of_nonneg_left (hmin w hw) (by linarith)




theorem complement_pinching_preserved
    (hC : RicciFlowCurvatureTheory.{u}) {T c : ℝ}
    (F : RicciFlow 3 M (Ico 0 T)) (hc : 1 ≤ c)
    (hinit : ∀ x : M,
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨(F.metric 0).toRiemannianMetric⟩
      (F.connection 0).ricciComplementTensor
        (hC.tensor_calculus 3 M (F.metric 0) (F.connection 0)) x ∈ tensorPinchingCone c) :
    ∀ t ∈ Ico 0 T, ∀ x : M,
      letI : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
        ⟨(F.metric t).toRiemannianMetric⟩
      (F.connection t).ricciComplementTensor
        (hC.tensor_calculus 3 M (F.metric t) (F.connection t)) x ∈ tensorPinchingCone c := by
  intro t ht x
  exact ricciComplement_mem_of_initial F
    (fun s => hC.tensor_calculus 3 M (F.metric s) (F.connection s))
    (hC.scalar_regular 3 M (Ico 0 T) F)
    (hC.curvature_evolution 3 M (Ico 0 T) F) hc hinit ht x





theorem exists_uniform_ricci_pinching
    (hC : RicciFlowCurvatureTheory.{u}) {T : ℝ} (hT : 0 < T)
    (F : RicciFlow 3 M (Ico 0 T))
    (hpos : ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric 0) x v w →
        0 < (F.connection 0).sectionalCurvature x v w) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ epsilon ≤ 1 / 3 ∧
      ∀ t ∈ Ico 0 T, ∀ x : M, ∀ v : TangentSpace (𝓡 3) x,
        (F.metric t).inner x v v = 1 →
          epsilon * (F.connection t).scalarCurvature x ≤
            (F.connection t).ricci x v v := by
  obtain ⟨c, hc, hinit⟩ := exists_initial_complement_pinching F ⟨le_rfl, hT⟩
    (hC.tensor_calculus 3 M (F.metric 0) (F.connection 0)) hpos
  have hden : 0 < c + 2 := by linarith
  refine ⟨1 / (c + 2), div_pos zero_lt_one hden, ?_, ?_⟩
  · apply (div_le_iff₀ hden).mpr
    linarith
  · intro t ht x v hv
    have hpinch := complement_pinching_preserved hC F hc hinit t ht x
    have h := ricci_lower_of_complement_pinching (F.connection t)
      (hC.tensor_calculus 3 M (F.metric t) (F.connection t)) x hc hpinch v hv
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using h





theorem exists_uniform_positive_scalar_lower [SecondCountableTopology M]
    {T : ℝ} (hT : 0 < T) (F : RicciFlow 3 M (Ico 0 T))
    (hpos : ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      LeviCivitaData.IsOrthonormalPair (F.metric 0) x v w →
        0 < (F.connection 0).sectionalCurvature x v w) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Ico 0 T, ∀ x : M,
      r ≤ (F.connection t).scalarCurvature x := by
  obtain ⟨m, hm, hinit⟩ := PoincareConjecture.Proofs.M46.exists_initial_sectional_lower
    F ⟨le_rfl, hT⟩ isClosed_univ (fun x _ => hpos x)
  refine ⟨6 * m, mul_pos (by norm_num) hm, ?_⟩
  intro t ht x
  apply PoincareConjecture.Proofs.M46.scalar_lower_of_sectional_lower (F.connection t) x m
  rcases eq_or_lt_of_le ht.1 with heq | htime
  · subst t
    exact hinit x (mem_univ x)
  · exact PoincareConjecture.Proofs.M46.sectional_lower_on_closed_interval F htime hm.le
      (fun s hs => ⟨hs.1, hs.2.trans_lt ht.2⟩)
      isOpen_univ isClosed_univ hinit t ⟨ht.1, le_rfl⟩ x (mem_univ x)

end PoincareConjecture.M47Positive
