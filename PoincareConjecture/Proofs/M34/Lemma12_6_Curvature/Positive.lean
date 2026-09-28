import PoincareConjecture.Proofs.M34.Lemma12_6_Curvature.Nonnegative
import PoincareConjecture.Proofs.M34.Standard.SectionalPositiveTransfer










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34

open M04



theorem initial_modelLeastSectional_tip_pos (g0 : StandardInitialMetric) :
    0 < modelLeastSectional g0.connection 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : StandardCapSpace → Type _) :=
    ⟨g0.metric.toRiemannianMetric⟩
  obtain ⟨r, hr, htip⟩ := g0.tip_sectional_curvature
  have hball : (0 : StandardCapSpace) ∈ g0.metric.ball 0 r := by
    change Manifold.riemannianEDist (𝓡 3) (0 : StandardCapSpace) 0 < ENNReal.ofReal r
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr hr
  have hbar (u v : TangentSpace (𝓡 3) (0 : StandardCapSpace)) :
      (1 / 4 : ℝ) * metricGram g0.metric 0 u v ≤
        g0.connection.curvatureTensor 0 u v u v := by
    apply sectional_lower_of_surjective_linearMap g0.connection 0
      (LinearMap.id : TangentSpace (𝓡 3) (0 : StandardCapSpace) →ₗ[ℝ]
        TangentSpace (𝓡 3) (0 : StandardCapSpace)) Function.surjective_id
    intro p q hp hq hpq
    have hpp : g0.metric.inner 0 p p = 1 := by
      change inner ℝ p p = 1
      rw [real_inner_self_eq_norm_sq, hp, one_pow]
    have hqq : g0.metric.inner 0 q q = 1 := by
      change inner ℝ q q = 1
      rw [real_inner_self_eq_norm_sq, hq, one_pow]
    have hpq' : g0.metric.inner 0 p q = 0 := hpq
    have ho : LeviCivitaData.IsOrthonormalPair g0.metric 0 p q := ⟨hpp, hqq, hpq'⟩
    have h := htip 0 hball p q ho
    simp only [LeviCivitaData.sectionalCurvature, hpp, hqq, hpq', one_mul,
      zero_pow (by norm_num : 2 ≠ 0), sub_zero, div_one] at h
    simpa only [LinearMap.id_apply, metricGram, hpp, hqq, hpq', one_mul,
      zero_pow (by norm_num : 2 ≠ 0), sub_zero, mul_one] using h.ge
  have hleast : (1 / 4 : ℝ) ≤ modelLeastSectional g0.connection 0 := by
    apply le_modelLeastSectional
    intro p hp
    exact (le_div_iff₀ (metricGram_pos_of_linearIndependent g0.metric 0 p.1 p.2
      (modelOrthonormalPairs_linearIndependent hp))).mpr (hbar p.1 p.2)
  exact lt_of_lt_of_le (by norm_num) hleast



theorem partialFlow_positiveSectional (P : RicciFlowCurvatureTheory.{0})
    {g0 : StandardInitialMetric} (E0 : StandardCapEstimate g0)
    (F : PartialStandardCapFlow g0) :
    ∀ t ∈ Ioo 0 F.lifetime, StandardCapPositiveSectional (F.flow.connection t) := by
  have hpair : (⟨F.flow.metric 0, F.flow.connection 0⟩ :
      Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g) =
        ⟨g0.metric, g0.connection⟩ :=
    Sigma.mk.inj_iff.mpr ⟨F.initial_metric, F.initial_connection⟩
  have hzero : 0 < modelLeastSectional (F.flow.connection 0) 0 := by
    have heq := congrArg (fun p : Σ g : RiemannianMetric 3 StandardCapSpace,
      LeviCivitaData g => modelLeastSectional p.2 0) hpair
    rw [heq]
    exact initial_modelLeastSectional_tip_pos g0
  intro t ht
  have hJ : Icc 0 t ⊆ Ico 0 F.lifetime := fun _ hs => ⟨hs.1, hs.2.trans_lt ht.2⟩
  have hpos := modelLeastSectional_positive_later ht.1 F.flow hJ
    (fun s hs => partialFlow_nonnegativeSectionalCurvature P E0 F s (hJ hs)) 0 hzero
  intro x u v ho
  have h := sectional_lower_of_model_pairs (F.flow.connection t) x
    (modelLeastSectional (F.flow.connection t) x)
    (fun p hp => modelLeastSectional_le (F.flow.connection t) x p hp) u v
  have hgram : metricGram (F.flow.metric t) x u v = 1 := by
    simp only [metricGram, ho.1, ho.2.1, ho.2.2, one_mul,
      zero_pow (by norm_num : 2 ≠ 0), sub_zero]
  rw [hgram, mul_one] at h
  have hcurv := (hpos x).trans_le h
  simpa only [LeviCivitaData.sectionalCurvature, ho.1, ho.2.1, ho.2.2, one_mul,
    zero_pow (by norm_num : 2 ≠ 0), sub_zero, div_one] using hcurv

end PoincareConjecture.M34
