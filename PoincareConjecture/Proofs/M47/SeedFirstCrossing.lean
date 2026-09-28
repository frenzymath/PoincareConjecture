import PoincareConjecture.Proofs.M47.SeedCrossingTransport
import PoincareConjecture.Proofs.M34.Lemma12_3_Estimates.Regularity
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_first_seed_scalar_level {f : ℝ → ℝ} {H : ℝ}
    (hf : ContinuousOn f (Icc 0 1)) (hzero : f 0 ≤ H) (hone : H ≤ f 1) :
    ∃ b ∈ Icc (0 : ℝ) 1, f b = H ∧ ∀ s ∈ Icc 0 b, f s ≤ H := by
  have hclosed : IsClosed (Icc (0 : ℝ) 1 ∩ f ⁻¹' Ici H) :=
    hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  obtain ⟨b, hb, hfirst⟩ :=
    (isCompact_Icc.of_isClosed_subset hclosed inter_subset_left).exists_isLeast
      ⟨1, ⟨⟨zero_le_one, le_rfl⟩, hone⟩⟩
  have hvalue : f b = H := by
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc hb.1.1
      (hf.mono (Icc_subset_Icc le_rfl hb.1.2)) ⟨hzero, hb.2⟩
    have hbs : b ≤ s := hfirst ⟨⟨hs.1, hs.2.trans hb.1.2⟩, hfs.ge⟩
    simpa only [le_antisymm hbs hs.2] using hfs
  refine ⟨b, hb.1, hvalue, ?_⟩
  intro s hs
  by_cases hsb : s = b
  · exact hsb ▸ hvalue.le
  · by_contra hhigh
    exact (not_le_of_gt (lt_of_le_of_ne hs.2 hsb))
      (hfirst ⟨⟨hs.1, hs.2.trans hb.1.2⟩, (lt_of_not_ge hhigh).le⟩)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem exists_reversed_seed_crossing_path
    (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (gamma : ℝ → M) (hgamma : ContinuousOn gamma (Icc 0 1))
    {H L : ℝ} (hL : 0 ≤ L)
    (hlow : D.scalarCurvature (gamma 0) ≤ H)
    (hhigh : H ≤ D.scalarCurvature (gamma 1))
    (hspeed : ∀ s ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      g.edist (gamma s) (gamma v) ≤ ENNReal.ofReal (L * |s - v|)) :
    ∃ delta : ℝ → M, delta 1 = gamma 0 ∧
      delta 0 ∈ connectedComponent (gamma 0) ∧
      D.scalarCurvature (delta 0) = H ∧ ContinuousOn delta (Icc 0 1) ∧
      (∀ v ∈ Icc (0 : ℝ) 1, D.scalarCurvature (delta v) ≤ H) ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
        g.edist (delta s) (delta v) ≤ ENNReal.ofReal (L * |s - v|) := by
  obtain ⟨b, hb, hvalue, hbefore⟩ := exists_first_seed_scalar_level
    ((M34.contMDiff_scalarCurvature D).continuous.comp_continuousOn hgamma) hlow hhigh
  let f : ℝ → ℝ := fun v => b * (1 - v)
  have hmem (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 1) : f v ∈ Icc 0 b := by
    dsimp only [f]
    exact ⟨mul_nonneg hb.1 (sub_nonneg.mpr hv.2), by nlinarith [mul_nonneg hb.1 hv.1]⟩
  have hmaps : MapsTo f (Icc 0 1) (Icc 0 1) :=
    fun v hv => ⟨(hmem v hv).1, (hmem v hv).2.trans hb.2⟩
  let delta := gamma ∘ f
  have hzero : delta 0 = gamma b := by simp only [delta, Function.comp_apply, f, sub_zero, mul_one]
  have hone : delta 1 = gamma 0 := by simp only [delta, Function.comp_apply, f, sub_self, mul_zero]
  have hcomponent : gamma b ∈ connectedComponent (gamma 0) :=
    (isPreconnected_Icc.image gamma hgamma).subset_connectedComponent
      ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩ ⟨b, hb, rfl⟩
  refine ⟨delta, hone, hzero ▸ hcomponent, ?_, ?_, ?_, ?_⟩
  · rw [hzero]
    exact hvalue
  · exact hgamma.comp (by fun_prop : ContinuousOn f (Icc 0 1)) hmaps
  · intro v hv
    exact hbefore _ (hmem v hv)
  · intro s hs v hv
    have h := hspeed _ (hmaps hs) _ (hmaps hv)
    have hdiff : |f s - f v| = b * |s - v| := by
      have heq : f s - f v = b * (v - s) := by dsimp only [f]; ring
      rw [heq, abs_mul, abs_of_nonneg hb.1, abs_sub_comm]
    rw [hdiff] at h
    exact h.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (abs_nonneg _) hb.2) hL))

theorem exists_old_prefix_high_point_volume (P : M47Predecessors.{u})
    (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    (H L : ℝ) (hlevel : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ H) (hL : 0 < L) :
    ∃ d k : ℝ, 0 < d ∧ 0 < k ∧
      ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F),
        SurgeryPrefixControls p F O →
        ∀ t ∈ surgeryObservationInterval O ∩ prefixFinalInterval p,
          ∀ z y : (F.slice t).carrier,
            ¬ SurgeryPositiveComponentAt F t z →
            (F.connection t).scalarCurvature z ≤ H →
            H ≤ (F.connection t).scalarCurvature y →
            (F.metric t).edist z y < ENNReal.ofReal L →
            ENNReal.ofReal (k * d ^ 3) ≤
              calibratedMetricVolume (F.metric t) ((F.metric t).ball z d) := by
  obtain ⟨d, k, hd, hk, htransport⟩ :=
    exists_old_prefix_crossing_transport P S p compatible H L hlevel
  refine ⟨d, k, hd, hk, ?_⟩
  intro F O old t ht z y hpositive hlow hhigh hdist
  let : CompactSpace (F.slice t).carrier :=
    isCompact_univ_iff.mp (F.slices_compact t (O.interval_subset ht.1))
  obtain ⟨gamma, hzero, hone, _, hgamma, hspeed⟩ :=
    exists_seed_path_of_distance (F.metric t) z y hL hdist
  obtain ⟨delta, hlast, hcomponent, hcross, hdelta, hbound, hspeed'⟩ :=
    exists_reversed_seed_crossing_path (F.metric t) (F.connection t) gamma hgamma
      (H := H) (L := L) hL.le
      (by rwa [hzero]) (by rwa [hone]) hspeed
  have hnotpositive : ¬ SurgeryPositiveComponentAt F t (delta 0) :=
    not_positive_of_mem_component hpositive (by rwa [hzero] at hcomponent)
  have h := htransport F O old t ht delta hdelta hnotpositive hcross hbound hspeed'
  simpa only [hlast, hzero] using h

end PoincareConjecture.Proofs.M47
