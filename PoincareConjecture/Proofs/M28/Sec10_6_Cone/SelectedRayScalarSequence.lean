import PoincareConjecture.Proofs.M28.Mathlib.ScalarRadiusSubsequence
import PoincareConjecture.Proofs.M28.Mathlib.MetricEndRayChord
import PoincareConjecture.Proofs.M28.Sec10_5_Angles.SelectedEndRayChordLimits
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.SelectedRayScalarRadius
import PoincareConjecture.Proofs.M28.Sec10_6_Cone.CenteredNeckRadiusFloor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

theorem exists_selected_ray_scalar_sequence_accuracy :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ (1 / 200 : ℝ) ∧
      ∀ (M : Type u) [TopologicalSpace M] [T2Space M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T3Space M]
        (g : RiemannianMetric 3 M) (D : LeviCivitaData g) (X : Set M)
        (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
        (U : TopologicalSpace.Opens M) [PreconnectedSpace U],
        (U : Set M) = A.tail true (1 / 2) → IsCompact (frontier (U : Set M)) →
        SmoothSphereIsotopicIn T.carrier A.middleSphere T.cylinder.middleSphere →
        ∀ C0 : NeckOnlyCover g, (U : Set M) ⊆ C0.X → C0.epsilon ≤ epsilon0 →
        (∀ i ∈ T.chain.shape.active,
          ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
            D.scalarCurvature y ≤ 2 * D.scalarCurvature z) →
        (∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
          ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < D.scalarCurvature x) →
        (∀ x : U, 0 < D.scalarCurvature x) →
        ∀ (f : M → ℝ)
          (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤)
          (DU : LeviCivitaData (intrinsicOpenMetric g U)),
        DU.NonnegativeSectionalCurvature →
        letI := intrinsicOpenMetricSpace g U hfinite
        ∀ (E : UniformSpace.Completion U) (alpha : ℝ),
          E ∉ range ((↑) : U → UniformSpace.Completion U) → 0 < alpha →
          (∀ eta : ℝ, 0 < eta → ∃ c : ℝ, 1 / 2 < c ∧ c < 1 ∧
            ∀ x : U, c < (A.inverse x).2 →
              dist (x : UniformSpace.Completion U) E < eta) →
          (∀ x : U, dist (x : UniformSpace.Completion U) E < alpha → 0 < f x) →
          (∀ p q : U, 0 < f p → 0 < f q →
            ∃ mu : ℝ → U, mu 0 = p ∧ mu 1 = q ∧ Continuous mu ∧
              (∀ t : ℝ, (3 / 4 : ℝ) ≤ (A.inverse (mu t)).2) ∧
              ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
                (intrinsicOpenMetric g U).edist (mu s) (mu t) =
                  ENNReal.ofReal |s - t| * (intrinsicOpenMetric g U).edist p q) →
          ∀ P Q : MetricEndRay E alpha, ¬MetricEndRay.SameEndGerm P Q →
            ∃ (eta B rho : ℝ) (phi : ℕ → ℕ),
              0 < eta ∧ eta ≤ P.length ∧ 0 < B ∧ 0 < rho ∧
              rho ∈ Icc (1 / 16 : ℝ) B ∧ StrictMono phi ∧
              let d : ℕ → ℝ := fun i => eta / ((phi i : ℝ) + 2)
              let x : ℕ → U := fun i => P.point (d i)
              let R : ℕ → ℝ := fun i => D.scalarCurvature (x i)
              (∀ i : ℕ, d i ∈ Ioo (0 : ℝ) eta ∧ d i < P.length ∧
                dist (x i : UniformSpace.Completion U) E = d i ∧
                (3 / 4 : ℝ) ≤ (A.inverse (x i)).2 ∧ 0 < R i ∧
                (1 / 16 : ℝ) < R i * d i ^ 2 ∧ R i * d i ^ 2 ≤ B) ∧
              Tendsto d atTop (𝓝[>] (0 : ℝ)) ∧
              Tendsto (fun i => (x i : UniformSpace.Completion U)) atTop (𝓝 E) ∧
              Tendsto R atTop atTop ∧
              Tendsto (fun i => R i * d i ^ 2) atTop (𝓝 rho) ∧
              Tendsto (fun i => Real.sqrt (R i) * d i) atTop (𝓝 (Real.sqrt rho)) ∧
              Tendsto (fun i => 1 / Real.sqrt (R i)) atTop (𝓝[>] (0 : ℝ)) ∧
              Tendsto (fun i => dist (x i : UniformSpace.Completion U) E /
                (1 / Real.sqrt (R i))) atTop (𝓝 (Real.sqrt rho)) := by
  obtain ⟨epsilon0, hepsilon0, hepsilonSmall, hfloorGeometry⟩ :=
    exists_centered_neck_radius_floor_accuracy.{u}
  refine ⟨epsilon0, hepsilon0, hepsilonSmall, ?_⟩
  intro M _ _ _ _ _ _ _ g D X T A U _ hU hfront hA C0 hUC0 hC0
    hratio hdiverge hpositive f hfinite DU hsec
  let := intrinsicOpenMetricSpace g U hfinite
  intro E alpha houtside halpha htail hbarrier hsegments P Q hdistinct
  have hheight : ∀ x : U, dist (x : UniformSpace.Completion U) E < alpha →
      (3 / 4 : ℝ) ≤ (A.inverse x).2 :=
    cylinder_height_ge_threeQuarter_of_radius_barrier T A U f hfinite
      E alpha hbarrier hsegments
  have hrayLower (S : MetricEndRay E alpha) (s : ℝ)
      (hs : s ∈ Ioc (0 : ℝ) S.length) :
      (3 / 4 : ℝ) ≤ (A.inverse (S.point s)).2 := by
    apply hheight
    rw [S.radius s hs]
    have hlength := S.length_lt
    linarith only [hs.2, hlength, halpha]
  obtain ⟨K, hK, hstrict, hlimit⟩ :=
    exists_selected_end_ray_chord_limits T A U hU f hfinite DU hsec
      E alpha halpha htail hbarrier hsegments
  obtain ⟨m, hm⟩ := exists_metricEndRay_chord_pseudometric E alpha K hK hstrict hlimit
  let := m
  obtain ⟨_hdiam, hjoint, _hequal, _hfixed, _hupper, hzero⟩ := hm
  have hnonzero : dist P Q ≠ 0 := fun h => hdistinct ((hzero P Q).mp h)
  have hpositiveChord : 0 < dist P Q := lt_of_le_of_ne dist_nonneg hnonzero.symm
  obtain ⟨etaUpper, B, hetaUpper, hetaLength, hB, hupper⟩ :=
    exists_selected_ray_scalar_radius_upper T A U hU hA D hratio hdiverge
      hpositive hfinite E houtside alpha P Q (dist P Q ^ 2)
      (sq_pos_of_pos hpositiveChord) (hjoint P Q) (hrayLower P) (hrayLower Q)
  obtain ⟨etaFloor, hetaFloor, hfloor⟩ :=
    hfloorGeometry M g D X T A U hU hfront C0 hUC0 hC0 hdiverge hfinite E houtside
  let eta : ℝ := min etaUpper etaFloor
  have heta : 0 < eta := lt_min hetaUpper hetaFloor
  have hetaP : eta ≤ P.length := (min_le_left _ _).trans hetaLength
  have hproduct (s : ℝ) (hs : s ∈ Ioo (0 : ℝ) eta) :
      (1 / 16 : ℝ) < D.scalarCurvature (P.point s) * s ^ 2 ∧
        D.scalarCurvature (P.point s) * s ^ 2 ≤ B := by
    have hsP : s ∈ Ioc (0 : ℝ) P.length := ⟨hs.1, hs.2.le.trans hetaP⟩
    have hsmall : dist (P.point s : UniformSpace.Completion U) E < etaFloor := by
      rw [P.radius s hsP]
      exact hs.2.trans_le (min_le_right _ _)
    have hlo := hfloor (P.point s) (hrayLower P s hsP) hsmall
    rw [P.radius s hsP] at hlo
    exact ⟨hlo, hupper s ⟨hs.1, hs.2.trans_le (min_le_left _ _)⟩⟩
  obtain ⟨rho, hrho, phi, hphi, hdata⟩ :=
    Real.exists_strict_scalar_radius_subsequence
      (fun s => D.scalarCurvature (P.point s)) heta
      (by norm_num : (0 : ℝ) < 1 / 16) hproduct
  let d : ℕ → ℝ := fun i => eta / ((phi i : ℝ) + 2)
  let x : ℕ → U := fun i => P.point (d i)
  let R : ℕ → ℝ := fun i => D.scalarCurvature (x i)
  obtain ⟨hpoint, hd, hR, hprod, hnormalized, hclock⟩ := hdata
  have hdP (i : ℕ) : d i ∈ Ioc (0 : ℝ) P.length :=
    ⟨(hpoint i).1.1, (hpoint i).1.2.le.trans hetaP⟩
  have hradius (i : ℕ) : dist (x i : UniformSpace.Completion U) E = d i :=
    P.radius (d i) (hdP i)
  have hcompletion : Tendsto (fun i => (x i : UniformSpace.Completion U)) atTop (𝓝 E) := by
    apply Metric.tendsto_nhds.mpr
    intro zeta hzeta
    filter_upwards [((tendsto_nhdsWithin_iff.mp hd).1).eventually
      (Iio_mem_nhds hzeta)] with i hi
    rw [hradius i]
    exact hi
  have hradiusScale : Tendsto
      (fun i => dist (x i : UniformSpace.Completion U) E / (1 / Real.sqrt (R i)))
      atTop (𝓝 (Real.sqrt rho)) := by
    apply hnormalized.congr'
    apply Eventually.of_forall
    intro i
    change Real.sqrt (R i) * d i =
      dist (x i : UniformSpace.Completion U) E / (1 / Real.sqrt (R i))
    rw [hradius i]
    simp only [one_div, div_inv_eq_mul, mul_comm]
  refine ⟨eta, B, rho, phi, heta, hetaP, hB,
    (by linarith only [hrho.1]), hrho, hphi, ?_, hd, hcompletion,
    hR, hprod, hnormalized, hclock, hradiusScale⟩
  intro i
  exact ⟨(hpoint i).1, (hpoint i).1.2.trans_le hetaP, hradius i,
    hrayLower P (d i) (hdP i), (hpoint i).2⟩

end PoincareConjecture.M28
