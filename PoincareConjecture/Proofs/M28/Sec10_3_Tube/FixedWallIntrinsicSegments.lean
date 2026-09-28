import PoincareConjecture.Proofs.M28.Sec10_3_Tube.FixedWallInteriorConfinement
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.ConfinementMinimizers
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicCompactSegment











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.M28

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}

set_option maxHeartbeats 1600000 in




theorem exists_fixed_wall_intrinsic_segments
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) = A.tail true (1 / 2))
    (hA : SmoothSphereIsotopicIn T.carrier A.middleSphere T.cylinder.middleSphere)
    (R : M → ℝ) (hR : ContinuousOn R T.carrier)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        R y ≤ 2 * R z)
    (hdiverge : ∀ C : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → C < R x)
    (hsmall : T.epsilon ≤ neckShorteningEpsilon)
    (hfinite : ∀ p q : U, intrinsicEDist g (U : Set M) (p : M) (q : M) ≠ ⊤) :
    ∃ i ∈ T.chain.shape.active, ∃ (f : M → ℝ) (b : ℝ), 1 / 2 < b ∧ b < 1 ∧
      ContinuousOn f T.carrier ∧
      (∀ x ∈ T.carrier, f x = 0 ↔ x ∈ (T.chain.neck i).central_sphere) ∧
      (T.chain.neck i).carrier ⊆ (U : Set M) ∧
      (∀ x ∈ T.carrier, b < (A.inverse x).2 → 0 < f x) ∧
      ∀ p q : U, 0 < f p → 0 < f q →
        ∃ gamma : ℝ → U, gamma 0 = p ∧ gamma 1 = q ∧ Continuous gamma ∧
          (∀ t : ℝ, (3 / 4 : ℝ) ≤ (A.inverse (gamma t)).2) ∧
          ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
            (intrinsicOpenMetric g U).edist (gamma s) (gamma t) =
              ENNReal.ofReal |s - t| * (intrinsicOpenMetric g U).edist p q := by
  obtain ⟨i, hi, phiMinus, aMinus, bMinus, _haMinus, _haMinusHalf,
      hbMinusHalf, hbMinus, hzeroMinus, htailMinus, _hlowerMinus, hNminus, hpairs⟩ :=
    exists_fixed_wall_interior_confinement T A U hU hA R hR hratio hdiverge
  have hUV : (U : Set M) ⊆ T.carrier := by
    rw [hU]
    exact A.tail_subset_m28 true (by norm_num) (by norm_num)
  have hNminusU : (T.chain.neck i).carrier ⊆ (U : Set M) := by
    intro x hx
    rw [hU]
    have hh := (A.mem_tail_iff_m28 true
      (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)).mp
        (hNminus hx)
    exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
      ⟨hh.1, (by norm_num : (1 / 2 : ℝ) < 3 / 4).trans hh.2⟩
  refine ⟨i, hi, ambientCylinderSignedHeight phiMinus, bMinus, hbMinusHalf, hbMinus,
    continuousOn_ambientCylinderSignedHeight phiMinus, hzeroMinus, hNminusU, ?_, ?_⟩
  · intro x hx hhigh
    rw [htailMinus x hx (Or.inr hhigh)]
    exact sub_pos.mpr (hbMinusHalf.trans hhigh)
  intro p q hp hq
  obtain ⟨j, hj, c, hcmax, hc1, hNplus, phiPlus, aPlus, bPlus,
      _haPlus, _haPlusHalf, _hbPlusHalf, _hbPlus, _hzeroPlus, _htailPlus,
      _hlowerPlus, K, B, hK, hKU, _hpK, _hqK, hheightK, _hB, _hB1,
      _hcapture, hcross⟩ := hpairs (hUV p.property) (hUV q.property) hp hq
  have hcHalf : 1 / 2 < c := hbMinusHalf.trans
    (((le_max_left _ _).trans (le_max_left _ _)).trans_lt hcmax)
  have hc0 : 0 < c := lt_trans (by norm_num) hcHalf
  let N : Bool → EpsilonNeck g := fun k =>
    if k then T.chain.neck j else T.chain.neck i
  have hsmallN : ∀ k, (N k).epsilon ≤ neckShorteningEpsilon := by
    intro k
    cases k with
    | false =>
      change (T.chain.neck i).epsilon ≤ _
      rw [T.chain.epsilon_eq i hi]
      exact hsmall
    | true =>
      change (T.chain.neck j).epsilon ≤ _
      rw [T.chain.epsilon_eq j hj]
      exact hsmall
  have hNU : ∀ k, (N k).carrier ⊆ (U : Set M) := by
    intro k x hx
    rw [hU]
    apply (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
    cases k with
    | false =>
      have hh := (A.mem_tail_iff_m28 true
        (by norm_num : (0 : ℝ) < 3 / 4) (by norm_num : (3 / 4 : ℝ) < 1)).mp
          (hNminus hx)
      exact ⟨hh.1, (by norm_num : (1 / 2 : ℝ) < 3 / 4).trans hh.2⟩
    | true =>
      have hh := (A.mem_tail_iff_m28 true hc0 hc1).mp (hNplus hx)
      exact ⟨hh.1, hcHalf.trans hh.2⟩
  let d := intrinsicEDist g (U : Set M) (p : M) (q : M)
  let ceiling : ℝ := d.toReal + 1
  have hd : d < ENNReal.ofReal ceiling := by
    calc
      d = ENNReal.ofReal d.toReal := (ENNReal.ofReal_toReal (hfinite p q)).symm
      _ < ENNReal.ofReal ceiling :=
        (ENNReal.ofReal_lt_ofReal_iff (by dsimp [ceiling]; positivity)).mpr (by
          dsimp [ceiling]
          linarith)
  obtain ⟨eta, heta0, heta1, heta, hetaU, hetaL⟩ := exists_intrinsic_competitor g hd
  obtain ⟨paths, hpaths, hlimit, _⟩ :=
    exists_confined_sequence_and_minimizer_of_endpoint_crossings g U hK hKU N hsmallN
      (fun k => (N k).central_sphere_subset.trans (hNU k))
      hcross heta0 heta1 heta hetaU hetaL
  obtain ⟨gamma0, hgamma0, hgamma1, hcont, hcapture, hmetric⟩ :=
    exists_intrinsic_metric_segment_of_compact_sequence g U hK hKU
      (fun k => (hpaths k).2.2.1) (fun k => (hpaths k).1)
      (fun k => (hpaths k).2.1) (fun k => (hpaths k).2.2.2.1)
      (fun k => (hpaths k).2.2.2.2) hlimit
  let gamma (t : ℝ) : U :=
    ⟨gamma0 (projIcc 0 1 zero_le_one t),
      hKU (hcapture (projIcc 0 1 zero_le_one t).property)⟩
  have hval {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      (gamma t : M) = gamma0 t := by
    dsimp only [gamma]
    rw [projIcc_of_mem zero_le_one ht]
  refine ⟨gamma, Subtype.ext ((hval (by norm_num)).trans hgamma0),
    Subtype.ext ((hval (by norm_num)).trans hgamma1), ?_, ?_, ?_⟩
  · exact (hcont.domRestrict.comp continuous_projIcc).subtype_mk _
  · intro t
    exact hheightK _ (hcapture (projIcc 0 1 zero_le_one t).property)
  · intro s hs t ht
    rw [intrinsicOpenMetric_edist, intrinsicOpenMetric_edist, hval hs, hval ht]
    exact hmetric s hs t ht

end PoincareConjecture.M28
