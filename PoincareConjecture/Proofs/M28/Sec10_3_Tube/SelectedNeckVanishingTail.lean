import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SelectedNeckIntrinsicBounds
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicMetricSpace
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.PathCrossingDistance
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderSphereCrossings
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Isotopy.Composition
import Mathlib.Topology.MetricSpace.HausdorffDistance













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M} {X : Set M}






theorem exists_vanishing_selected_cylinder_tail
    (T : EpsilonTubeCertificate g X) (A : OpenCylinderModel T.carrier)
    (U : TopologicalSpace.Opens M) (hU : (U : Set M) = A.tail true (1 / 2))
    (hA : SmoothSphereIsotopicIn T.carrier A.middleSphere T.cylinder.middleSphere)
    (D : LeviCivitaData g) (hR : ContinuousOn D.scalarCurvature T.carrier)
    (hratio : ∀ i ∈ T.chain.shape.active,
      ∀ y ∈ (T.chain.neck i).carrier, ∀ z ∈ (T.chain.neck i).carrier,
        D.scalarCurvature y ≤ 2 * D.scalarCurvature z)
    (hdiverge : ∀ B : ℝ, ∃ d : ℝ, 1 / 2 < d ∧ d < 1 ∧
      ∀ x ∈ T.carrier, d < (A.inverse x).2 → B < D.scalarCurvature x)
    {B : ℝ} (hB : 0 < B) (hdiam : intrinsicDiameter g (U : Set M) ≤ ENNReal.ofReal B)
    (p : U) :
    ∀ eta : ℝ, 0 < eta → ∃ a : ℝ, 1 / 2 < a ∧ a < 1 ∧
      ∀ q r : U, a < (A.inverse q).2 → a < (A.inverse r).2 →
        intrinsicEDist g (U : Set M) (q : M) (r : M) < ENNReal.ofReal eta := by
  classical
  have hpair (q r : U) :
      intrinsicEDist g (U : Set M) (q : M) (r : M) ≤ ENNReal.ofReal B := by
    have hle : intrinsicEDist g (U : Set M) (q : M) (r : M) ≤
        intrinsicDiameter g (U : Set M) := le_sSup ⟨(q, r), rfl⟩
    exact hle.trans hdiam
  have hfinite (q r : U) : intrinsicEDist g (U : Set M) (q : M) (r : M) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hpair q r)
  let := intrinsicOpenMetricSpace g U hfinite
  let gU := intrinsicOpenMetric g U
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : U → Type _) :=
    ⟨gU.toRiemannianMetric⟩
  have hed (q r : U) : gU.edist q r = ENNReal.ofReal (dist q r) := by
    change edist q r = _
    exact edist_dist q r
  have hdistBound (q r : U) : dist q r ≤ B := by
    apply (ENNReal.ofReal_le_ofReal_iff hB.le).mp
    rw [← hed, intrinsicOpenMetric_edist]
    exact hpair q r
  have hUV : (U : Set M) ⊆ T.carrier := by
    rw [hU]
    exact A.tail_subset_m28 true (by norm_num) (by norm_num)
  have hphalf : 1 / 2 < (A.inverse p).2 :=
    ((A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mp (hU ▸ p.property)).2
  have hpone : (A.inverse p).2 < 1 := (A.inverse_mem p (hUV p.property)).2.2
  obtain ⟨c0, hpc0, hc01⟩ := exists_between hpone
  have hc0 : 1 / 2 < c0 := hphalf.trans hpc0
  have hc0pos : 0 < c0 := lt_trans (by norm_num) hc0
  intro eta heta
  let tau : ℝ := eta / 8
  have htau : 0 < tau := by dsimp [tau]; positivity
  let C : ℝ := 2 * T.epsilon⁻¹ + 8 * standardSpherePathCeiling
  have hC : 0 < C := by
    have heps := inv_pos.mpr T.epsilon_pos
    have hL := standardSpherePathCeiling_pos
    dsimp [C]
    positivity
  let sigma : ℝ := tau / C
  have hsigma : 0 < sigma := div_pos htau hC
  obtain ⟨d, hd, hd1, hgood⟩ := exists_selected_chain_tail_with_scale_lt
    T A D hR hratio hdiverge hc0 hc01 hsigma
  let I : Type := {i : ℤ // i ∈ T.chain.shape.active ∧
    (T.chain.neck i).carrier ⊆ A.tail true c0 ∧ (T.chain.neck i).scale < sigma}
  obtain ⟨y0, hy0⟩ := A.tail_nonempty true (lt_trans (by norm_num) hd) hd1
  have hy0read := (A.mem_tail_iff_m28 true (lt_trans (by norm_num) hd) hd1).mp hy0
  obtain ⟨i0, hi0⟩ := mem_iUnion.mp (T.carrier_eq_chain_union ▸ hy0read.1)
  let j0 : I := ⟨i0.1, i0.2, hgood i0.1 i0.2 y0 hi0 hy0read.2⟩
  have hNU (i : I) : (T.chain.neck i.1).carrier ⊆ (U : Set M) := by
    intro z hz
    rw [hU]
    have hzread := (A.mem_tail_iff_m28 true hc0pos hc01).mp (i.property.2.1 hz)
    exact (A.mem_tail_iff_m28 true (by norm_num) (by norm_num)).mpr
      ⟨hzread.1, hc0.le.trans_lt hzread.2⟩
  let S (i : I) : Set U := (Subtype.val : U → M) ⁻¹' (T.chain.neck i.1).central_sphere
  let center (i : I) : U := ⟨(T.chain.neck i.1).center,
    hNU i ((T.chain.neck i.1).central_sphere_subset
      (T.chain.neck i.1).center_on_central_sphere)⟩
  have hcenter (i : I) : center i ∈ S i := (T.chain.neck i.1).center_on_central_sphere
  have hSnonempty (i : I) : (S i).Nonempty := ⟨center i, hcenter i⟩
  have hScompact (i : I) : IsCompact (S i) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage'
      (T.chain.neck i.1).isCompact_central_sphere
      (fun z hz => ⟨⟨z, hNU i ((T.chain.neck i.1).central_sphere_subset hz)⟩, rfl⟩)
  have hcostpos (i : I) : 0 < C * (T.chain.neck i.1).scale :=
    mul_pos hC (T.chain.neck i.1).scale_pos
  have hcostsmall (i : I) : C * (T.chain.neck i.1).scale < tau := by
    calc
      _ < C * sigma := mul_lt_mul_of_pos_left i.property.2.2 hC
      _ = tau := by dsimp [sigma]; field_simp [hC.ne']
  have hneckdist (i : I) {q z : U} (hq : (q : M) ∈ (T.chain.neck i.1).carrier)
      (hz : z ∈ S i) : dist q z ≤ C * (T.chain.neck i.1).scale := by
    apply (ENNReal.ofReal_le_ofReal_iff (hcostpos i).le).mp
    rw [← hed]
    have h := intrinsicOpenMetric_edist_neck_to_sphere_le
      (T.chain.neck i.1) U (hNU i) hq hz
    simpa only [T.chain.epsilon_eq i.1 i.property.1] using h
  let delta (i : I) : ℝ := Metric.infDist p (S i)
  have hdeltaNonneg (i : I) : 0 ≤ delta i := Metric.infDist_nonneg
  have hbounded : BddAbove (range delta) := by
    refine ⟨B, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (Metric.infDist_le_dist_of_mem (hcenter i)).trans (hdistBound p (center i))
  let ell : ℝ := sSup (range delta)
  have hdeltaSup (i : I) : delta i ≤ ell := le_csSup hbounded (mem_range_self i)
  obtain ⟨v, hv, hnear⟩ := exists_lt_of_lt_csSup
    (show (range delta).Nonempty from ⟨delta j0, mem_range_self j0⟩)
    (show ell - tau < sSup (range delta) from sub_lt_self ell htau)
  obtain ⟨j, rfl⟩ := hv
  let V : TopologicalSpace.Opens M := ⟨T.carrier, T.carrier_open⟩
  obtain ⟨phi, a0, b0, _ha0, _ha0half, hb0half, hb01, hzero, hread, hside⟩ :=
    exists_fixed_positive_side_above_cylinder_level (V := V) A (T.chain.neck j.1)
      hc0 hc01 j.property.2.1 ((T.central_sphere_isotopy j.1 j.property.1).trans hA.symm)
  let f : M → ℝ := ambientCylinderSignedHeight phi
  have hfp : f p < 0 := by
    apply lt_of_not_ge
    intro hp
    exact (not_le_of_gt hpc0) (hside p (hUV p.property) hp)
  have hfhigh (q : U) (hq : b0 < (A.inverse q).2) : 0 < f q := by
    rw [show f q = (A.inverse q).2 - 1 / 2 from
      hread q (hUV q.property) (Or.inr hq)]
    exact sub_pos.mpr (hb0half.trans hq)
  have hupper (q : U) (hq : d < (A.inverse q).2) : dist p q < ell + tau := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (T.carrier_eq_chain_union ▸ hUV q.property)
    let iq : I := ⟨i.1, i.2, hgood i.1 i.2 q hi hq⟩
    obtain ⟨z, hz, hdelta⟩ := (hScompact iq).exists_infDist_eq_dist (hSnonempty iq) p
    change delta iq = dist p z at hdelta
    have hqz : dist q z < tau := (hneckdist iq hi hz).trans_lt (hcostsmall iq)
    calc
      dist p q ≤ dist p z + dist z q := dist_triangle p z q
      _ = delta iq + dist q z := by rw [← hdelta, dist_comm z q]
      _ < ell + tau := add_lt_add_of_le_of_lt (hdeltaSup iq) hqz
  have hradial (q : U) (hq : max d b0 < (A.inverse q).2) :
      dist q (center j) < 3 * tau := by
    have hqd : d < (A.inverse q).2 := (le_max_left _ _).trans_lt hq
    have hqb : b0 < (A.inverse q).2 := (le_max_right _ _).trans_lt hq
    have hcross : ∀ gamma : ℝ → U, gamma 0 = q → gamma 1 = p →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc (0 : ℝ) 1) →
          ∃ t ∈ Icc (0 : ℝ) 1, gamma t ∈ S j := by
      intro gamma h0 h1 hgamma
      have hnegativeZero : ∀ x ∈ (V : Set M), -f x = 0 ↔
          x ∈ (T.chain.neck j.1).central_sphere := by
        intro x hx
        rw [neg_eq_zero]
        exact hzero x hx
      obtain ⟨t, ht, hts⟩ := exists_sphere_crossing_of_signed_height
        ((continuousOn_ambientCylinderSignedHeight phi).neg) hnegativeZero zero_le_one
        (continuous_subtype_val.comp_continuousOn hgamma.continuousOn)
        (fun t (_ : t ∈ Icc (0 : ℝ) 1) => hUV (gamma t).property)
        (by simpa only [Function.comp_apply, Pi.neg_apply, f, h0] using
          neg_neg_of_pos (hfhigh q hqb))
        (by simpa only [Function.comp_apply, Pi.neg_apply, f, h1] using neg_pos.mpr hfp)
      exact ⟨t, ⟨ht.1.le, ht.2.le⟩, hts⟩
    have hescape : ∀ y ∈ S j, ENNReal.ofReal (delta j) ≤ gU.edist y p := by
      intro y hy
      rw [hed, dist_comm y p]
      exact ENNReal.ofReal_le_ofReal (Metric.infDist_le_dist_of_mem hy)
    have hshort : ∀ y ∈ S j, gU.edist y (center j) ≤
        ENNReal.ofReal (C * (T.chain.neck j.1).scale) := by
      intro y hy
      rw [hed]
      exact ENNReal.ofReal_le_ofReal
        (hneckdist j ((T.chain.neck j.1).central_sphere_subset hy) (hcenter j))
    have hcrossBound := gU.edist_add_escape_le_add_shortcut_of_path_crossing
      hcross hescape hshort
    rw [hed, hed, ← ENNReal.ofReal_add dist_nonneg (hdeltaNonneg j),
      ← ENNReal.ofReal_add dist_nonneg (hcostpos j).le] at hcrossBound
    have hreal := (ENNReal.ofReal_le_ofReal_iff
      (add_nonneg dist_nonneg (hcostpos j).le)).mp hcrossBound
    have hup := hupper q hqd
    rw [dist_comm q p] at hreal
    linarith [hcostsmall j]
  refine ⟨max d b0, lt_max_of_lt_left hd, max_lt hd1 hb01, ?_⟩
  intro q r hq hr
  have hdist : dist q r < eta := by
    have hqrad := hradial q hq
    have hrrad := hradial r hr
    have htriangle := dist_triangle_right q r (center j)
    dsimp [tau] at hqrad hrrad
    linarith
  rw [← intrinsicOpenMetricSpace_edist g U hfinite q r, edist_dist]
  exact (ENNReal.ofReal_lt_ofReal_iff heta).mpr hdist

end PoincareConjecture.M28
