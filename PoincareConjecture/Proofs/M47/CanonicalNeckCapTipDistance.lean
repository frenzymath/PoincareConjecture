import PoincareConjecture.Proofs.M47.CanonicalNeckCapInverseDistance
import PoincareConjecture.Proofs.M47.CanonicalNeckCapBirthMetric
import PoincareConjecture.Proofs.M34.Standard.CapMetricScalingGeometry
import PoincareConjecture.Proofs.M34.Standard.NonnegativeRicciMetric
import PoincareConjecture.Proofs.M04.PointwiseFlatness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.TangentBound
import PoincareConjecture.Definitions.M34StandardCapExistence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open M46



theorem cap_birth_tip_distance_near_one
    {F : SurgeryFlowData.{u}} {t : ℝ} {hT : t ∈ F.surgery_times}
    [Nonempty (F.slice t).carrier] {i : Fin (F.event t hT).cap_count}
    {S : MaximalStandardCapFlow F.standard_initial} {A eta : ℝ}
    (hA : 0 < A) {J : Set ℝ}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
      ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J)
    (hbase : ∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
      HEq (e.forward 0 hzero y) y)
    (hh : 0 < F.parameters.h t) (heta : 0 < eta) (hetaSmall : eta ≤ 1 / 1000)
    {z : StandardCapSpace} (hz : z ∈ F.standard_initial.metric.ball 0 A) :
    (F.standard_initial.metric.edist 0 z).toReal ≤
      (101 / 100 : ℝ) * (F.parameters.h t)⁻¹ *
        ((F.metric t).edist ((F.event t hT).caps i).tip (initial.chart z)).toReal := by
  let Q := (F.parameters.h t)⁻¹ ^ 2
  have hQ : 0 < Q := sq_pos_of_pos (inv_pos.mpr hh)
  let gQ : RiemannianMetric 3 (F.slice t).carrier := M13.scaleSmoothMetric (F.metric t) Q hQ
  let q := capInitialPartialDiffeomorph initial
  have hsqrt : Real.sqrt Q = (F.parameters.h t)⁻¹ := Real.sqrt_sq (inv_pos.mpr hh).le
  have hball : gQ.ball (q 0) A =
      (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t) := by
    have hrad : Real.sqrt Q * (A * F.parameters.h t) = A := by
      rw [hsqrt]
      field_simp
    have h := M13.scaleSmoothMetric_ball (F.metric t) Q hQ (q 0)
      (A * F.parameters.h t)
    rw [hrad] at h
    exact h.trans (congrArg (fun x => (F.metric t).ball x (A * F.parameters.h t))
      initial.tip_eq)
  have hsource0 : (0 : StandardCapSpace) ∈ q.source := by
    change F.standard_initial.metric.edist 0 0 < ENNReal.ofReal A
    rw [M36.metric_edist_self]
    exact ENNReal.ofReal_pos.mpr hA
  have hcover : gQ.ball (q 0) A ⊆ q.target := by
    rw [hball]
    change (F.metric t).ball _ _ ⊆ initial.chart '' F.standard_initial.metric.ball 0 A
    rw [comparison.choose_spec.2.2.2.1]
  have himage : q z ∈ gQ.ball (q 0) A := by
    rw [hball, ← comparison.choose_spec.2.2.2.1]
    exact mem_image_of_mem initial.chart hz
  have hbound (x : StandardCapSpace) (hx : x ∈ q.source)
      (v : TangentSpace (𝓡 3) x) :
      F.standard_initial.metric.tangentNorm x v ≤ (101 / 100 : ℝ) *
        gQ.tangentNorm (q x) (mfderiv (𝓡 3) (𝓡 3) q x v) :=
    (cap_birth_tangent_bounds_near_one e initial comparison hzero hbase hh heta hetaSmall
      hx v).2
  have hd := PoincareConjecture.M47.cap_inverse_toReal_edist_le
    F.standard_initial.metric gQ q.toOpenPartialHomeomorph
    (q.contMDiffOn_toFun.of_le (by simp)) (q.contMDiffOn_invFun.of_le (by simp))
    hsource0 (by norm_num : (0 : ℝ) < 101 / 100) hcover hbound hz himage
  have hscale := M13.homothety_edist (F.metric t) gQ
    (Diffeomorph.refl (𝓡 3) (F.slice t).carrier ∞) Q hQ
    (M13.identity_metricHomothety (F.metric t) Q hQ) (q 0) (q z)
  change gQ.edist (q.toOpenPartialHomeomorph 0)
      (q.toOpenPartialHomeomorph z) = _ at hscale
  rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.sqrt_nonneg _), hsqrt] at hd
  have htip : q 0 = ((F.event t hT).caps i).tip := initial.tip_eq
  rw [htip] at hd
  have hqz : q z = initial.chart z := rfl
  rw [hqz] at hd
  simpa only [mul_assoc] using hd



theorem standard_flow_tip_distance_le_initial
    {g0 : StandardInitialMetric} (E : RepairedStandardCapExistenceData g0)
    {s : ℝ} (hs : s ∈ Ico 0 E.flow.base.lifetime) (z : StandardCapSpace) :
    ((E.flow.metric s).edist 0 z).toReal ≤ (g0.metric.edist 0 z).toReal := by
  have hsub : Icc 0 s ⊆ Ico 0 E.flow.base.lifetime :=
    fun _ ht => ⟨ht.1, ht.2.trans_lt hs.2⟩
  have hmetric (x : StandardCapSpace) (v : TangentSpace (𝓡 3) x) :
      (E.flow.metric s).inner x v v ≤ (E.flow.metric 0).inner x v v := by
    have hmono := E.flow.base.flow.inner_self_antitoneOn_of_nonnegative_ricci
      (convex_Icc (0 : ℝ) s) hsub x v (fun t ht =>
        M04.nonneg_ricci_of_nonnegativeSectionalAt (E.flow.connection t) x
          (E.nonnegative_sectional t (hsub ht) x) v)
    exact hmono ⟨le_rfl, hs.1⟩ ⟨hs.1, le_rfl⟩ hs.1
  have hdist := (E.flow.metric 0).edist_le_mul_of_inner_mfderiv_le
    (E.flow.metric s) contMDiff_id zero_lt_one (fun x v => by
      simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply, one_pow, one_mul]
        using hmetric x v) 0 z
  simp only [id_eq, ENNReal.ofReal_one, one_mul] at hdist
  have hinitial : E.flow.metric 0 = g0.metric := E.flow.base.initial_metric
  rw [hinitial] at hdist
  exact ENNReal.toReal_mono (g0.metric.edist_ne_top 0 z) hdist

end PoincareConjecture.Proofs.M47
