import PoincareConjecture.Proofs.M47.SeedCapPhysicalDensity
import PoincareConjecture.Proofs.M47.SeedCapBirthTangent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

open M46

theorem exists_seed_cap_birth_density (g0 : StandardInitialMetric)
    {Rtip Rmax : ℝ} (htip : 0 < Rtip) (hmax : 0 < Rmax) :
    ∃ k : ℝ, 0 < k ∧
      ∀ (F : SurgeryFlowData.{u}), F.standard_initial = g0 →
      ∀ (S : MaximalStandardCapFlow F.standard_initial) (t : ℝ)
        (hT : t ∈ F.surgery_times) (_hn : Nonempty (F.slice t).carrier)
        (i : Fin (F.event t hT).cap_count) (A eta : ℝ),
        2 * Rtip + Rmax ≤ A → 0 < eta → eta ≤ 1 / 2 →
      ∀ (J : Set ℝ)
        (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J
          ((F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t)))
        (initial : SurgeryCapInitialComparison F t hT i A),
        SurgeryCapFamilyComparison F S A eta e initial.chart →
        ∀ hzero : (0 : ℝ) ∈ J,
          (∀ y ∈ (F.metric t).ball ((F.event t hT).caps i).tip (A * F.parameters.h t),
            HEq (e.forward 0 hzero y) y) →
          ∀ z ∈ (F.metric t).ball ((F.event t hT).caps i).tip (Rtip * F.parameters.h t),
            ∀ r : ℝ, 0 < r → r ≤ Rmax * F.parameters.h t →
              ENNReal.ofReal (k * r ^ 3) ≤
                calibratedMetricVolume (F.metric t) ((F.metric t).ball z r) := by
  obtain ⟨k, hk, hdensity⟩ := exists_seed_cap_physical_density g0 htip hmax
  refine ⟨k, hk, ?_⟩
  intro F hinitial S t hT hn i A eta hA heta hetahalf J e initial comparison hzero hbase
    z hz r hr hrmax
  have hh : 0 < F.parameters.h t :=
    F.parameters.h_pos t (F.time_domain_nonnegative (F.surgery_times_subset hT))
  let Q := (F.parameters.h t)⁻¹ ^ 2
  have hQ : 0 < Q := sq_pos_of_pos (inv_pos.mpr hh)
  let q := capInitialPartialDiffeomorph initial
  let gQ : RiemannianMetric 3 (F.slice t).carrier := M13.scaleSmoothMetric (F.metric t) Q hQ
  have hsqrt : Real.sqrt Q = (F.parameters.h t)⁻¹ := Real.sqrt_sq (inv_pos.mpr hh).le
  have hball : gQ.ball (q 0) Rtip =
      (F.metric t).ball ((F.event t hT).caps i).tip (Rtip * F.parameters.h t) := by
    have hrad : Real.sqrt Q * (Rtip * F.parameters.h t) = Rtip := by
      rw [hsqrt]
      field_simp
    have h := M13.scaleSmoothMetric_ball (F.metric t) Q hQ (q 0)
      (Rtip * F.parameters.h t)
    rw [hrad] at h
    exact h.trans (congrArg (fun x => (F.metric t).ball x (Rtip * F.parameters.h t)) initial.tip_eq)
  have hsource : q.source = g0.metric.ball 0 A := by
    change F.standard_initial.metric.ball 0 A = _
    rw [hinitial]
  have htangent (x : StandardCapSpace) (hx : x ∈ q.source)
      (v : TangentSpace (𝓡 3) x) :
      gQ.tangentNorm (q x) (mfderiv (𝓡 3) (𝓡 3) q x v) ≤
          2 * g0.metric.tangentNorm x v ∧
        g0.metric.tangentNorm x v ≤
          2 * gQ.tangentNorm (q x) (mfderiv (𝓡 3) (𝓡 3) q x v) := by
    rw [← hinitial]
    exact seed_cap_birth_tangent_bounds e initial comparison hzero hbase hh heta hetahalf hx v
  have hcover : gQ.ball (q 0) Rtip ⊆ q.target := by
    rw [hball]
    change (F.metric t).ball _ _ ⊆ initial.chart '' F.standard_initial.metric.ball 0 A
    rw [comparison.choose_spec.2.2.2.1]
    intro y hy
    exact hy.trans_le (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (by linarith only [hA, htip, hmax]) hh.le))
  have hmaxr : Real.sqrt Q * r ≤ Rmax := by
    rw [hsqrt]
    have h := mul_le_mul_of_nonneg_left hrmax (inv_pos.mpr hh).le
    have hc : (F.parameters.h t)⁻¹ * (Rmax * F.parameters.h t) = Rmax := by field_simp
    rwa [hc] at h
  exact hdensity (F.slice t).carrier (F.metric t) Q hQ q.toOpenPartialHomeomorph
    (q.contMDiffOn_toFun.of_le (by simp)) (q.contMDiffOn_invFun.of_le (by simp))
    A hA hsource (fun x hx v => (htangent x hx v).1)
    (fun x hx v => (htangent x hx v).2) hcover z (hball.symm ▸ hz) r hr hmaxr

end PoincareConjecture.Proofs.M47
