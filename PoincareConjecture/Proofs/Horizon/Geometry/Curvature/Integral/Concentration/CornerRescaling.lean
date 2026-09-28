import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.CornerModels
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Integral.Concentration.WeightedFiberGeometry

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Topology MeasureTheory Function
open Poincare.GromovHausdorff
open Poincare.Geometry.Manifold.RegularFiber
open scoped Manifold ContDiff Bundle
namespace PoincareConjecture

private theorem rescaled_edist_le_iff
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {a : ℝ} (ha : 0 < a) (p x : M) (r : ℝ) :
    (rescaledMetric g a ha).edist p x ≤ ENNReal.ofReal (Real.sqrt a*r) ↔
      g.edist p x ≤ ENNReal.ofReal r := by
  rw [rescaledMetric_edist, ENNReal.ofReal_mul (Real.sqrt_nonneg a)]
  rw [mul_comm (ENNReal.ofReal (Real.sqrt a)) (g.edist p x),
    mul_comm (ENNReal.ofReal (Real.sqrt a)) (ENNReal.ofReal r)]
  exact ENNReal.mul_le_mul_iff_left (by positivity) ENNReal.ofReal_ne_top

theorem exists_rescaled_pointedCornerModel
    {m k : ℕ} {δ H : ℝ} (hm : 2 ≤ m) (hH : 0 ≤ H)
    (A : PointedCornerModel m k δ H)
    (q : openFiber A.joint A.domain A.value) {a : ℝ} (ha : 1 ≤ a)
    (hbuffer : ∀ y : A.carrier,
      A.metric.edist (openFiberIncl A.joint A.domain A.value q) y ≤
        ENNReal.ofReal (2 / Real.sqrt a) → y ∈ A.domain) :
    letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
      ⟨finrank_euclideanSpace_fin⟩
    letI := openFiberChartedSpace (m := m) A.joint_smooth A.domain A.regular A.value
    letI := isManifold_openFiber (m := m) A.joint_smooth A.domain A.regular A.value
    ∃ B : PointedCornerModel m k δ H,
      letI := openFiberChartedSpace (m := m) B.joint_smooth B.domain B.regular B.value
      letI := isManifold_openFiber (m := m) B.joint_smooth B.domain B.regular B.value
      ∃ eM : A.carrier ≃ₘ⟮𝓡 (m+k), 𝓡 (m+k)⟯ B.carrier,
      ∃ eL : openFiber A.joint A.domain A.value ≃ₘ⟮𝓡 m, 𝓡 m⟯
        openFiber B.joint B.domain B.value,
        (∀ (x : A.carrier) (v w : TangentSpace (𝓡 (m+k)) x),
          B.metric.inner (eM x) (mfderiv (𝓡 (m+k)) (𝓡 (m+k)) eM x v)
            (mfderiv (𝓡 (m+k)) (𝓡 (m+k)) eM x w) = a*A.metric.inner x v w) ∧
        (∀ x y, B.metric.edist (eM x) (eM y) =
          ENNReal.ofReal (Real.sqrt a)*A.metric.edist x y) ∧
        B.ambientPoint = eM (openFiberIncl A.joint A.domain A.value q) ∧
        (∀ i x, B.f i (eM x) = Real.sqrt a*A.f i x) ∧
        (∀ i x, B.h i (eM x) = Real.sqrt a*A.h i x) ∧
        B.value = Real.sqrt a • A.value ∧
        (∀ x, eM x ∈ B.domain ↔ x ∈ A.domain) ∧
        (∀ x, openFiberIncl B.joint B.domain B.value (eL x) =
          eM (openFiberIncl A.joint A.domain A.value x)) ∧
        eL q = B.point ∧
        (∀ x, B.error (eL x) = a⁻¹*A.error x) ∧
        A.metric.openFiberWeightedAmbientBallRatio A.joint_smooth A.domain A.regular
          A.value A.error (openFiberIncl A.joint A.domain A.value q)
          (1 / Real.sqrt a) (2 / Real.sqrt a) ≤ B.weightedRatio := by
  classical
  have hap : 0 < a := zero_lt_one.trans_le ha
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr hap
  have hs1 : 1 ≤ Real.sqrt a := (Real.le_sqrt (by norm_num) hap.le).2 (by simpa using ha)
  let G := rescaledMetric A.metric a hap
  let DG := rescaledMetric_connection A.metric A.connection a hap
  let fs := fun i x => Real.sqrt a*A.f i x
  let hsfun := fun i x => Real.sqrt a*A.h i x
  let Ps := fun x => Real.sqrt a • (fun x i => A.f i x) x
  let vs := Real.sqrt a • A.value
  obtain ⟨hcG,hsecG,hfs,hhs,hunit,hopp,hcross,htight,hhess,hPs,hregS,hdata⟩ :=
    A.metric.exists_scaled_openFiber_weighted_corner_geometry A.connection A.complete
      A.sectional_lower A.f A.h A.f_smooth A.h_smooth A.domain A.unit A.opposite
      A.cross A.tight A.hessian_upper A.value hm ha A.regular
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (m+k))) = m+k) :=
    ⟨finrank_euclideanSpace_fin⟩
  let := openFiberChartedSpace (m := m) (contMDiff_pi_space.mpr A.f_smooth) A.domain A.regular A.value
  let := isManifold_openFiber (m := m) (contMDiff_pi_space.mpr A.f_smooth) A.domain A.regular A.value
  let := openFiberChartedSpace (m := m) hPs A.domain hregS vs
  let := isManifold_openFiber (m := m) hPs A.domain hregS vs
  obtain ⟨e,hinc,hmetric,hdist,hballs,hbuffers,herrors⟩ := hdata
  obtain ⟨hKcont,hKnonneg,hKsec,hratio⟩ :=
    herrors A.error A.error_continuous A.error_nonneg A.error_sectional_lower
  let Knew := fun y => a⁻¹*A.error (e.symm y)
  have hHscale : H / Real.sqrt a ≤ H := div_le_self hH hs1
  have hhessH : ∀ x ∈ A.domain, ∀ i z,
      DG.hessian (fs i) x z z ≤ H*G.inner x z z ∧
      DG.hessian (hsfun i) x z z ≤ H*G.inner x z z := by
    intro x hx i z
    have hn : 0 ≤ G.inner x z z := by
      by_cases hz : z = 0
      · simp [hz]
      · exact (G.pos x z hz).le
    exact ⟨(hhess x hx i z).1.trans (mul_le_mul_of_nonneg_right hHscale hn),
      (hhess x hx i z).2.trans (mul_le_mul_of_nonneg_right hHscale hn)⟩
  have hbufferG : ∀ y : A.carrier,
      G.edist (openFiberIncl Ps A.domain vs (e q)) y ≤ ENNReal.ofReal 2 →
      y ∈ A.domain := by
    intro y hy
    rw [hinc] at hy
    apply hbuffer y
    apply (rescaled_edist_le_iff A.metric hap _ y (2 / Real.sqrt a)).mp
    simpa only [mul_div_cancel₀ _ hs.ne'] using hy
  let B : PointedCornerModel m k δ H :=
    { carrier := A.carrier
      metric := G
      connection := DG
      complete := hcG
      sectional_lower := hsecG
      f := fs
      h := hsfun
      f_smooth := hfs
      h_smooth := hhs
      domain := A.domain
      unit := hunit
      opposite := hopp
      cross := hcross
      tight := htight
      hessian_upper := hhessH
      regular := hregS
      value := vs
      point := e q
      buffer := hbufferG
      error := Knew
      error_continuous := hKcont
      error_nonneg := hKnonneg
      error_sectional_lower := hKsec }
  refine ⟨B, Diffeomorph.refl (𝓡 (m+k)) A.carrier ∞, e, ?_, ?_, ?_,
    (fun _ _ => rfl), (fun _ _ => rfl), rfl, (fun _ => Iff.rfl), hinc, rfl, ?_, ?_⟩
  · intro x v w
    change G.inner x (mfderiv (𝓡 (m+k)) (𝓡 (m+k)) id x v)
      (mfderiv (𝓡 (m+k)) (𝓡 (m+k)) id x w) = a*A.metric.inner x v w
    simp only [mfderiv_id]
    exact rescaledMetric_inner A.metric a hap x v w
  · intro x y
    exact rescaledMetric_edist A.metric a hap x y
  · exact hinc q
  · intro x
    change a⁻¹*A.error (e.symm (e x)) = a⁻¹*A.error x
    rw [e.symm_apply_apply]
  · change A.metric.openFiberWeightedAmbientBallRatio (contMDiff_pi_space.mpr A.f_smooth) A.domain A.regular
      A.value A.error (openFiberIncl (fun x i => A.f i x) A.domain A.value q)
      (1 / Real.sqrt a) (2 / Real.sqrt a) ≤
      G.openFiberWeightedAmbientBallRatio hPs A.domain hregS vs Knew
        (openFiberIncl Ps A.domain vs (e q)) 1 2
    rw [hinc]
    simpa only [mul_div_cancel₀ _ hs.ne'] using
      hratio (openFiberIncl (fun x i => A.f i x) A.domain A.value q)
        (1 / Real.sqrt a) (2 / Real.sqrt a)

end PoincareConjecture
