import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Scaling








noncomputable section

namespace PoincareConjecture.CoordinateExponential

open Set Metric Filter
open scoped ContDiff Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


structure LocalFlowData
    (B : E → E →L[ℝ] E →L[ℝ] ℝ) (U : Set E) (x : E) where
  radius : ℝ
  radius_pos : 0 < radius
  fieldRadius : ℝ
  fieldRadius_pos : 0 < fieldRadius
  field_ball_subset : ball (x, (0 : E)) fieldRadius ⊆ U ×ˢ univ
  constant : ℝ≥0
  lipschitz : LipschitzOnWith constant (coordinateGeodesicField B)
    (ball (x, 0) fieldRadius)
  flow : E × ℝ → E × E
  smooth : ContDiffOn ℝ ∞ flow (ball 0 radius ×ˢ Ioo (-radius) radius)
  initial : ∀ v ∈ ball 0 radius, flow (v, 0) = (x, v)
  hasDerivAt : ∀ v ∈ ball 0 radius, ∀ t ∈ Ioo (-radius) radius,
    HasDerivAt (fun s => flow (v, s)) (coordinateGeodesicField B (flow (v, t))) t
  stays : ∀ v ∈ ball 0 radius, ∀ t ∈ Ioo (-radius) radius,
    flow (v, t) ∈ ball (x, 0) fieldRadius

theorem exists_localFlowData [FiniteDimensional ℝ E]
    {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} (hU : IsOpen U)
    (hB : ContDiffOn ℝ ∞ B U) (hinv : ∀ x ∈ U, (B x).IsInvertible)
    (hsymm : ∀ x ∈ U, ∀ u v, B x u v = B x v u)
    {x : E} (hx : x ∈ U) : Nonempty (LocalFlowData B U x) := by
  have hfield := contDiffAt_coordinateGeodesicField
    (z := (x, (0 : E))) (hB.contDiffAt (hU.mem_nhds hx)) (hinv x hx)
  obtain ⟨K, Q, hQ, hK⟩ := (hfield.of_le (by simp : (1 : WithTop ℕ∞) ≤ ∞)).exists_lipschitzOnWith
  have hQU : Q ∩ (U ×ˢ univ) ∈ 𝓝 (x, (0 : E)) :=
    inter_mem hQ ((hU.prod isOpen_univ).mem_nhds ⟨hx, mem_univ _⟩)
  obtain ⟨R, hR, hRQ⟩ := Metric.mem_nhds_iff.mp hQU
  obtain ⟨V, δ, Φ, hV, hxV, _, hδ, hΦ, hinit, hspec⟩ :=
    exists_smooth_coordinate_geodesic_flow hU hB hinv hsymm hx (0 : E)
  let W := (V ×ˢ Ioo (-δ) δ) ∩ Φ ⁻¹' ball (x, 0) R
  have hWopen : IsOpen W := hΦ.continuousOn.isOpen_inter_preimage
    (hV.prod isOpen_Ioo) isOpen_ball
  have hWmem : ((x, (0 : E)), 0) ∈ W := by
    refine ⟨⟨hxV, ⟨by linarith, hδ⟩⟩, ?_⟩
    change Φ ((x, 0), 0) ∈ ball (x, 0) R
    rw [hinit (x, 0) hxV]
    exact mem_ball_self hR
  obtain ⟨a, ha, haW⟩ := Metric.isOpen_iff.mp hWopen _ hWmem
  have hsub : ∀ v ∈ ball (0 : E) a, ∀ t ∈ Ioo (-a) a, ((x, v), t) ∈ W := by
    intro v hv t ht
    apply haW
    simp only [mem_ball, Prod.dist_eq, dist_self, dist_zero_right, max_lt_iff]
    exact ⟨⟨ha, by simpa only [mem_ball, dist_zero_right] using hv⟩, abs_lt.mpr ht⟩
  refine ⟨{
    radius := a
    radius_pos := ha
    fieldRadius := R
    fieldRadius_pos := hR
    field_ball_subset := fun z hz => (hRQ hz).2
    constant := K
    lipschitz := hK.mono (fun z hz => (hRQ hz).1)
    flow := fun p => Φ ((x, p.1), p.2)
    smooth := ?_
    initial := ?_
    hasDerivAt := ?_
    stays := ?_ }⟩
  · exact hΦ.comp ((contDiffOn_const.prodMk contDiffOn_fst).prodMk contDiffOn_snd)
      (fun p hp => (hsub p.1 hp.1 p.2 hp.2).1)
  · intro v hv
    exact hinit (x, v) (hsub v hv 0 ⟨by linarith, ha⟩).1.1
  · intro v hv t ht
    exact (hspec (x, v) (hsub v hv t ht).1.1 t (hsub v hv t ht).1.2).2.1
  · intro v hv t ht
    exact (hsub v hv t ht).2

namespace LocalFlowData

variable {B : E → E →L[ℝ] E →L[ℝ] ℝ} {U : Set E} {x : E}
variable (D : LocalFlowData B U x)

theorem smul_mem {c : ℝ} (hc : |c| ≤ 1) {v : E}
    (hv : v ∈ ball 0 D.radius) : c • v ∈ ball 0 D.radius := by
  rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans_lt (by
    simpa only [one_mul, mem_ball, dist_zero_right] using hv)

theorem mul_mem {c t : ℝ} (hc : |c| ≤ 1)
    (ht : t ∈ Ioo (-D.radius) D.radius) : c * t ∈ Ioo (-D.radius) D.radius := by
  apply abs_lt.mp
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right hc (abs_nonneg _)).trans_lt (by
    simpa only [one_mul] using abs_lt.mpr ht)


theorem scaling {c : ℝ} (hc : |c| ≤ 1) {v : E} (hv : v ∈ ball 0 D.radius)
    {t : ℝ} (ht : t ∈ Ioo (-D.radius) D.radius) :
    D.flow (c • v, t) = velocityScale c (D.flow (v, c * t)) := by
  have hcv := D.smul_mem hc hv
  apply ODE_solution_unique_of_mem_Ioo
    (v := fun _ => coordinateGeodesicField B)
    (s := fun _ => ball (x, 0) D.fieldRadius) (K := D.constant)
    (fun _ _ => D.lipschitz)
    (show (0 : ℝ) ∈ Ioo (-D.radius) D.radius by
      constructor <;> linarith [D.radius_pos])
    (fun s hs => ⟨D.hasDerivAt (c • v) hcv s hs, D.stays (c • v) hcv s hs⟩)
    (fun s hs => ⟨hasDerivAt_velocityScale (D.hasDerivAt v hv (c * s) (D.mul_mem hc hs)),
      velocityScale_mem_ball hc (D.stays v hv (c * s) (D.mul_mem hc hs))⟩)
    ?_ ht
  rw [mul_zero, D.initial (c • v) hcv, D.initial v hv]
  rfl


theorem zero {t : ℝ} (ht : t ∈ Ioo (-D.radius) D.radius) :
    D.flow (0, t) = (x, 0) := by
  have h := D.scaling (c := 0) (by norm_num) (mem_ball_self D.radius_pos) ht
  simp only [zero_smul, zero_mul, D.initial 0 (mem_ball_self D.radius_pos)] at h
  simpa [velocityScale] using h

end LocalFlowData

end PoincareConjecture.CoordinateExponential
