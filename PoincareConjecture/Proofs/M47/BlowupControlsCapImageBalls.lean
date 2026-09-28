import PoincareConjecture.Proofs.M47.BlowupControlsCapImageTail
import PoincareConjecture.Proofs.M47.CanonicalCoreBallContainment









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal

universe u v

namespace PoincareConjecture.M47

variable {M : Type u} {X : Type v} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M] [T3Space M] [T3Space X]



theorem cap_image_recut_compact_closure
    {g : RiemannianMetric 3 M} (N : CapCertificate g)
    (e : OpenPartialHomeomorph M X) (hsource : N.carrier ⊆ e.source)
    {b : ℝ} (hb0 : -N.epsilon⁻¹ < b) (hb : b < N.epsilon⁻¹) :
    IsCompact (closure (e '' N.recutCarrier b)) ∧
      closure (e '' N.recutCarrier b) ⊆ e '' N.carrier := by
  let : T25Space X := T3Space.t25Space
  let : T2Space X := T25Space.t2Space
  have hcapture := N.recutCarrier_compact_closure hb0 hb
  have hsource' := hcapture.2.trans hsource
  rw [← e.image_closure_eq_of_isCompact hcapture.1 hsource']
  exact ⟨hcapture.1.image_of_continuousOn (e.continuousOn.mono hsource'),
    image_mono hcapture.2⟩

variable [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] [IsManifold (𝓡 3) ∞ X]
  [MeasurableSpace X] [BorelSpace X]



theorem scalar_normalized_ball_subset_cap_image_recut
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}
    (N : CapCertificate g) (E : EpsilonNeck h) (D : LeviCivitaData h)
    (e : OpenPartialHomeomorph M X) (hsource : N.carrier ⊆ e.source)
    (hconnection : E.connection = D)
    (hcarrier : E.carrier = e '' N.end_neck.carrier)
    (hinverse : E.coordinate_inverse = N.end_neck.coordinate_inverse ∘ e.symm)
    {y : X} (hy : y ∈ e '' N.closed_core) {r : ℝ} (hr : 0 < r)
    (hbounded : BddAbove (D.scalarCurvature '' h.ball y r))
    (hnormal : scalarCurvatureSupOn h D (h.ball y r) = r⁻¹ ^ 2) :
    h.ball y r ⊆ e '' N.recutCarrier (N.epsilon⁻¹ / 2) := by
  let b := N.epsilon⁻¹ / 2
  have hinv : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hlarge : 200 ≤ N.epsilon⁻¹ := by
    have h := inv_anti₀ N.epsilon_pos N.epsilon_le_threshold
    norm_num at h
    exact h
  have hb16 : 16 ≤ b := by dsimp only [b]; linarith
  have hb0 : -N.epsilon⁻¹ < b := by dsimp only [b]; linarith
  have hb : b < N.epsilon⁻¹ := by dsimp only [b]; linarith
  have hcapture := cap_image_recut_compact_closure N e hsource hb0 hb
  have hopen : IsOpen (e '' N.recutCarrier b) :=
    e.isOpen_image_of_subset_source (N.recutCarrier_isOpen hb0 hb)
      ((N.recutCarrier_subset_carrier b).trans hsource)
  intro z hz
  by_contra hzout
  obtain ⟨gamma, hgamma0, hgamma1, hgamma, hlength, _⟩ :=
    h.exists_short_path_in_ball y z hz
  obtain ⟨t, ht, hfrontier, _, hbefore⟩ := hgamma.continuousOn.exists_first_frontier_time
    zero_le_one hopen (hgamma0.symm ▸ image_mono (fun _ hx => Or.inl hx) hy)
    (hgamma1.symm ▸ hzout)
  have hgamma' := hgamma.mono (Icc_subset_Icc_right ht.2)
  obtain ⟨a, ha, _, htail, hcenter⟩ := exists_cap_image_exit_neck_tail N E e hsource
    hcarrier hinverse hb16 hb ht.1.le hgamma'
    (fun s hs => hcapture.2 (hbefore hs)) (hgamma0.symm ▸ hy) hfrontier
  have hprefix : h.edist y (gamma a) ≤ h.pathELength gamma 0 a := by
    rw [← hgamma0]
    exact M36.metric_edist_le_pathELength h ha.1
      (hgamma.mono (Icc_subset_Icc_right (ha.2.le.trans ht.2)))
  have hcenterBall : E.center ∈ h.ball y r := by
    change h.edist y E.center < ENNReal.ofReal r
    calc
      _ ≤ h.edist y (gamma a) + h.edist (gamma a) E.center :=
        M36.metric_edist_triangle h y (gamma a) E.center
      _ ≤ h.pathELength gamma 0 a + h.pathELength gamma a t :=
        add_le_add hprefix hcenter
      _ = h.pathELength gamma 0 t := M36.metric_pathELength_add h gamma ha.1 ha.2.le
      _ ≤ h.pathELength gamma 0 1 := M36.metric_pathELength_mono h gamma le_rfl ht.2
      _ < _ := hlength
  have hR : D.scalarCurvature E.center ≤ r⁻¹ ^ 2 := by
    rw [← hnormal]
    have h := le_csSup hbounded (mem_image_of_mem D.scalarCurvature hcenterBall)
    simpa only [scalarCurvatureSupOn, image_eq_range] using h
  have hscale : E.scale⁻¹ ^ 2 = D.scalarCurvature E.center := by
    rw [← hconnection, E.scale_eq_scalar, inv_pow,
      ← Real.rpow_mul_natCast E.scalar_center_pos.le (-1 / 2) 2]
    norm_num [Real.rpow_neg_one]
  have hrscale : r ≤ E.scale := by
    have hsq : E.scale⁻¹ ^ 2 ≤ r⁻¹ ^ 2 := hscale.trans_le hR
    have hi := (sq_le_sq₀ (inv_nonneg.mpr E.scale_pos.le) (inv_nonneg.mpr hr.le)).mp hsq
    exact (inv_le_inv₀ E.scale_pos hr).mp hi
  have hcontradiction : ENNReal.ofReal r ≤ h.pathELength gamma 0 1 := by
    calc
      _ ≤ ENNReal.ofReal E.scale := ENNReal.ofReal_le_ofReal hrscale
      _ ≤ ENNReal.ofReal (8 * E.scale) := ENNReal.ofReal_le_ofReal (by linarith [E.scale_pos])
      _ ≤ h.pathELength gamma a t := htail
      _ ≤ h.pathELength gamma 0 1 := M36.metric_pathELength_mono h gamma ha.1 ht.2
  exact not_lt_of_ge hcontradiction hlength



theorem scalar_normalized_cap_image_ball_captured
    {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}
    (N : CapCertificate g) (E : EpsilonNeck h) (D : LeviCivitaData h)
    (e : OpenPartialHomeomorph M X) (hsource : N.carrier ⊆ e.source)
    (hconnection : E.connection = D)
    (hcarrier : E.carrier = e '' N.end_neck.carrier)
    (hinverse : E.coordinate_inverse = N.end_neck.coordinate_inverse ∘ e.symm)
    {y : X} (hy : y ∈ e '' N.closed_core) {r : ℝ} (hr : 0 < r)
    (hbounded : BddAbove (D.scalarCurvature '' h.ball y r))
    (hnormal : scalarCurvatureSupOn h D (h.ball y r) = r⁻¹ ^ 2) :
    IsCompact (closure (h.ball y r)) ∧ closure (h.ball y r) ⊆ e '' N.carrier := by
  have hinv : 0 < N.epsilon⁻¹ := inv_pos.mpr N.epsilon_pos
  have hcapture := cap_image_recut_compact_closure N e hsource
    (b := N.epsilon⁻¹ / 2) (by linarith) (by linarith)
  have hball := closure_mono (scalar_normalized_ball_subset_cap_image_recut
    N E D e hsource hconnection hcarrier hinverse hy hr hbounded hnormal)
  exact ⟨hcapture.1.of_isClosed_subset isClosed_closure hball, hball.trans hcapture.2⟩

end PoincareConjecture.M47
