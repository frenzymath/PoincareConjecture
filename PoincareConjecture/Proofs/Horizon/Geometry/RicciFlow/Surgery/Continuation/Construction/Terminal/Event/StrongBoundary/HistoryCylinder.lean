import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.History.Cylinders.ToSurgery

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M33RegularHistoryRealization

variable {F : SurgeryFlowData.{u}} {G : GeneralizedRicciFlowData.{u}}
  (h : M33RegularHistoryRealization G F) (W : M33RegularHistoryWindow F)
  (hInterval : G.interval = W.interval)
  {C : GeneralizedSliceCarrier.{u}} {a q : ℝ} {J : Set ℝ} {U : Set C.carrier}
  (d : GeneralizedFlowCylinder G C a q J U) (hJ : J.OrdConnected) (hJo : IsOpen J)
  (htime : ∀ s ∈ J, a + s / q ∈ G.interval)

include hJo in
theorem openCylinder_retained (s : ℝ) (hs : s ∈ J)
    (hT : a + s / q ∈ F.surgery_times) [Nonempty (F.slice (a + s / q)).carrier]
    (x : C.carrier) (hx : x ∈ U) :
    h.forward (a + s / q) (htime s hs) (d.forward s hs x) ∈
      interior (F.event (a + s / q) hT).retained_post := by
  obtain ⟨b, y, r, hr, hworld⟩ := d.vertical_compatibility s hs x hx
  obtain ⟨hb, hby⟩ := hworld s hs (by simpa using hr)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hJo s hs
  obtain ⟨t, hlow, hts⟩ := exists_between (show s - min r ε < s by linarith [lt_min hr hε])
  have hdist : |t - s| < min r ε := by
    rw [abs_of_neg (sub_neg.mpr hts)]
    linarith
  have ht : t ∈ J := hball (by
    simpa only [Metric.mem_ball, Real.dist_eq] using hdist.trans_le (min_le_right _ _))
  obtain ⟨htb, _⟩ := hworld t ht (hdist.trans_le (min_le_left _ _))
  rw [hby]
  apply h.retained_at_surgery b (a + s / q) hb hT
  exact ⟨a + t / q, htb, by linarith [(div_lt_div_iff_of_pos_right d.scale_pos).mpr hts]⟩

def toSurgeryOpenCylinder : SurgeryFlowCylinder F C a q J U where
  scale_pos := d.scale_pos
  interval_connected := hJ
  time_subset := by
    rintro _ ⟨s, hs, rfl⟩
    exact h.time_subset (htime s hs)
  forward s hs := h.forward (a + s / q) (htime s hs) ∘ d.forward s hs
  inverse s hs := d.inverse s hs ∘ h.inverse (a + s / q) (htime s hs)
  forward_smooth s hs := (h.forward_smooth _ _).comp_contMDiffOn (d.forward_smooth s hs)
  inverse_smooth s hs := by
    apply (d.inverse_smooth s hs).comp ((h.inverse_smooth _ _).mono ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact mem_range_self _
    · rintro _ ⟨x, hx, rfl⟩
      change h.inverse (a + s / q) (htime s hs)
        (h.forward (a + s / q) (htime s hs) (d.forward s hs x)) ∈ d.forward s hs '' U
      rw [h.left_inverse]
      exact mem_image_of_mem _ hx
  left_inverse s hs x hx := by
    dsimp only [Function.comp_apply]
    rw [h.left_inverse, d.left_inverse s hs hx]
  right_inverse s hs y hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    dsimp only [Function.comp_apply]
    rw [h.left_inverse, d.left_inverse s hs hx]
  slab_compatibility s t hst htime' hfree r hr z hz hr' hz' x hx :=
    h.cylinder_slab_compatibility d hJ htime s t hst htime' hfree r hr z hz hr' hz' x hx
  retained_at_surgery s hs hT _ _ := by
    rintro _ ⟨x, hx, rfl⟩
    exact h.openCylinder_retained d hJo htime s hs hT x hx
  pre_retained_at_surgery s hs hT _ t ht ht' x hx :=
    (h.cylinder_event_coordinates W hInterval d hJ htime s hs hT t ht ht' x hx).1
  surgery_compatibility s hs hT _ t ht ht' x hx :=
    (h.cylinder_event_coordinates W hInterval d hJ htime s hs hT t ht ht' x hx).2

theorem toSurgeryOpenCylinder_pullbackInner (hU : IsOpen U)
    (s : ℝ) (hs : s ∈ J) (x : C.carrier) (hx : x ∈ U)
    (v w : TangentSpace (𝓡 3) x) :
    (h.toSurgeryOpenCylinder W hInterval d hJ hJo htime).pullbackInner s hs x v w =
      d.pullbackInner s hs x v w := by
  have hd := ((d.forward_smooth s hs).contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp)
  have hh := (h.forward_smooth (a + s / q) (htime s hs)).mdifferentiable (by simp) (d.forward s hs x)
  change q * (F.metric (a + s / q)).inner _
    (mfderiv (𝓡 3) (𝓡 3) (h.forward _ _ ∘ d.forward s hs) x v)
    (mfderiv (𝓡 3) (𝓡 3) (h.forward _ _ ∘ d.forward s hs) x w) = _
  rw [mfderiv_comp x hh hd]
  exact congrArg (q * ·) (h.metric_pullback (a + s / q) (htime s hs)
    (d.forward s hs x) (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x v)
      (mfderiv (𝓡 3) (𝓡 3) (d.forward s hs) x w))

end PoincareConjecture.M33RegularHistoryRealization
