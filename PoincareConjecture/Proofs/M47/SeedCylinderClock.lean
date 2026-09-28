import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47

variable {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
  {origin scale : ℝ} {I : Set ℝ} {U : Set C.carrier}
  (e : SurgeryFlowCylinder F C origin scale I U)

private noncomputable def clockForward (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) : C.carrier → (F.slice t).carrier := by
  subst t
  exact e.forward s hs

private noncomputable def clockInverse (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) : (F.slice t).carrier → C.carrier := by
  subst t
  exact e.inverse s hs

private theorem clockForward_smooth (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (clockForward e s hs t h) U := by
  subst t
  exact e.forward_smooth s hs

private theorem clockInverse_smooth (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) :
    ContMDiffOn (𝓡 3) (𝓡 3) ∞ (clockInverse e s hs t h)
      (clockForward e s hs t h '' U) := by
  subst t
  exact e.inverse_smooth s hs

private theorem clock_left_inverse (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) :
    LeftInvOn (clockInverse e s hs t h) (clockForward e s hs t h) U := by
  subst t
  exact e.left_inverse s hs

private theorem clock_right_inverse (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) :
    LeftInvOn (clockForward e s hs t h) (clockInverse e s hs t h)
      (clockForward e s hs t h '' U) := by
  subst t
  exact e.right_inverse s hs

private theorem clockForward_heq (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) (x : C.carrier) :
    HEq (clockForward e s hs t h x) (e.forward s hs x) := by
  subst t
  rfl

private theorem clockForward_curvature (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) (x : C.carrier) :
    (F.connection t).curvatureTensorNorm (clockForward e s hs t h x) =
      (F.connection (origin + s / scale)).curvatureTensorNorm (e.forward s hs x) := by
  subst t
  rfl

private theorem clock_slab (a b : ℝ) (hab : a < b)
    (hJ : Icc a b ⊆ F.time_domain) (hS : Disjoint F.surgery_times (Ioc a b))
    (s : ℝ) (hs : s ∈ I) (t : ℝ) (ht : t ∈ I)
    (s' t' : ℝ) (hsclock : s' = origin + s / scale)
    (htclock : t' = origin + t / scale)
    (hs' : s' ∈ Icc a b) (ht' : t' ∈ Icc a b) (x : C.carrier) (hx : x ∈ U) :
    (F.regular_slabs a b hab hJ hS).transport ⟨s', hs'⟩ ⟨t', ht'⟩
      (clockForward e s hs s' hsclock x) = clockForward e t ht t' htclock x := by
  subst s'
  subst t'
  exact e.slab_compatibility a b hab hJ hS s hs t ht hs' ht' x hx

private theorem clock_retained (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (h : t = origin + s / scale) (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (hearlier : ∃ s' ∈ I, s' < s) :
    clockForward e s hs t h '' U ⊆ interior (F.event t hT).retained_post := by
  subst t
  exact e.retained_at_surgery s hs hT hearlier

private theorem clock_pre_retained (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (ht : t ∈ I) (s' t' : ℝ)
    (hsclock : s' = origin + s / scale) (htclock : t' = origin + t / scale)
    (hT : s' ∈ F.surgery_times) [Nonempty (F.slice s').carrier]
    (ht' : t' ∈ Ico (F.event s' hT).tMinus s') (x : C.carrier) (hx : x ∈ U) :
    ((F.event s' hT).pre_identify ⟨t', ht'⟩).symm
      (clockForward e t ht t' htclock x) ∈ interior (F.event s' hT).retained_pre := by
  subst s'
  subst t'
  exact e.pre_retained_at_surgery s hs hT t ht ht' x hx

private theorem clock_surgery (s : ℝ) (hs : s ∈ I)
    (t : ℝ) (ht : t ∈ I) (s' t' : ℝ)
    (hsclock : s' = origin + s / scale) (htclock : t' = origin + t / scale)
    (hT : s' ∈ F.surgery_times) [Nonempty (F.slice s').carrier]
    (ht' : t' ∈ Ico (F.event s' hT).tMinus s') (x : C.carrier) (hx : x ∈ U) :
    (F.event s' hT).retention.map
      (((F.event s' hT).pre_identify ⟨t', ht'⟩).symm
        (clockForward e t ht t' htclock x)) = clockForward e s hs s' hsclock x := by
  subst s'
  subst t'
  exact e.surgery_compatibility s hs hT t ht ht' x hx

variable {nextOrigin nextScale : ℝ} {J : Set ℝ}
  (hscale : 0 < nextScale) (hJ : J.OrdConnected) (phi : ℝ → ℝ)
  (hmem : MapsTo phi J I) (hmono : StrictMonoOn phi J)
  (hclock : ∀ s ∈ J, nextOrigin + s / nextScale = origin + phi s / scale)



noncomputable def seedCylinderReclock :
    SurgeryFlowCylinder F C nextOrigin nextScale J U where
  scale_pos := hscale
  interval_connected := hJ
  time_subset := by
    rintro _ ⟨s, hs, rfl⟩
    change nextOrigin + s / nextScale ∈ F.time_domain
    rw [hclock s hs]
    exact e.time_subset (mem_image_of_mem _ (hmem hs))
  forward := fun s hs => clockForward e (phi s) (hmem hs) _ (hclock s hs)
  inverse := fun s hs => clockInverse e (phi s) (hmem hs) _ (hclock s hs)
  forward_smooth := fun s hs => clockForward_smooth e (phi s) (hmem hs) _ (hclock s hs)
  inverse_smooth := fun s hs => clockInverse_smooth e (phi s) (hmem hs) _ (hclock s hs)
  left_inverse := fun s hs => clock_left_inverse e (phi s) (hmem hs) _ (hclock s hs)
  right_inverse := fun s hs => clock_right_inverse e (phi s) (hmem hs) _ (hclock s hs)
  slab_compatibility := fun a b hab hK hS s hs t ht hs' ht' x hx =>
    clock_slab e a b hab hK hS (phi s) (hmem hs) (phi t) (hmem ht) _ _
      (hclock s hs) (hclock t ht) hs' ht' x hx
  retained_at_surgery := by
    intro s hs hT _ hearlier
    apply clock_retained e (phi s) (hmem hs) _ (hclock s hs) hT
    obtain ⟨t, ht, hts⟩ := hearlier
    exact ⟨phi t, hmem ht, hmono ht hs hts⟩
  pre_retained_at_surgery := fun s hs hT _ t ht ht' x hx =>
    clock_pre_retained e (phi s) (hmem hs) (phi t) (hmem ht) _ _
      (hclock s hs) (hclock t ht) hT ht' x hx
  surgery_compatibility := fun s hs hT _ t ht ht' x hx =>
    clock_surgery e (phi s) (hmem hs) (phi t) (hmem ht) _ _
      (hclock s hs) (hclock t ht) hT ht' x hx



theorem seedCylinderReclock_forward_heq (s : ℝ) (hs : s ∈ J) (x : C.carrier) :
    HEq ((seedCylinderReclock e hscale hJ phi hmem hmono hclock).forward s hs x)
      (e.forward (phi s) (hmem hs) x) := by
  exact clockForward_heq e (phi s) (hmem hs) _ (hclock s hs) x



theorem seedCylinderReclock_curvature {K : ℝ}
    (hK : ∀ s (hs : s ∈ I), ∀ x ∈ U,
      (F.connection (origin + s / scale)).curvatureTensorNorm (e.forward s hs x) ≤ K)
    (s : ℝ) (hs : s ∈ J) (x : C.carrier) (hx : x ∈ U) :
    (F.connection (nextOrigin + s / nextScale)).curvatureTensorNorm
      ((seedCylinderReclock e hscale hJ phi hmem hmono hclock).forward s hs x) ≤ K := by
  change (F.connection _).curvatureTensorNorm
    (clockForward e (phi s) (hmem hs) _ (hclock s hs) x) ≤ K
  rw [clockForward_curvature]
  exact hK (phi s) (hmem hs) x hx

end PoincareConjecture.Proofs.M47
