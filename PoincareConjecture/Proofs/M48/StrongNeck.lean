import PoincareConjecture.Proofs.M48.CylinderSource
import PoincareConjecture.Proofs.M48.RoundCylinderCongruence
import PoincareConjecture.Proofs.M48.RegularGuards
import PoincareConjecture.Proofs.M33.GuardedCylinders

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

private theorem strongNeck_history_heq {G : GeneralizedRicciFlowData.{u}}
    {F : SurgeryFlowData.{u}} (H : M33RegularHistoryRealization G F) {s t : ℝ}
    (hs : s ∈ G.interval) (ht : t ∈ G.interval) {x : (G.slice s).carrier}
    {y : (G.slice t).carrier} (hst : s = t)
    (h : HEq (H.forward s hs x) (H.forward t ht y)) : HEq x y := by
  subst t
  exact heq_of_eq ((H.forward_openEmbedding s hs).injective (eq_of_heq h))

namespace M33RegularHistoryData

variable {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
  (H : M33RegularHistoryData W) {t epsilon : ℝ} (ht : t ∈ H.generalized.interval)
  (N : SurgeryStrongNeck F t epsilon)

include ht

theorem strongNeck_time_subset (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0) :
    t + s / N.neck.scale⁻¹ ^ 2 ∈ H.generalized.interval := by
  have hn := F.time_domain_nonnegative (N.cylinder.time_subset ⟨s, hs, rfl⟩)
  have hle : t + s / N.neck.scale⁻¹ ^ 2 ≤ t :=
    add_le_of_nonpos_right (div_nonpos_of_nonpos_of_nonneg hs.2 N.cylinder.scale_pos.le)
  rw [H.interval_eq] at ht ⊢
  exact W.interval_connected.out W.zero_mem ht ⟨hn, hle⟩

theorem strongNeck (hregular : t ∉ F.surgery_times) :
    ∃ Q : GeneralizedStrongNeck H.generalized t epsilon,
      H.history.forward t ht Q.center = N.neck.center ∧ Q.scale = N.neck.scale := by
  classical
  rcases N with ⟨neck, hepsilon, hconnection, cylinder, hterminal, hclose⟩
  subst epsilon
  let N : SurgeryStrongNeck F t neck.epsilon :=
    ⟨neck, rfl, hconnection, cylinder, hterminal, hclose⟩
  let f := H.regularDiffeomorph t ht hregular
  let U := f ⁻¹' N.neck.carrier
  let coordinate : RoundCylinderSpace → (H.generalized.slice t).carrier :=
    f.symm ∘ N.neck.coordinate_map
  let inverse := N.neck.coordinate_inverse ∘ f
  let fU : U ≃ₜ N.neck.carrier := f.toHomeomorph.sets rfl
  have hcoord (z : RoundCylinderSpace) (hz : z.2 ∈ Ioo (-N.neck.epsilon⁻¹) N.neck.epsilon⁻¹) :
      N.neck.coordinate_map z ∈ N.neck.carrier := by
    have heq := N.neck.coordinate_map_eq (z.1, ⟨z.2, hz⟩)
    exact heq ▸ (N.neck.coordinate (z.1, ⟨z.2, hz⟩)).property
  have hcoord' : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate
      (univ ×ˢ Ioo (-N.neck.epsilon⁻¹) N.neck.epsilon⁻¹) :=
    f.symm.contMDiff.comp_contMDiffOn N.neck.coordinate_map_smooth
  have htime := H.strongNeck_time_subset ht N
  obtain ⟨d, hd, hmetric⟩ := H.cylinders_from_surgery (F.slice t) t
    (N.neck.scale⁻¹ ^ 2) (Ioc (-1 : ℝ) 0) N.neck.carrier N.neck.carrier_open htime
    N.cylinder (fun _ hs => N.cylinder.regular_image_Ioc hs)
  let c := d.rebaseSource f
  have hscalar : (H.generalized.connection t).scalarCurvature (f.symm N.neck.center) =
      N.neck.connection.scalarCurvature N.neck.center := by
    rw [← H.scalar_pullback t ht]
    change (F.connection t).scalarCurvature (f (f.symm N.neck.center)) = _
    rw [f.apply_symm_apply, N.connection_eq]
  have hzero : ∀ h x, x ∈ U → c.pointMap 0 h x = (⟨t, x⟩ : H.generalized.point) := by
    intro h x hx
    apply Sigma.ext (by simp [GeneralizedFlowCylinder.pointMap])
    apply strongNeck_history_heq H.history (htime 0 h) ht (by simp)
    exact (heq_of_eq (hd 0 h (f x) hx)).trans (N.terminal_identity h (f x) hx)
  have hcomparison : RoundCylinderFamilyClose N.neck.epsilon (Ioc (-1 : ℝ) 0)
      (generalizedCylinderPullback c coordinate) := by
    apply RoundCylinderFamilyClose.congr (B' := surgeryCylinderPullback N.cylinder
      N.neck.coordinate_map) ?_ N.metric_comparison
    intro s hs z hz v w
    have hmem : f (coordinate z) ∈ N.neck.carrier := by
      simpa only [coordinate, Function.comp_apply, f.apply_symm_apply] using hcoord z hz
    have hdiff := (hcoord'.contMDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
    have hcomp : (f ∘ coordinate) = N.neck.coordinate_map := by
      funext y
      exact f.apply_symm_apply _
    have hderiv : (mfderiv (𝓡 3) (𝓡 3) f (coordinate z)).comp
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.neck.coordinate_map z := by
      rw [← mfderiv_comp z (f.contMDiff.mdifferentiable (by simp) _) hdiff, hcomp]
    have hv (v : RoundCylinderTangent z) :
        mfderiv (𝓡 3) (𝓡 3) f (coordinate z)
          (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) coordinate z v) =
        mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) N.neck.coordinate_map z v :=
      congrArg (fun A => A v) hderiv
    simp only [generalizedCylinderPullback, surgeryCylinderPullback, dif_pos hs]
    rw [d.rebaseSource_pullbackInner f N.neck.carrier_open s hs (coordinate z) hmem,
      hv v, hv w]
    change d.pullbackInner s hs (f (f.symm (N.neck.coordinate_map z))) _ _ = _
    rw [f.apply_symm_apply]
    exact hmetric s hs (N.neck.coordinate_map z) (hcoord z hz) _ _
  let Q : GeneralizedStrongNeck H.generalized t N.neck.epsilon := {
    epsilon_pos := N.neck.epsilon_pos
    center := f.symm N.neck.center
    scalar_center_pos := hscalar.symm ▸ N.neck.scalar_center_pos
    scale := N.neck.scale
    scale_pos := N.neck.scale_pos
    scale_scalar := by rw [hscalar]; exact N.neck.scale_eq_scalar
    carrier := U
    carrier_open := N.neck.carrier_open.preimage f.continuous
    coordinate := N.neck.coordinate.trans fU.symm
    coordinate_map := coordinate
    coordinate_map_eq := by
      intro z
      change f.symm (N.neck.coordinate z) = f.symm (N.neck.coordinate_map (z.1, z.2))
      rw [N.neck.coordinate_map_eq]
    coordinate_map_smooth := hcoord'
    coordinate_inverse := inverse
    coordinate_inverse_mem := fun x hx => (N.neck.coordinate_inverse_mem (f x) hx).2
    coordinate_inverse_left := by
      intro z
      change N.neck.coordinate_inverse (f (f.symm (N.neck.coordinate z))) = _
      rw [f.apply_symm_apply]
      exact N.neck.coordinate_inverse_left z
    coordinate_inverse_right := by
      intro x hx
      have h := congrArg Subtype.val (N.neck.coordinate_inverse_right (f x) hx)
      rw [N.neck.coordinate_map_eq] at h
      change f.symm (N.neck.coordinate_map (N.neck.coordinate_inverse (f x))) = x
      rw [h, f.symm_apply_apply]
    coordinate_inverse_smooth := N.neck.coordinate_inverse_smooth.comp
      f.contMDiff.contMDiffOn (fun _ hx => hx)
    central_sphere := f ⁻¹' N.neck.central_sphere
    central_sphere_eq := by
      ext x
      change (f x ∈ N.neck.central_sphere) ↔ x ∈ coordinate '' (univ ×ˢ {0})
      rw [N.neck.central_sphere_eq]
      constructor
      · rintro ⟨z, hz, hzx⟩
        exact ⟨z, hz, by dsimp only [coordinate, Function.comp_apply]; rw [hzx, f.symm_apply_apply]⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, (f.apply_symm_apply _).symm⟩
    center_on_central_sphere := by
      change f (f.symm N.neck.center) ∈ N.neck.central_sphere
      rw [f.apply_symm_apply]
      exact N.neck.center_on_central_sphere
    central_sphere_subset := fun _ hx => N.neck.central_sphere_subset hx
    time_cylinder := c
    cylinder_identity := hzero
    metric_comparison := hcomparison }
  exact ⟨Q, f.apply_symm_apply _, rfl⟩

theorem canonical_neck (hregular : t ∉ F.surgery_times) (C : ℝ)
    (x : (H.generalized.slice t).carrier)
    (hcenter : N.neck.center = H.history.forward t ht x) :
    GeneralizedCanonicalControl t x epsilon C := by
  obtain ⟨Q, hQ, _⟩ := H.strongNeck ht N hregular
  exact .neck Q ((H.history.forward_openEmbedding t ht).injective (hQ.trans hcenter))

end M33RegularHistoryData

end PoincareConjecture
