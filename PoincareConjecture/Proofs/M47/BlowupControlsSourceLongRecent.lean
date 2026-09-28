import PoincareConjecture.Proofs.M47.CanonicalNeckPatch
import PoincareConjecture.Proofs.M47.CanonicalNeckInverseScaling
import PoincareConjecture.Proofs.M47.CanonicalNeckPhysicalAssembly
import PoincareConjecture.Proofs.M47.CanonicalNeckOpenSource
import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderMetric
import PoincareConjecture.Proofs.M34.Standard.NeckRestriction









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)



theorem source_long_recent_family_canonical
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin Q dr eta epsilon Cc : ℝ}
    (E : SurgeryFlowCylinder F C origin Q (Icc (-dr) 0) univ)
    (G : RicciFlow 3 C.carrier (Icc (-dr) 0)) (x : C.carrier)
    (patch : M45CylinderPatch C eta⁻¹ x)
    (heta : 0 < eta) (hetaEps : eta ≤ epsilon) (hepsSmall : epsilon < 1 / 2)
    (hdr : 1 ≤ dr)
    (hmetric : ∀ s (hs : s ∈ Icc (-dr) 0), ∀ y : C.carrier,
      ∀ v w : TangentSpace (𝓡 3) y,
        E.pullbackInner s hs y v w = (G.metric s).inner y v w)
    (hfinal : (G.connection 0).scalarCurvature x = 1)
    (hfamily : RoundCylinderFamilyClose eta (Icc (-dr) 0)
      (fun s => roundCylinderPullback (G.metric s) patch.coordinate))
    (hscalar : (F.connection (origin + 0 / Q)).scalarCurvature
      (E.forward 0 ⟨by linarith only [hdr], le_rfl⟩ x) = Q) :
    SurgeryCanonicalControl F (origin + 0 / Q)
      (E.forward 0 ⟨by linarith only [hdr], le_rfl⟩ x) epsilon Cc := by
  have hQ := E.scale_pos
  have hz : (0 : ℝ) ∈ Icc (-dr) 0 := ⟨by linarith only [hdr], le_rfl⟩
  have hclose0 : RoundCylinderClose eta 0
      (roundCylinderPullback (G.metric 0) patch.coordinate) :=
    ⟨hfamily.1 0 hz, hfamily.2.choose, hfamily.2.choose_spec.1,
      hfamily.2.choose_spec.2 0 hz⟩
  obtain ⟨N, hNeps, _hNscale, hNcenter, hNconn, _hNcarrier, hNmap⟩ :=
    exists_scalar_one_patch_neck (G.connection 0) patch heta
      (hetaEps.trans_lt hepsSmall) hfinal hclose0
  let short := N.restrict (hNeps.trans_le hetaEps) hepsSmall
  have hshortScalar : short.connection.scalarCurvature short.center = 1 := by
    change N.connection.scalarCurvature N.center = 1
    rw [hNconn, hNcenter]
    exact hfinal
  let physical := short.scaleMetric Q⁻¹ (inv_pos.mpr hQ)
  obtain ⟨hphysicalEps, hphysicalScale, hphysicalScalar, _hc, _hcarrier, _hmap⟩ :=
    epsilonNeck_scaleMetric_inv_normalization short hshortScalar hQ
  change physical.epsilon = epsilon at hphysicalEps
  have hunit : Ioc (-1 : ℝ) 0 ⊆ Icc (-dr) 0 := by
    intro s hs
    exact ⟨by linarith only [hdr, hs.1], hs.2⟩
  let unit := E.restrict hunit ordConnected_Ioc (subset_univ physical.carrier)
  have hphysicalPos : 0 < physical.scale⁻¹ ^ 2 := by rw [hphysicalScale]; exact hQ
  have hclock : ∀ s ∈ Ioc (-1 : ℝ) 0,
      origin + s / (physical.scale⁻¹ ^ 2) = origin + id s / Q := by
    intro s _
    rw [hphysicalScale]
    rfl
  let e := seedCylinderReclock unit hphysicalPos ordConnected_Ioc id
    (fun _ hs => hs) (fun _ _ _ _ h => h) hclock
  have hpoint : (⟨origin + 0 / (physical.scale⁻¹ ^ 2),
      e.forward 0 (by constructor <;> norm_num) physical.center⟩ : Σ t, (F.slice t).carrier) =
        ⟨origin + 0 / Q, E.forward 0 hz x⟩ := by
    apply Sigma.ext (by simp only [zero_div, add_zero])
    have hforward := seedCylinderReclock_forward_heq unit hphysicalPos ordConnected_Ioc id
      (fun _ hs => hs) (fun _ _ _ _ h => h) hclock
        0 (by constructor <;> norm_num) physical.center
    exact hforward.trans (heq_of_eq (congrArg (E.forward 0 hz) hNcenter))
  have hscalarPhysical : (F.connection (origin + 0 / (physical.scale⁻¹ ^ 2))).scalarCurvature
      (e.forward 0 (by constructor <;> norm_num) physical.center) =
        physical.connection.scalarCurvature physical.center := by
    rw [hphysicalScalar]
    exact (congrArg (fun p : Σ t, (F.slice t).carrier =>
      (F.connection p.1).scalarCurvature p.2) hpoint).trans hscalar
  have hfull := (hfamily.mono_time hunit).mono_epsilon heta hetaEps
    (fun _ hs => hs.2.trans_lt zero_lt_one)
  have hclose : RoundCylinderFamilyClose physical.epsilon (Ioc (-1 : ℝ) 0)
      (surgeryCylinderPullback e physical.coordinate_map) := by
    rw [hphysicalEps]
    apply hfull.congr_cylinder
    intro s hs z _hz v w
    have hr := neck_reclock_cylinderPullback unit hphysicalPos ordConnected_Ioc id
      (fun _ ht => ht) (fun _ _ _ _ h => h) hclock physical.coordinate_map s hs z v w
    have hratio : physical.scale⁻¹ ^ 2 / Q = 1 := by rw [hphysicalScale, div_self hQ.ne']
    rw [hratio, one_mul] at hr
    rw [hr]
    simp only [id_eq, surgeryCylinderPullback, dif_pos hs]
    change roundCylinderPullback (G.metric s) patch.coordinate z v w =
      E.pullbackInner s (hunit hs) (N.coordinate_map z)
        (mfderiv Ic (𝓡 3) N.coordinate_map z v) (mfderiv Ic (𝓡 3) N.coordinate_map z w)
    rw [hmetric, hNmap]
    rfl
  obtain ⟨neck, hcenter⟩ := exists_physical_strong_neck_of_family physical e hscalarPhysical hclose
  have hcanonical : SurgeryCanonicalControl F (origin + 0 / (physical.scale⁻¹ ^ 2))
      (e.forward 0 (by constructor <;> norm_num) physical.center) epsilon Cc := by
    rw [← hphysicalEps]
    exact SurgeryCanonicalControl.neck neck hcenter
  exact (congrArg (fun p : Σ t, (F.slice t).carrier =>
    SurgeryCanonicalControl F p.1 p.2 epsilon Cc) hpoint).mp hcanonical



theorem source_long_recent_canonical
    {F : SurgeryFlowData.{u}} {T q Q s epsilon eta Cc : ℝ}
    {J : Set ℝ} {V : Set (F.slice T).carrier}
    (recent : SurgeryFlowCylinder F (F.slice T) T q J V)
    (hQ : 0 < Q) (hs : 0 < s) (hJ : Icc (0 : ℝ) s ⊆ J)
    (Up : TopologicalSpace.Opens (F.slice T).carrier) (hUpV : (Up : Set _) ⊆ V)
    (center : Up) (Grecent : RicciFlow 3 Up (Icc (-(Q / q * s)) 0))
    (patch : M45CylinderPatch (neckOpenSourceCarrier Up) eta⁻¹ center)
    (heta : 0 < eta) (hetaEps : eta ≤ epsilon) (hepsSmall : epsilon < 1 / 2)
    (hRecentTimes : MapsTo (fun u : ℝ => s + u / (Q / q)) (Icc (-(Q / q * s)) 0) J)
    (hrecentMetric : ∀ u (hu : u ∈ Icc (-(Q / q * s)) 0),
      ∀ x : Up, ∀ v w : TangentSpace (𝓡 3) x,
        (Grecent.metric u).inner x v w = (Q / q) *
          recent.pullbackInner (s + u / (Q / q)) (hRecentTimes hu) x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Up → (F.slice T).carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Up → (F.slice T).carrier) x w))
    (hfinal : (Grecent.connection 0).scalarCurvature center = 1)
    (hfamily : RoundCylinderFamilyClose eta (Icc (-(Q / q * s)) 0)
      (fun u => roundCylinderPullback (Grecent.metric u) patch.coordinate))
    (hage : 1 ≤ Q / q * s)
    (hscalar : (F.connection (T + s / q)).scalarCurvature
      (recent.forward s (hJ ⟨hs.le, le_rfl⟩) center.val) = Q) :
    SurgeryCanonicalControl F (T + s / q)
      (recent.forward s (hJ ⟨hs.le, le_rfl⟩) center.val) epsilon Cc := by
  let H := Q / q
  let dr := H * s
  let phi := fun u : ℝ => s + u / H
  have hq := recent.scale_pos
  have hH : 0 < H := div_pos hQ hq
  have hmono : StrictMonoOn phi (Icc (-dr) 0) := by
    intro u _ v _ huv
    have h := (div_lt_div_iff_of_pos_right hH).mpr huv
    change s + u / H < s + v / H
    linarith only [h]
  have hclock : ∀ u ∈ Icc (-dr) 0, (T + s / q) + u / Q = T + phi u / q := by
    intro u _
    dsimp only [phi, H]
    field_simp
    ring
  let raw := seedCylinderReclock recent hQ ordConnected_Icc phi hRecentTimes hmono hclock
  let restricted := raw.restrict Subset.rfl ordConnected_Icc hUpV
  let E := neckOpenSourceCylinder Up center restricted
  have hmetric (u : ℝ) (hu : u ∈ Icc (-dr) 0) (x : Up)
      (v w : TangentSpace (𝓡 3) x) :
      E.pullbackInner u hu x v w = (Grecent.metric u).inner x v w := by
    have hm := neck_source_pullbackInner restricted (neckOpenSourceInclusion Up center)
      univ (Subset.refl _) (fun y _ => y.property) Up.isOpen u hu (mem_univ x) v w
    change E.pullbackInner u hu x v w = restricted.pullbackInner u hu x.val
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Up → (F.slice T).carrier) x v)
      (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Up → (F.slice T).carrier) x w) at hm
    rw [hm]
    have hr := neck_reclock_pullbackInner recent hQ ordConnected_Icc phi
      hRecentTimes hmono hclock u hu x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Up → (F.slice T).carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Up → (F.slice T).carrier) x w)
    exact hr.trans (hrecentMetric u hu x v w).symm
  have hz : (0 : ℝ) ∈ Icc (-dr) 0 := ⟨by dsimp only [dr, H]; linarith only [hage], le_rfl⟩
  have hpoint : (⟨(T + s / q) + 0 / Q, E.forward 0 hz center⟩ : Σ t, (F.slice t).carrier) =
      ⟨T + s / q, recent.forward s (hJ ⟨hs.le, le_rfl⟩) center.val⟩ := by
    apply Sigma.ext (by simp only [zero_div, add_zero])
    have hforward := seedCylinderReclock_forward_heq recent hQ ordConnected_Icc phi
      hRecentTimes hmono hclock 0 hz center.val
    have hsame (r : ℝ) (hr : r ∈ J) (hrs : r = s) :
        HEq (recent.forward r hr center.val)
          (recent.forward s (hJ ⟨hs.le, le_rfl⟩) center.val) := by
      subst r
      rfl
    exact hforward.trans (hsame _ _ (by simp only [phi, zero_div, add_zero]))
  have hscalarE : (F.connection ((T + s / q) + 0 / Q)).scalarCurvature
      (E.forward 0 hz center) = Q :=
    (congrArg (fun p : Σ t, (F.slice t).carrier =>
      (F.connection p.1).scalarCurvature p.2) hpoint).trans hscalar
  have hcanonical := source_long_recent_family_canonical E Grecent center patch heta
    hetaEps hepsSmall hage hmetric hfinal hfamily hscalarE (Cc := Cc)
  exact (congrArg (fun p : Σ t, (F.slice t).carrier =>
    SurgeryCanonicalControl F p.1 p.2 epsilon Cc) hpoint).mp hcanonical

end PoincareConjecture.M47
