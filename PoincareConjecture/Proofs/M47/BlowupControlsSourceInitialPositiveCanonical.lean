import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialOlderOrdinary
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBirthIdentify
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialJoinedSource
import PoincareConjecture.Proofs.M47.BlowupControlsSourceGluedPhysicalLocal
import PoincareConjecture.Proofs.M47.CanonicalNeckInverseScaling
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.Prop15_2_RecentNeck












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 12

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M47

local notation "Ic" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

private theorem initialSigma_metric
    {F : SurgeryFlowData.{u}} {X : GeneralizedSliceCarrier.{u}} {t r : ℝ}
    (f : X.carrier → (F.slice t).carrier) (g : X.carrier → (F.slice r).carrier)
    (h : ∀ x, (⟨t, f x⟩ : Σ a, (F.slice a).carrier) = ⟨r, g x⟩)
    (x : X.carrier) (v w : TangentSpace (𝓡 3) x) :
    (F.metric t).inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w) =
      (F.metric r).inner (g x) (mfderiv (𝓡 3) (𝓡 3) g x v)
        (mfderiv (𝓡 3) (𝓡 3) g x w) := by
  have ht : t = r := congrArg Sigma.fst (h x)
  have hfunctions : (⟨t, f⟩ : (a : ℝ) × (X.carrier → (F.slice a).carrier)) = ⟨r, g⟩ := by
    apply Sigma.ext ht
    apply Function.hfunext rfl
    intro y y' hyy
    cases hyy
    exact (Sigma.mk.inj (h y)).2
  exact congrArg (fun p : (a : ℝ) × (X.carrier → (F.slice a).carrier) =>
    (F.metric p.1).inner (p.2 x) (mfderiv (𝓡 3) (𝓡 3) p.2 x v)
      (mfderiv (𝓡 3) (𝓡 3) p.2 x w)) hfunctions

private theorem initialComposed_pullback
    {F : SurgeryFlowData.{u}} {C X : GeneralizedSliceCarrier.{u}}
    {T q : ℝ} {J : Set ℝ} {V : Set C.carrier}
    (e : SurgeryFlowCylinder F C T q J V) (hV : IsOpen V)
    (f : X.carrier → C.carrier) (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (himage : ∀ x, f x ∈ V) (r : ℝ) (hr : r ∈ J)
    (x : X.carrier) (v w : TangentSpace (𝓡 3) x) :
    e.pullbackInner r hr (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x w) =
      q * (F.metric (T + r / q)).inner (e.forward r hr (f x))
        (mfderiv (𝓡 3) (𝓡 3) (e.forward r hr ∘ f) x v)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward r hr ∘ f) x w) := by
  have heSmooth := e.forward_smooth r hr |>.contMDiffAt (hV.mem_nhds (himage x))
  have he := heSmooth.mdifferentiableAt (by simp)
  have hc := mfderiv_comp x he (hf.mdifferentiableAt (by simp))
  unfold SurgeryFlowCylinder.pullbackInner
  rw [hc]
  rfl




theorem source_initial_positive_age_canonical
    (P : M47Predecessors.{u}) {epsilon beta : ℝ}
    (hglue : M45NeckGluingProperty.{u} epsilon beta)
    (hepsilon : 0 < epsilon) (hepsilonSmall : epsilon < 1 / 2)
    (hbeta : 0 < beta) (hbetaOne : beta ≤ 1)
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {g : RiemannianMetric 3 C.carrier} (N : EpsilonNeck g)
    (hNepsilon : N.epsilon = beta * epsilon / 2)
    {T q Q k tau s Cc : ℝ} (hQ : 0 < Q) (hk : 0 < k) (htau : 0 < tau) (hs : 0 < s)
    (hscale : N.scale⁻¹ ^ 2 = q * k)
    (hclock : MapsTo (fun u : ℝ => u / k) (Icc (-1 : ℝ) 0) (Icc (-tau) 0))
    (old : SurgeryFlowCylinder F C T q (Icc (-tau) 0) N.carrier)
    (hzero : ∀ hz, ∀ x ∈ N.carrier, ∀ v w : TangentSpace (𝓡 3) x,
      old.pullbackInner 0 hz x v w = q * g.inner x v w)
    (holdFamily : RoundCylinderFamilyClose N.epsilon (Icc (-1 : ℝ) 0)
      (fun u z v w => k * surgeryCylinderPullback old N.coordinate_map (u / k) z v w))
    {J : Set ℝ} {V : Set (F.slice T).carrier}
    (recent : SurgeryFlowCylinder F (F.slice T) T q J V)
    (hV : IsOpen V) (hJ : Icc (0 : ℝ) s ⊆ J)
    (hbased : ∀ hz x, x ∈ V → HEq (recent.forward 0 hz x) x)
    (Up : TopologicalSpace.Opens (F.slice T).carrier) (hUpV : (Up : Set _) ⊆ V)
    (center : Up)
    (D : PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier (F.slice T).carrier ∞)
    (hDsource : D.source = N.carrier) (hUpD : (Up : Set _) ⊆ D.target)
    (hDpoint : ∀ x, HEq (D x) (old.forward 0 ⟨by linarith only [htau], le_rfl⟩ x))
    (hDmetric : ∀ x ∈ D.source, ∀ v w : TangentSpace (𝓡 3) x,
      (F.metric T).inner (D x) (mfderiv (𝓡 3) (𝓡 3) D x v)
        (mfderiv (𝓡 3) (𝓡 3) D x w) = g.inner x v w)
    (hcenter : D N.center = center.val)
    (Grecent : RicciFlow 3 Up (Icc (-(Q / q * s)) 0))
    (patch : M45CylinderPatch (neckOpenSourceCarrier Up) (beta * epsilon)⁻¹ center)
    (hRecentTimes : MapsTo (fun u : ℝ => s + u / (Q / q)) (Icc (-(Q / q * s)) 0) J)
    (hrecentMetric : ∀ u (hu : u ∈ Icc (-(Q / q * s)) 0),
      ∀ x : Up, ∀ v w : TangentSpace (𝓡 3) x,
        (Grecent.metric u).inner x v w = (Q / q) *
          recent.pullbackInner (s + u / (Q / q)) (hRecentTimes hu) x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Up → (F.slice T).carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Up → (F.slice T).carrier) x w))
    (hjoinMetric : ∀ x : Up, ∀ v w : TangentSpace (𝓡 3) x,
      (Grecent.metric (-(Q / q * s))).inner x v w = Q * (F.metric T).inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Up → (F.slice T).carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : Up → (F.slice T).carrier) x w))
    (hfinal : (Grecent.connection 0).scalarCurvature center = 1)
    (hrecentFamily : RoundCylinderFamilyClose (beta * epsilon) (Icc (-(Q / q * s)) 0)
      (fun u => roundCylinderPullback (Grecent.metric u) patch.coordinate))
    (hscalar : (F.connection (T + s / q)).scalarCurvature
      (recent.forward s (hJ ⟨hs.le, le_rfl⟩) center.val) = Q) :
    SurgeryCanonicalControl F (T + s / q)
      (recent.forward s (hJ ⟨hs.le, le_rfl⟩) center.val) epsilon Cc := by
  let H := Q / q
  let dr := H * s
  let dold := dr + H * tau
  let U : TopologicalSpace.Opens C.carrier := ⟨N.carrier, N.carrier_open⟩
  have hq : 0 < q := old.scale_pos
  have hH : 0 < H := div_pos hQ hq
  have hdr : 0 < dr := mul_pos hH hs
  have hspan : 0 < H * tau := mul_pos hH htau
  have horder : dr < dold := by dsimp only [dold]; linarith only [hspan]
  have hHq : H * q = Q := div_mul_cancel₀ Q hq.ne'
  obtain ⟨Gold, older, holdCenter, holdCarrier, _holdScale, _holdCoordinate, holdMetric⟩ :=
    exists_source_initial_older_ordinary P N hk hH htau hscale hclock old hzero holdFamily
      (dr := dr)
  have hOldJoin (x : U) (v w : TangentSpace (𝓡 3) x) :
      (Gold.metric (-dr)).inner x v w = Q * g.inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) := by
    have hm := holdMetric (-dr) ⟨by linarith only [horder], le_rfl⟩
      (show (-dr + dr) / H ∈ Icc (-tau) 0 by simp; linarith only [htau]) x v w
    simp only [neg_add_cancel, zero_div] at hm
    rw [hm, hzero _ x.val x.property, ← mul_assoc, hHq]
  obtain ⟨identify, hidentify, hidentifySmooth, hidentifyInjective, hidentifyCenter, hjoining⟩ :=
    exists_source_initial_birth_identification U Up D hDsource hUpD g (F.metric T)
      hDmetric (Gold.metric (-dr)) (Grecent.metric (-dr)) Q hOldJoin hjoinMetric
        older.neck.center center (by rw [holdCenter]; exact hcenter)
  let older' : SurgeryOrdinaryStrongNeck (neckOpenSourceCarrier U) Gold (-dr)
      (beta * epsilon / 2) := {
    neck := older.neck
    epsilon_eq := older.epsilon_eq.trans hNepsilon
    connection_eq := older.connection_eq
    backward_subset := older.backward_subset
    comparison := by simpa only [hNepsilon] using older.comparison }
  let I : M45NeckGluingInput epsilon beta := {
    recent_duration := dr
    older_duration := dold
    recent_duration_pos := hdr
    durations_ordered := horder
    recent_carrier := neckOpenSourceCarrier Up
    older_carrier := neckOpenSourceCarrier U
    recent_flow := Grecent
    older_flow := Gold
    center := center
    final_scalar_one := hfinal
    recent_patch := patch
    recent_comparison := hrecentFamily
    older_neck := older'
    identify := identify
    identify_smooth := hidentifySmooth.contMDiffOn
    identify_injective := hidentifyInjective.injOn
    identify_image := by rw [show older'.neck.carrier = univ from holdCarrier]; exact subset_univ _
    identify_center := hidentifyCenter
    joining_metric := fun x _ v w => hjoining x v w }
  obtain ⟨conclusion⟩ := hglue I
  obtain ⟨hOldTimes, hNewTimes, joined, hpast, hfuture⟩ :=
    exists_source_initial_joined_source hQ htau hs.le rfl old recent hJ D hDsource hDpoint
      hbased Up.isOpen ⟨center.val, center.property⟩ hUpD hUpV
  have hunit : Ioc (-1 : ℝ) 0 ⊆ Icc (-dold) 0 := by
    intro u hu
    by_cases hrecent : -dr ≤ u
    · exact ⟨by linarith only [horder, hrecent], hu.2⟩
    · exact ⟨(conclusion.older_survival u hu (lt_of_not_ge hrecent)).1.le, hu.2⟩
  let openJoined := neckOpenSourceCylinder Up center joined
  have hrecentRead (u : ℝ) (hu : u ∈ Icc (-dr) 0) (hu' : u ∈ Icc (-dold) 0)
      (x : Up) (v w : TangentSpace (𝓡 3) x) :
      openJoined.pullbackInner u hu' x v w = (Grecent.metric u).inner x v w := by
    have hm := initialSigma_metric (X := neckOpenSourceCarrier Up)
      (fun y : Up => joined.forward u hu' y.val)
      (fun y : Up => recent.forward (s + u / H) (hNewTimes hu) y.val)
      (fun y => hfuture u hu hu' y.val) x v w
    have hc := initialComposed_pullback (X := neckOpenSourceCarrier Up) recent hV
      (Subtype.val : Up → (F.slice T).carrier) contMDiff_subtype_val
      (fun y : Up => hUpV y.property) (s + u / H) (hRecentTimes hu) x v w
    rw [neckOpenSourceCylinder_pullbackInner, hm, hrecentMetric u hu]
    rw [hc]
    rw [← mul_assoc, hHq]
    rfl
  have hpastRead (u : ℝ) (hu : u ∈ Icc (-dold) (-dr)) (hu' : u ∈ Icc (-dold) 0)
      (x : Up) (v w : TangentSpace (𝓡 3) x) :
      openJoined.pullbackInner u hu' x v w =
        (Gold.metric u).inner (identify x) (mfderiv (𝓡 3) (𝓡 3) identify x v)
          (mfderiv (𝓡 3) (𝓡 3) identify x w) := by
    let f : Up → C.carrier := Subtype.val ∘ identify
    have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f := contMDiff_subtype_val.comp hidentifySmooth
    have hm := initialSigma_metric (X := neckOpenSourceCarrier Up)
      (fun y : Up => joined.forward u hu' y.val)
      (fun y : Up => old.forward ((u + dr) / H) (hOldTimes hu) (f y))
      (fun y => by
        simpa only [f, Function.comp_apply, hidentify] using
          (hpast u hu hu' y.val y.property)) x v w
    have hsub : MDifferentiableAt (𝓡 3) (𝓡 3)
        (Subtype.val : U → C.carrier) (identify x) :=
      contMDiff_subtype_val.mdifferentiableAt (n := ∞) (by simp)
    have hc : mfderiv (𝓡 3) (𝓡 3) f x =
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (identify x)).comp
          (mfderiv (𝓡 3) (𝓡 3) identify x) :=
      mfderiv_comp x hsub (hidentifySmooth.mdifferentiableAt (by simp))
    rw [neckOpenSourceCylinder_pullbackInner, hm, holdMetric u hu (hOldTimes hu)]
    have hv := congrArg (fun L => L v) hc
    have hw := congrArg (fun L => L w) hc
    change mfderiv (𝓡 3) (𝓡 3) f x v =
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (identify x)
        (mfderiv (𝓡 3) (𝓡 3) identify x v) at hv
    change mfderiv (𝓡 3) (𝓡 3) f x w =
      mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) (identify x)
        (mfderiv (𝓡 3) (𝓡 3) identify x w) at hw
    rw [← hv, ← hw]
    have hcompose := initialComposed_pullback (X := neckOpenSourceCarrier Up)
      old N.carrier_open f hf (fun y => (identify y).property)
        ((u + dr) / H) (hOldTimes hu) x v w
    change old.pullbackInner ((u + dr) / H) (hOldTimes hu) (identify x).val
      (mfderiv (𝓡 3) (𝓡 3) f x v) (mfderiv (𝓡 3) (𝓡 3) f x w) = _ at hcompose
    rw [hcompose]
    rw [← mul_assoc, hHq]
    rfl
  have hbe : 0 < beta * epsilon := mul_pos hbeta hepsilon
  have hbeLe : beta * epsilon ≤ epsilon := by nlinarith only [hbetaOne, hepsilon]
  let short := (I.recentNeck hbe (hbeLe.trans_lt hepsilonSmall)).restrict hbeLe hepsilonSmall
  let physical := short.scaleMetric Q⁻¹ (inv_pos.mpr hQ)
  obtain ⟨hphysicalEps, hphysicalScale, hphysicalScalar, _hc, _hcarrier, _hmap⟩ :=
    epsilonNeck_scaleMetric_inv_normalization short hfinal hQ
  let unit := openJoined.restrict hunit ordConnected_Ioc (subset_univ physical.carrier)
  have hphysicalScalePos : 0 < physical.scale⁻¹ ^ 2 := by rw [hphysicalScale]; exact hQ
  have hsameClock : ∀ u ∈ Ioc (-1 : ℝ) 0,
      (T + s / q) + u / (physical.scale⁻¹ ^ 2) = (T + s / q) + id u / Q := by
    intro u _
    rw [hphysicalScale]
    rfl
  let e := seedCylinderReclock unit hphysicalScalePos ordConnected_Ioc id
    (fun _ hu => hu) (fun _ _ _ _ h => h) hsameClock
  have hpoint : (⟨(T + s / q) + 0 / (physical.scale⁻¹ ^ 2),
      e.forward 0 (by constructor <;> norm_num) physical.center⟩ : Σ t, (F.slice t).carrier) =
        ⟨T + s / q, recent.forward s (hJ ⟨hs.le, le_rfl⟩) center.val⟩ := by
    apply Sigma.ext (by simp only [zero_div, add_zero])
    have hforward := seedCylinderReclock_forward_heq unit hphysicalScalePos ordConnected_Ioc id
      (fun _ hu => hu) (fun _ _ _ _ h => h) hsameClock
        0 (by constructor <;> norm_num) physical.center
    have hrecent := (Sigma.mk.inj (hfuture 0 ⟨by linarith only [hdr], le_rfl⟩
      (hunit (by constructor <;> norm_num)) center.val)).2
    have hsame (r : ℝ) (hr : r ∈ J) (hrs : r = s) :
        HEq (recent.forward r hr center.val)
          (recent.forward s (hJ ⟨hs.le, le_rfl⟩) center.val) := by
      subst r
      rfl
    exact hforward.trans (hrecent.trans (hsame _ _ (by simp only [zero_div, add_zero])))
  have hscalarPhysical : (F.connection ((T + s / q) + 0 / (physical.scale⁻¹ ^ 2))).scalarCurvature
      (e.forward 0 (by constructor <;> norm_num) physical.center) =
        physical.connection.scalarCurvature physical.center := by
    rw [hphysicalScalar]
    exact (congrArg (fun p : Σ t, (F.slice t).carrier =>
      (F.connection p.1).scalarCurvature p.2) hpoint).trans hscalar
  have hpull : ∀ u ∈ Ioc (-1 : ℝ) 0, ∀ z : RoundCylinderSpace,
      z.2 ∈ Ioo (-epsilon⁻¹) epsilon⁻¹ → ∀ v w,
        surgeryCylinderPullback e physical.coordinate_map u z v w =
          I.piecewiseTensor I.recent_patch.coordinate u z v w := by
    intro u hu z hz v w
    have hr := neck_reclock_cylinderPullback unit hphysicalScalePos ordConnected_Ioc id
      (fun _ ht => ht) (fun _ _ _ _ h => h) hsameClock physical.coordinate_map u hu z v w
    have hratio : physical.scale⁻¹ ^ 2 / Q = 1 := by rw [hphysicalScale, div_self hQ.ne']
    rw [hratio, one_mul] at hr
    rw [hr]
    simp only [id_eq, surgeryCylinderPullback, dif_pos hu]
    by_cases hrecent : -dr ≤ u
    · change openJoined.pullbackInner u (hunit hu) (patch.coordinate z)
        (mfderiv Ic (𝓡 3) patch.coordinate z v) (mfderiv Ic (𝓡 3) patch.coordinate z w) = _
      rw [hrecentRead u ⟨hrecent, hu.2⟩ (hunit hu)]
      simp only [M45NeckGluingInput.piecewiseTensor, I, if_pos hrecent, roundCylinderPullback]
    · have hold : u ∈ Icc (-dold) (-dr) :=
        ⟨(conclusion.older_survival u hu (lt_of_not_ge hrecent)).1.le, (lt_of_not_ge hrecent).le⟩
      change openJoined.pullbackInner u (hunit hu) (patch.coordinate z)
        (mfderiv Ic (𝓡 3) patch.coordinate z v) (mfderiv Ic (𝓡 3) patch.coordinate z w) = _
      rw [hpastRead u hold (hunit hu)]
      have hpatch : MDifferentiableAt Ic (𝓡 3) (patch.coordinate : RoundCylinderSpace → Up) z :=
        (physical.coordinate_map_smooth.contMDiffAt
          ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, hz⟩)).mdifferentiableAt (by simp)
      have hc := mfderiv_comp z (hidentifySmooth.mdifferentiableAt (by simp)) hpatch
      simp only [M45NeckGluingInput.piecewiseTensor, I, if_neg hrecent, roundCylinderPullback]
      rw [hc]
      rfl
  have hcanonical := surgeryCanonicalControl_of_neck_gluing_family_on hglue I physical
    hphysicalEps e hscalarPhysical hpull (Cc := Cc)
  exact (congrArg (fun p : Σ t, (F.slice t).carrier =>
    SurgeryCanonicalControl F p.1 p.2 epsilon Cc) hpoint).mp hcanonical

end PoincareConjecture.M47
