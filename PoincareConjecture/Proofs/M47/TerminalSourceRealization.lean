import PoincareConjecture.Proofs.M47.PositiveHistoryOrdinary
import PoincareConjecture.Proofs.M47.SeedCylinderClock
import PoincareConjecture.Proofs.M12.GeneralizedCylinderMetric
import PoincareConjecture.Proofs.M13.ContractionTransport
import PoincareConjecture.Proofs.M34.Standard.LocalHomothetyCurvature











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

private theorem exists_closed_normalization
    (P : GeneralizedParabolicRescalingTheory.{u} 3)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [SecondCountableTopology M]
    {I : SpacetimeInterval} (G : RicciFlow 3 M I.domain)
    {b Q τ : ℝ} (hτ : 0 < τ) (hQ : 0 < Q)
    (hI : I.domain = Icc (b - τ / Q) b) :
    ∃ F : RicciFlow 3 M (Icc (-τ) 0),
      ∀ (s : ℝ), s ∈ Icc (-τ) 0 → ∀ x : M,
        (∀ v w : TangentSpace (𝓡 3) x,
          (F.metric s).inner x v w = Q * (G.metric (b + s / Q)).inner x v w) ∧
        (F.connection s).scalarCurvature x =
          (G.connection (b + s / Q)).scalarCurvature x / Q ∧
        (F.connection s).curvatureTensorNorm x =
          (G.connection (b + s / Q)).curvatureTensorNorm x / Q := by
  obtain ⟨R⟩ := P.ordinary_flow M I G Q hQ b
  have hdomain : (parabolicInterval Q hQ b I).domain = Icc (-τ) 0 := by
    change (parabolicTimeOrderIso Q hQ b) '' I.domain = _
    rw [hI, OrderIso.image_Icc]
    have hleft : parabolicTime Q b (b - τ / Q) = -τ := by
      dsimp only [parabolicTime]
      field_simp
      ring
    simp only [parabolicTimeOrderIso_apply]
    rw [hleft]
    simp only [parabolicTime, sub_self, mul_zero]
  have hsub : Icc (-τ) 0 ⊆ (parabolicInterval Q hQ b I).domain := by
    rw [hdomain]
  let F : RicciFlow 3 M (Icc (-τ) 0) := {
    metric := R.flow.metric
    connection := R.flow.connection
    interval := ordConnected_Icc
    nontrivial := ⟨-τ, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩
    smooth := R.flow.smooth.mono (prod_mono hsub Subset.rfl)
    equation := fun t ht x v w => (R.flow.equation t (hsub ht) x v w).mono hsub }
  refine ⟨F, ?_⟩
  intro s _hs x
  refine ⟨R.metric_eq s x, ?_, ?_⟩
  · simpa only [parabolicTimeInv, Diffeomorph.coe_refl, id_eq] using
      M13.homothety_scalarCurvature_eq _ _ (Diffeomorph.refl (𝓡 3) M ∞)
        Q hQ (R.metric_homothety s) (G.connection _) (R.flow.connection s) x
  · simpa only [parabolicTimeInv, Diffeomorph.coe_refl, id_eq] using
      M13.homothety_curvatureTensorNorm_eq _ _ (Diffeomorph.refl (𝓡 3) M ∞)
        Q hQ (R.metric_homothety s) (G.connection _) (R.flow.connection s) x



theorem terminalSourceRealization_surgery
    (P : M47Predecessors.{u}) {S : SurgeryFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {b Q τ : ℝ} (hτ : 0 < τ)
    (U : TopologicalSpace.Opens C.carrier) (hne : (U : Set C.carrier).Nonempty)
    (e : SurgeryFlowCylinder S C b Q (Icc (-τ) 0) U) :
    ∃ F : RicciFlow 3 U (Icc (-τ) 0),
      ∀ (s : ℝ) (hs : s ∈ Icc (-τ) 0) (x : U),
        (∀ v w : TangentSpace (𝓡 3) x,
          (F.metric s).inner x v w = e.pullbackInner s hs x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) ∧
        (F.connection s).scalarCurvature x =
          (S.connection (b + s / Q)).scalarCurvature (e.forward s hs x.val) / Q ∧
        (F.connection s).curvatureTensorNorm x =
          (S.connection (b + s / Q)).curvatureTensorNorm (e.forward s hs x.val) / Q := by
  have ha : -τ / Q < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hτ) e.scale_pos
  have hmem : MapsTo (fun r : ℝ => Q * r) (Icc (-τ / Q) 0) (Icc (-τ) 0) := by
    intro r hr
    exact ⟨by simpa only [mul_comm] using (div_le_iff₀ e.scale_pos).mp hr.1,
      mul_nonpos_of_nonneg_of_nonpos e.scale_pos.le hr.2⟩
  have hmono : StrictMonoOn (fun r : ℝ => Q * r) (Icc (-τ / Q) 0) :=
    fun _ _ _ _ hrs => mul_lt_mul_of_pos_left hrs e.scale_pos
  have hclock : ∀ r ∈ Icc (-τ / Q) 0, b + r / 1 = b + (Q * r) / Q := by
    intro r _hr
    simp only [div_one, mul_div_cancel_left₀ r e.scale_pos.ne']
  let E := Proofs.M47.seedCylinderReclock e (by norm_num : (0 : ℝ) < 1)
    ordConnected_Icc (fun r : ℝ => Q * r) hmem hmono hclock
  obtain ⟨G, hG⟩ := M47Positive.exists_component_closed_ordinary_history P ha U hne E
  let I : SpacetimeInterval := {
    domain := Icc (b + (-τ / Q)) b
    ordConnected := G.interval
    nontrivial := G.nontrivial }
  have hI : I.domain = Icc (b - τ / Q) b := by
    simp only [I, neg_div, sub_eq_add_neg]
  obtain ⟨F, hF⟩ := exists_closed_normalization P.m13 (I := I) G hτ e.scale_pos hI
  refine ⟨F, ?_⟩
  intro s hs x
  have hu : s / Q ∈ Icc (-τ / Q) 0 :=
    ⟨div_le_div_of_nonneg_right hs.1 e.scale_pos.le,
      div_nonpos_of_nonpos_of_nonneg hs.2 e.scale_pos.le⟩
  have hparam : Q * (s / Q) = s := by
    rw [← mul_div_assoc, mul_div_cancel_left₀ s e.scale_pos.ne']
  have htime : b + (s / Q) / 1 = b + s / Q := by simp only [div_one]
  have hfunctions :
      (⟨b + (s / Q) / 1, fun y : U => E.forward (s / Q) hu y.val⟩ :
        (t : ℝ) × (U → (S.slice t).carrier)) =
        ⟨b + s / Q, fun y : U => e.forward s hs y.val⟩ := by
    apply Sigma.ext htime
    apply Function.hfunext rfl
    intro y y' hyy
    cases hyy
    have hf := Proofs.M47.seedCylinderReclock_forward_heq e
      (by norm_num : (0 : ℝ) < 1) ordConnected_Icc
      (fun r : ℝ => Q * r) hmem hmono hclock (s / Q) hu y.val
    have heq : ∀ r (hr : r ∈ Icc (-τ) 0), r = s →
        HEq (e.forward r hr y.val) (e.forward s hs y.val) := by
      intro r hr hrs
      subst r
      rfl
    exact hf.trans (heq _ _ hparam)
  refine ⟨?_, ?_, ?_⟩
  · intro v w
    have hm := congrArg (fun p : (t : ℝ) × (U → (S.slice t).carrier) =>
      (S.metric p.1).inner (p.2 x)
        (mfderiv (𝓡 3) (𝓡 3) p.2 x v) (mfderiv (𝓡 3) (𝓡 3) p.2 x w)) hfunctions
    have hphysical := ((hG (s / Q) hu x).1 v w).symm.trans hm
    simp only [div_one] at hphysical
    rw [(hF s hs x).1 v w, hphysical]
    have hf := (e.forward_smooth s hs x.val x.property).contMDiffAt
      (U.isOpen.mem_nhds x.property)
    have hd := mfderiv_comp x (hf.mdifferentiableAt (by simp))
      (contMDiff_subtype_val (n := ∞) x |>.mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) (fun y : U => e.forward s hs y.val) x = _ at hd
    rw [hd]
    rfl
  · have hr := congrArg (fun p : (t : ℝ) × (U → (S.slice t).carrier) =>
      (S.connection p.1).scalarCurvature (p.2 x)) hfunctions
    have hphysical := (hG (s / Q) hu x).2.1.trans hr
    have hread := (congrArg (fun t => (G.connection t).scalarCurvature x) htime).symm.trans
      hphysical
    exact ((hF s hs x).2.1).trans (congrArg (fun z : ℝ => z / Q) hread)
  · have hr := congrArg (fun p : (t : ℝ) × (U → (S.slice t).carrier) =>
      (S.connection p.1).curvatureTensorNorm (p.2 x)) hfunctions
    have hphysical := (hG (s / Q) hu x).2.2.trans hr
    have hread := (congrArg (fun t => (G.connection t).curvatureTensorNorm x) htime).symm.trans
      hphysical
    exact ((hF s hs x).2.2).trans (congrArg (fun z : ℝ => z / Q) hread)



theorem terminalSourceRealization_generalized
    (P : M47Predecessors.{u}) {G : GeneralizedRicciFlowData.{u}}
    {C : GeneralizedSliceCarrier.{u}} {b Q τ : ℝ} (hτ : 0 < τ)
    (U : TopologicalSpace.Opens C.carrier) (hne : (U : Set C.carrier).Nonempty)
    (e : GeneralizedFlowCylinder G C b Q (Icc (-τ) 0) U) :
    ∃ F : RicciFlow 3 U (Icc (-τ) 0),
      ∀ (s : ℝ) (hs : s ∈ Icc (-τ) 0) (x : U),
        (∀ v w : TangentSpace (𝓡 3) x,
          (F.metric s).inner x v w = e.pullbackInner s hs x.val
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
            (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w)) ∧
        (F.connection s).scalarCurvature x =
          (G.connection (b + s / Q)).scalarCurvature (e.forward s hs x.val) / Q ∧
        (F.connection s).curvatureTensorNorm x =
          (G.connection (b + s / Q)).curvatureTensorNorm (e.forward s hs x.val) / Q := by
  have htime (s : ℝ) (hs : s ∈ Icc (-τ) 0) : b + s / Q ∈ G.interval :=
    (G.slice_nonempty_iff _).mp ⟨e.forward s hs hne.choose⟩
  let J : SpacetimeInterval := {
    domain := Icc (-τ) 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨-τ, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩ }
  let I := Proofs.M12.cylinderPhysicalInterval b Q e.scale_pos J
  have hI : I.domain ⊆ G.interval := by
    rintro _ ⟨s, hs, rfl⟩
    exact htime s hs
  obtain ⟨geometry⟩ := Proofs.M12.flowBoxRicciGeometry G P.m11 P.m12
  let R := geometry.realization
  let metric := Proofs.M12.rawCylinderMetric R e hI
  let gauges := P.m12.gauges G.point Sigma.fst (Proofs.M12.flowInterval G)
    R.spacetime R.slices R.timeIntervals R.gaugeCover geometry.leafwise
  obtain ⟨ordinary⟩ := gauges.compatible_ordinary U I
    (Proofs.M12.rawCylinderTransport R e hI) metric (fun p _hp => geometry.equation p)
  have hdomain : I.domain = Icc (b - τ / Q) b := by
    change (parabolicTimeOrderIso Q e.scale_pos b).symm '' Icc (-τ) 0 = _
    rw [OrderIso.image_Icc]
    simp only [parabolicTimeOrderIso_symm_apply, parabolicTimeInv, zero_div,
      add_zero, neg_div, sub_eq_add_neg]
  obtain ⟨F, hF⟩ := exists_closed_normalization P.m13 ordinary.flow hτ e.scale_pos hdomain
  have hm (s : ℝ) (hs : s ∈ Icc (-τ) 0) (x : U) (v w : TangentSpace (𝓡 3) x) :
      (F.metric s).inner x v w = e.pullbackInner s hs x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → C.carrier) x w) := by
    have hraw := Proofs.M12.rawCylinderMetric_eq R e hI metric ⟨s, hs⟩
      (geometry.sliceIdentification (b + s / Q)) x v w
    rw [(hF s hs x).1 v w, ordinary.metric_eq, hraw]
    rw [← mul_div_assoc, mul_div_cancel_left₀ _ e.scale_pos.ne']
  refine ⟨F, ?_⟩
  intro s hs x
  have hf : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun y : U => e.forward s hs y.val) := by
    intro y
    exact ((e.forward_smooth s hs y.val y.property).contMDiffAt
      (U.isOpen.mem_nhds y.property)).comp y (contMDiff_subtype_val (n := ∞) y)
  have hlink (y : U) (v w : TangentSpace (𝓡 3) y) :
      (F.metric s).inner y v w = Q * (G.metric (b + s / Q)).inner
        (e.forward s hs y.val)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y v)
        (mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y w) := by
    rw [hm s hs y v w]
    have hforward := (e.forward_smooth s hs y.val y.property).contMDiffAt
      (U.isOpen.mem_nhds y.property)
    have hd := mfderiv_comp y (hforward.mdifferentiableAt (by simp))
      (contMDiff_subtype_val (n := ∞) y |>.mdifferentiableAt (by simp))
    change mfderiv (𝓡 3) (𝓡 3) (fun z : U => e.forward s hs z.val) y = _ at hd
    rw [hd]
    rfl
  refine ⟨hm s hs x, ?_, ?_⟩
  · exact (F.connection s).scalarCurvature_eq_of_local_homothety
      (G.connection (b + s / Q)) e.scale_pos isOpen_univ hf.contMDiffOn
      (fun y _hy v w => hlink y v w) (mem_univ x)
  · exact (F.connection s).curvatureTensorNorm_eq_of_local_homothety
      (G.connection (b + s / Q)) e.scale_pos isOpen_univ hf.contMDiffOn
      (fun y _hy v w => hlink y v w) (mem_univ x)

end PoincareConjecture.M47
