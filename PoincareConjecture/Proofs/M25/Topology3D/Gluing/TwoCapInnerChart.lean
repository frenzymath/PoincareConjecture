import PoincareConjecture.Proofs.M25.Topology3D.Gluing.ClosedModelCapStandardEnd












set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D




theorem capCertificate_exists_radial_lower_cut_chart_of_services
    (hS : SchoenfliesService) (hD : DiffSphereIsotopyService)
    {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M]
    [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
    [T3Space M] {g : RiemannianMetric 3 M}
    (C : ClosedModelCapData g) (hkind : C.model_kind = CapModelKind.euclidean)
    {v a b : ℝ} (hv : v ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹)
    (hva : v < a) (hab : a < b) (hb : b < C.epsilon⁻¹) :
    let U : TopologicalSpace.Opens M :=
      { carrier := C.carrier, is_open' := C.carrier_open }
    let L := C.epsilon⁻¹
    let N := C
    let K : ℝ → Set M := fun t => C.carrier \ N.region t L
    ∃ (Phi : Diffeomorph (𝓡 3) (𝓡 3) U E3 ∞)
      (A : E3 ≃ₗᵢ[ℝ] E3) (r0 : ℝ) (sigma : OpenPartialHomeomorph ℝ ℝ)
      (I : OpenPartialHomeomorph M E3),
      0 < r0 ∧ sigma.source = Ioo v L ∧ sigma.target = Ioi r0 ∧
      ContDiffOn ℝ ∞ (sigma : ℝ → ℝ) sigma.source ∧
      ContDiffOn ℝ ∞ sigma.symm sigma.target ∧
      StrictMonoOn (sigma : ℝ → ℝ) sigma.source ∧
      (∀ s ∈ sigma.source, 0 < deriv (sigma : ℝ → ℝ) s) ∧
      (∀ (q : UnitTwoSphere) (s : ℝ) (x : U),
        s ∈ Ioo v L → x.val = N.coordinate_map (q, s) →
        Phi x = sigma s • (sphereMap A q).val) ∧
      (∀ t ∈ Ioo v L,
        Phi '' ((Subtype.val : U → M) ⁻¹' (N.region t L)) =
            {z : E3 | sigma t < ‖z‖} ∧
        Phi '' ((Subtype.val : U → M) ⁻¹' (K t)) = closedBall 0 (sigma t) ∧
        Phi '' ((Subtype.val : U → M) ⁻¹' interior (K t)) = ball 0 (sigma t)) ∧
      I.source = interior (K b) ∧ I.target = ball 0 (sigma b) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ I I.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ I.symm I.target ∧
      (∀ x : U, x.val ∈ interior (K b) → I x.val = Phi x) ∧
      (∀ z ∈ I.target, I.symm z = (Phi.symm z).val) ∧
      I '' (N.region a b) = {z : E3 | sigma a < ‖z‖ ∧ ‖z‖ < sigma b} ∧
      (∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo a b →
        N.coordinate_map (q, s) ∈ I.source ∧
        I (N.coordinate_map (q, s)) = sigma s • (sphereMap A q).val ∧
        sigma s • (sphereMap A q).val ∈ I.target ∧
        I.symm (sigma s • (sphereMap A q).val) = N.coordinate_map (q, s)) := by
  classical
  let U : TopologicalSpace.Opens M :=
    { carrier := C.carrier, is_open' := C.carrier_open }
  let L := C.epsilon⁻¹
  let N := C
  let K : ℝ → Set M := fun t => C.carrier \ N.region t L
  obtain ⟨Phi, A, r0, sigma, hr0, hsrc, htgt, hsmooth, hismooth, hmono, hderiv, hformula⟩ :=
    closedModelCapData_exists_standardEnd_of_services hS hD C hkind hv
  have hmono' : StrictMonoOn (sigma : ℝ → ℝ) (Ioo v L) := by
    simpa only [hsrc] using hmono
  have hsource (s : ℝ) (hs : s ∈ Ioo v L) : s ∈ sigma.source := hsrc.symm ▸ hs
  have hradius (s : ℝ) (hs : s ∈ Ioo v L) : r0 < sigma s := by
    have h := sigma.map_source (hsource s hs)
    simpa only [htgt, mem_Ioi] using h
  have hpositive (s : ℝ) (hs : s ∈ Ioo v L) : 0 < sigma s := hr0.trans (hradius s hs)
  have hnorm (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ioo v L) :
      ‖sigma s • (sphereMap A q).val‖ = sigma s := by
    rw [norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp (sphereMap A q).property,
      mul_one, abs_of_pos (hpositive s hs)]
  have hdomain {s : ℝ} (hs : s ∈ Ioo v L) :
      s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    exact ⟨hv.1.trans hs.1, hs.2⟩
  have hradial (z : E3) (hz : ‖z‖ ∈ sigma.target) :
      ∃ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo v L ∧ sigma s = ‖z‖ ∧
        (Phi.symm z).val = N.coordinate_map (q, s) ∧
        z = sigma s • (sphereMap A q).val := by
    let s := sigma.symm ‖z‖
    have hs : s ∈ Ioo v L := by
      simpa only [hsrc] using sigma.map_target hz
    have heq : sigma s = ‖z‖ := sigma.right_inv hz
    have hn : 0 < ‖z‖ := by
      have hnr : r0 < ‖z‖ := by simpa only [htgt, mem_Ioi] using hz
      exact hr0.trans hnr
    let q : UnitTwoSphere := ⟨A.symm (‖z‖⁻¹ • z), by
      rw [mem_sphere_zero_iff_norm, A.symm.norm_map, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']⟩
    have hq : (sphereMap A q).val = ‖z‖⁻¹ • z := A.apply_symm_apply _
    have hzrad : z = sigma s • (sphereMap A q).val := by
      rw [heq, hq, smul_inv_smul₀ hn.ne']
    let x : U := ⟨N.coordinate_map (q, s),
      C.end_chart_target_subset (N.coordinate_map_mem ⟨mem_univ _, hdomain hs⟩)⟩
    have hPhi : Phi x = z := (hformula q s x hs rfl).trans hzrad.symm
    have hxeq : Phi.symm z = x := by
      apply Phi.injective
      change Phi (Phi.symm z) = Phi x
      rw [Phi.apply_symm_apply, hPhi]
    exact ⟨q, s, hs, heq, congrArg Subtype.val hxeq, hzrad⟩
  have htail (t : ℝ) (ht : t ∈ Ioo v L) :
      Phi '' ((Subtype.val : U → M) ⁻¹' (N.region t L)) =
        {z : E3 | sigma t < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hs : (N.coordinate_inverse x.val).2 ∈ Ioo v L :=
        ⟨ht.1.trans hx.2.1, hx.2.2⟩
      have hf := hformula (N.coordinate_inverse x.val).1 (N.coordinate_inverse x.val).2
        x hs (N.coordinate_map_inverse hx.1).symm
      change sigma t < ‖Phi x‖
      rw [hf, hnorm _ _ hs]
      exact hmono' ht hs hx.2.1
    · intro hz
      have hzt : ‖z‖ ∈ sigma.target := by
        rw [htgt]
        exact (hradius t ht).trans hz
      obtain ⟨q, s, hs, heq, hpoint, _⟩ := hradial z hzt
      have hts : t < s := by
        by_contra hnot
        have hle := hmono'.monotoneOn hs ht (le_of_not_gt hnot)
        rw [heq] at hle
        exact (not_le_of_gt hz) hle
      refine ⟨Phi.symm z, ?_, Phi.apply_symm_apply z⟩
      change (Phi.symm z).val ∈ N.region t L
      rw [hpoint]
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hdomain hs⟩, ?_⟩
      rw [N.coordinate_inverse_map (q, s) (hdomain hs)]
      exact ⟨hts, hs.2⟩
  have hcut (t : ℝ) (ht : t ∈ Ioo v L) :
      Phi '' ((Subtype.val : U → M) ⁻¹' (K t)) = closedBall 0 (sigma t) := by
    have hcomp : (Subtype.val : U → M) ⁻¹' (K t) =
        ((Subtype.val : U → M) ⁻¹' (N.region t L))ᶜ := by
      ext x
      change (x.val ∈ C.carrier ∧ x.val ∉ N.region t L) ↔ x.val ∉ N.region t L
      exact ⟨fun hx => hx.2, fun hx => ⟨x.property, hx⟩⟩
    have hPhi : Phi '' (((Subtype.val : U → M) ⁻¹' (N.region t L))ᶜ) =
        (Phi '' ((Subtype.val : U → M) ⁻¹' (N.region t L)))ᶜ := by
      simpa only [Diffeomorph.coe_toHomeomorph] using
        Phi.toHomeomorph.image_compl ((Subtype.val : U → M) ⁻¹' (N.region t L))
    rw [hcomp, hPhi, htail t ht]
    ext z
    simp only [mem_compl_iff, mem_ofPred_eq, not_lt, mem_closedBall_zero_iff]
  have hopen (t : ℝ) (ht : t ∈ Ioo v L) :
      Phi '' ((Subtype.val : U → M) ⁻¹' interior (K t)) = ball 0 (sigma t) := by
    have hval : IsOpenMap (Subtype.val : U → M) :=
      C.carrier_open.isOpenEmbedding_subtypeVal.isOpenMap
    have hPhi : Phi '' interior ((Subtype.val : U → M) ⁻¹' (K t)) =
        interior (Phi '' ((Subtype.val : U → M) ⁻¹' (K t))) := by
      simpa only [Diffeomorph.coe_toHomeomorph] using
        Phi.toHomeomorph.image_interior ((Subtype.val : U → M) ⁻¹' (K t))
    rw [hval.preimage_interior_eq_interior_preimage continuous_subtype_val, hPhi, hcut t ht,
      interior_closedBall (0 : E3) (hpositive t ht).ne']
  have ha : a ∈ Ioo v L := ⟨hva, hab.trans hb⟩
  have hb' : b ∈ Ioo v L := ⟨hva.trans hab, hb⟩
  let hU : Nonempty U := ⟨Phi.symm 0⟩
  let e := U.openPartialHomeomorphSubtypeCoe hU
  let J := e.symm.trans Phi.toHomeomorph.toOpenPartialHomeomorph
  have hEt : e.target = C.carrier := U.openPartialHomeomorphSubtypeCoe_target hU
  have hJs : J.source = C.carrier := by
    change e.target ∩ e.symm ⁻¹' univ = C.carrier
    rw [preimage_univ, inter_univ, hEt]
  have hJf (x : U) : J x.val = Phi x := by
    change Phi (e.symm x.val) = Phi x
    congr 1
    exact e.left_inv (show x ∈ e.source from mem_univ _)
  let I := J.restrOpen (interior (K b)) isOpen_interior
  have hIs : I.source = interior (K b) := by
    change J.source ∩ interior (K b) = interior (K b)
    rw [hJs]
    exact inter_eq_right.mpr (interior_subset.trans sdiff_subset)
  have hIf (x : U) : I x.val = Phi x := hJf x
  have hIi (z : E3) : I.symm z = (Phi.symm z).val := rfl
  have hIt : I.target = ball 0 (sigma b) := by
    rw [← I.image_source_eq_target, hIs]
    have himage : I '' interior (K b) =
        Phi '' ((Subtype.val : U → M) ⁻¹' interior (K b)) := by
      ext z
      constructor
      · rintro ⟨x, hx, hxeq⟩
        let y : U := ⟨x, (interior_subset hx).1⟩
        exact ⟨y, hx, (hIf y).symm.trans hxeq⟩
      · rintro ⟨x, hx, hxeq⟩
        exact ⟨x.val, hx, (hIf x).trans hxeq⟩
    exact himage.trans (hopen b hb')
  have he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm C.carrier := by
    have hcomp : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (Subtype.val ∘ e.symm) C.carrier :=
      contMDiff_id.contMDiffOn.congr (fun x hx => e.right_inv (hEt.symm ▸ hx))
    intro x hx
    exact (ContMDiffWithinAt.subtypeVal_comp_iff U e.symm C.carrier x).mp (hcomp x hx)
  have hI : ContMDiffOn (𝓡 3) (𝓡 3) ∞ I I.source := by
    have hJ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ J C.carrier :=
      Phi.contMDiff.comp_contMDiffOn he
    exact hJ.mono (hIs ▸ interior_subset.trans sdiff_subset)
  have hiI : ContMDiffOn (𝓡 3) (𝓡 3) ∞ I.symm I.target :=
    (contMDiff_subtype_val.comp Phi.symm.contMDiff).contMDiffOn
  have hannulus : I '' (N.region a b) =
      {z : E3 | sigma a < ‖z‖ ∧ ‖z‖ < sigma b} := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      let y : U := ⟨x, C.end_chart_target_subset hx.1⟩
      have hs : (N.coordinate_inverse x).2 ∈ Ioo v L :=
        ⟨hva.trans hx.2.1, hx.2.2.trans hb⟩
      have hf := (hIf y).trans (hformula (N.coordinate_inverse x).1
        (N.coordinate_inverse x).2 y hs (N.coordinate_map_inverse hx.1).symm)
      change sigma a < ‖I x‖ ∧ ‖I x‖ < sigma b
      rw [hf, hnorm _ _ hs]
      exact ⟨hmono' ha hs hx.2.1, hmono' hs hb' hx.2.2⟩
    · intro hz
      have hzt : ‖z‖ ∈ sigma.target := by
        rw [htgt]
        exact (hradius a ha).trans hz.1
      obtain ⟨q, s, hs, heq, hpoint, _⟩ := hradial z hzt
      have hsa : a < s := by
        by_contra hnot
        have hle := hmono'.monotoneOn hs ha (le_of_not_gt hnot)
        rw [heq] at hle
        exact (not_le_of_gt hz.1) hle
      have hsb : s < b := by
        by_contra hnot
        have hle := hmono'.monotoneOn hb' hs (le_of_not_gt hnot)
        rw [heq] at hle
        exact (not_le_of_gt hz.2) hle
      refine ⟨(Phi.symm z).val, ?_, (hIf (Phi.symm z)).trans (Phi.apply_symm_apply z)⟩
      rw [hpoint]
      refine ⟨N.coordinate_map_mem ⟨mem_univ _, hdomain hs⟩, ?_⟩
      rw [N.coordinate_inverse_map (q, s) (hdomain hs)]
      exact ⟨hsa, hsb⟩
  refine ⟨Phi, A, r0, sigma, I, hr0, hsrc, htgt, hsmooth, hismooth, hmono, hderiv,
    hformula, fun t ht => ⟨htail t ht, hcut t ht, hopen t ht⟩,
    hIs, hIt, hI, hiI, fun x _ => hIf x, fun z _ => hIi z, hannulus, ?_⟩
  intro q s hs
  have hs' : s ∈ Ioo v L := ⟨hva.trans hs.1, hs.2.trans hb⟩
  have hxN : N.coordinate_map (q, s) ∈ N.end_chart.target :=
    N.coordinate_map_mem ⟨mem_univ _, hdomain hs'⟩
  let x : U := ⟨N.coordinate_map (q, s), C.end_chart_target_subset hxN⟩
  have hxI : N.coordinate_map (q, s) ∈ I.source := by
    rw [hIs]
    have hcutb := (C.end_neck_lower_cut_topology
      (show b ∈ Ioo (-C.epsilon⁻¹) C.epsilon⁻¹ from ⟨hv.1.trans hb'.1, hb⟩)).2.2.2.1
    rw [hcutb]
    apply Or.inr
    refine ⟨hxN, ?_⟩
    rw [N.coordinate_inverse_map (q, s) (hdomain hs')]
    exact ⟨hv.1.trans hs'.1, hs.2⟩
  have hforward : I (N.coordinate_map (q, s)) = sigma s • (sphereMap A q).val :=
    (hIf x).trans (hformula q s x hs' rfl)
  have htarget := I.map_source hxI
  rw [hforward] at htarget
  have hinverse := I.left_inv hxI
  rw [hforward] at hinverse
  exact ⟨hxI, hforward, htarget, hinverse⟩

end PoincareConjecture.M25.Topology3D
