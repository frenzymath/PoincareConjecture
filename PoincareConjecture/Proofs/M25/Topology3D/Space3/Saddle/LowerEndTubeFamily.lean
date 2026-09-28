import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.LowerEndTubePrimitives
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.PieceData
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SourceCircleChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.CollarHeight
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsFamily








set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Manifold InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem exists_saddle_cap_source_annulus
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (C : SurgeryCapTag psi u) (hsign : C.sign = 1) :
    let ell := C.cutHeight + C.removal
    ∃ (d : ℝ) (Q : OpenPartialHomeomorph (UnitCircle × ℝ) UnitTwoSphere),
      0 < d ∧ Q.source = (univ : Set UnitCircle) ×ˢ Ioo (ell - d) (ell + d) ∧
      ContMDiffOn ((𝓡 1).prod 𝓘(ℝ, ℝ)) (𝓡 2) ∞ Q Q.source ∧
      ContMDiffOn (𝓡 2) ((𝓡 1).prod 𝓘(ℝ, ℝ)) ∞ Q.symm Q.target ∧
      (∀ p ∈ Q.source, ⟪(u : E3), psi (Q p, 0)⟫_ℝ = p.2) ∧
      (∀ theta : UnitCircle, ∀ z ∈ Ioo (ell - d) (ell + d),
        psi (Q (theta, z), 0) = C.tube (theta.1, z)) ∧
      range (fun theta : UnitCircle => Q (theta, ell)) = C.sourceSeam := by
  classical
  let ell := C.cutHeight + C.removal
  let d := C.scale * C.overlapWidth / 4
  have hd : 0 < d := div_pos (mul_pos C.scale_pos C.overlap_pos) (by norm_num)
  let J := Ioo (ell - d) (ell + d)
  have hjinj : Injective (fun q : UnitTwoSphere => psi (q, 0)) := by
    intro q r hqr
    exact congrArg Prod.fst (hpsi.2.1 (x₁ := (q, 0)) (x₂ := (r, 0))
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hqr)
  have hnative (theta : UnitCircle) (v : ℝ) (hv : |v| ≤ 1 / 4) :
      ∃ q : UnitTwoSphere,
        (heightCoordinates (q : E3)).2 = v ∧ C.profile.model q = (theta.1, v) := by
    have hpos : 0 < 1 - v ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
    let x := heightCoordinates.symm (Real.sqrt (1 - v ^ 2) • theta.1, v)
    have hnorm : ‖x‖ = 1 := by
      have hsq : ‖x‖ ^ 2 = 1 := by
        dsimp only [x]
        rw [heightCoordinates_symm_norm_sq, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _), norm_eq_of_mem_sphere theta, mul_one,
          Real.sq_sqrt hpos.le]
        ring
      nlinarith [norm_nonneg x]
    let q : UnitTwoSphere := ⟨x, mem_sphere_zero_iff_norm.mpr hnorm⟩
    have hcoords : heightCoordinates (q : E3) =
        (Real.sqrt (1 - v ^ 2) • theta.1, v) := heightCoordinates.apply_symm_apply _
    refine ⟨q, congrArg Prod.snd hcoords, ?_⟩
    change flatCapDiffeomorph C.profile.horizontal C.profile.vertical
      C.profile.horizontal_smooth C.profile.vertical_smooth
      (fun z => (C.profile.horizontal_pos z).ne')
      (fun x => (C.profile.vertical_pos x).ne') (heightCoordinates (q : E3)) = _
    rw [hcoords]
    exact flatCapDiffeomorph_cylinder C.profile.horizontal C.profile.vertical
      C.profile.horizontal_smooth C.profile.vertical_smooth
      (fun z => (C.profile.horizontal_pos z).ne')
      (fun x => (C.profile.vertical_pos x).ne') C.profile.horizontal_near
      C.profile.vertical_far theta.1 (norm_eq_of_mem_sphere theta) v hv
  have hboundary (theta : UnitCircle) (z : ℝ) (hz : z ∈ J) :
      C.tube (theta.1, z) ∈ range (fun q : UnitTwoSphere => psi (q, 0)) := by
    let v := (z - ell) / C.scale
    have hv : |v| < C.overlapWidth / 4 := by
      rw [show |v| = |z - ell| / C.scale by
        dsimp [v]; rw [abs_div, abs_of_pos C.scale_pos]]
      apply (div_lt_iff₀ C.scale_pos).mpr
      have habs : |z - ell| < d := abs_lt.mpr ⟨by linarith [hz.1], by linarith [hz.2]⟩
      dsimp [d] at habs
      nlinarith
    obtain ⟨q, hqz, hqmodel⟩ := hnative theta v (by linarith [C.overlap_le])
    refine ⟨C.sourceChart q, ?_⟩
    change psi (C.sourceChart q, 0) = C.tube (theta.1, z)
    rw [C.central_eq q (by rw [hqz]; exact (le_abs_self v).trans_lt (by
      linarith [C.overlap_pos])), SurgeryCapProfile.capMap_apply, hqmodel, hsign]
    congr 1
    apply Prod.ext
    · rfl
    · dsimp [ell, v]
      field_simp [C.scale_pos.ne']
      ring
  have hsource : sphere (0 : E2) 1 ×ˢ J ⊆ C.tube.source :=
    fun p hp => C.tube_source ⟨sphere_subset_closedBall hp.1, mem_univ _⟩
  obtain ⟨Q, hQs, hQsm, hQim, hQ⟩ := exists_source_tube_chart psi hpsi C.tube
    C.tube_smooth C.tube_inverse isOpen_Ioo hsource hboundary
  have hell : ell ∈ J := ⟨by linarith, by linarith⟩
  have hQheight (p : UnitCircle × ℝ) (hp : p ∈ Q.source) :
      ⟪(u : E3), psi (Q p, 0)⟫_ℝ = p.2 := by
    have hpJ : p.2 ∈ J := (hQs ▸ hp).2
    rw [hQ p.1 p.2 hpJ]
    exact C.tube_height _ (C.tube_source ⟨sphere_subset_closedBall p.1.2, mem_univ _⟩)
  refine ⟨d, Q, hd, hQs, hQsm, hQim, hQheight, hQ, ?_⟩
  ext p
  constructor
  · rintro ⟨theta, rfl⟩
    obtain ⟨q, hqz, hqmodel⟩ := hnative theta 0 (by norm_num)
    refine ⟨q, hqz, ?_⟩
    apply hjinj
    change psi (C.sourceChart q, 0) = psi (Q (theta, ell), 0)
    rw [C.central_eq q (by rw [hqz]; exact C.overlap_pos),
      SurgeryCapProfile.capMap_apply, hqmodel, hsign, hQ theta ell hell]
    simp only [mul_zero, add_zero, one_mul, ell]
  · rintro ⟨q, hq, rfl⟩
    change (heightCoordinates (q : E3)).2 = 0 at hq
    let theta := circleDirection (heightCoordinates (q : E3)).1
    have hmodel : C.profile.model q = (theta.1, 0) := by
      have hm := surgeryCapModel_cylinder C.profile.horizontal C.profile.vertical
        C.profile.horizontal_smooth C.profile.vertical_smooth
        (fun z => (C.profile.horizontal_pos z).ne')
        (fun x => (C.profile.vertical_pos x).ne') C.profile.horizontal_near
        C.profile.vertical_far q (by rw [hq]; norm_num)
      simpa only [SurgeryCapProfile.model, theta, hq] using hm
    refine ⟨theta, hjinj ?_⟩
    change psi (Q (theta, ell), 0) = psi (C.sourceChart q, 0)
    rw [hQ theta ell hell, C.central_eq q (by rw [hq]; exact C.overlap_pos),
      SurgeryCapProfile.capMap_apply, hmodel, hsign]
    simp only [mul_zero, add_zero, one_mul, ell]


set_option linter.unusedVariables false in


theorem exists_saddle_lower_end_family
    (hP : PlanarSchoenfliesService)
    (psi : UnitTwoSphere × ℝ → E3) (hpsi : IsCollarEmbedding psi)
    (u : UnitTwoSphere) (D : SaddlePieceData psi u)
    (W : SaddleLowerLevelData D) (i : Fin 2) :
    let C := D.cap (W.label i)
    let ell := C.cutHeight + C.removal
    let L := heightPlaneCoordinates u
    ∃ (eta d : ℝ) (c : ℝ → UnitCircle → E2)
      (F : PlanarSchoenfliesFamilyData c (ell - 2 * eta) (W.level + 2 * eta))
      (G : PlanarFamilyGraphChart F),
      0 < eta ∧ 0 < d ∧ d < eta ∧
      ((univ : Set UnitCircle) ×ˢ Icc (ell - 3 * eta) (W.level + 3 * eta) ⊆
        (W.leg i).source) ∧
      (∀ z ∈ Icc (ell - 2 * eta) (W.level + 2 * eta), ∀ q : UnitCircle,
        c z q = (L (psi (W.leg i (q, z), 0))).1) ∧
      (∀ z ∈ Icc (ell - d) (ell + d),
        range (fun q : UnitCircle => (L (C.tube (q.1, z))).1) = range (c z)) := by
  classical
  let C := D.cap (W.label i)
  let ell := C.cutHeight + C.removal
  let L := heightPlaneCoordinates u
  let j : UnitTwoSphere → E3 := fun q => psi (q, 0)
  have hsign : C.sign = 1 := W.label_lower i
  have hell : ell < W.level := by
    have h := W.lower_seams_lt_level (W.label i) hsign
    change C.cutHeight + C.sign * C.removal < W.level at h
    simpa only [hsign, one_mul] using h
  have hlegsource : (univ : Set UnitCircle) ×ˢ Icc ell W.level ⊆ (W.leg i).source := by
    have h := W.leg_source i
    change (univ : Set UnitCircle) ×ˢ Icc (C.cutHeight + C.sign * C.removal) W.level ⊆
      (W.leg i).source at h
    simpa only [hsign, one_mul] using h
  obtain ⟨s, hs, hsleg⟩ := exists_saddle_end_circle_buffer
    (W.leg i).source (W.leg i).open_source ell W.level hell.le hlegsource
  let eta := s / 8
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hband : (univ : Set UnitCircle) ×ˢ
      Icc (ell - 3 * eta) (W.level + 3 * eta) ⊆ (W.leg i).source := by
    intro p hp
    apply hsleg
    refine ⟨hp.1, ?_, ?_⟩ <;> dsimp [eta] at * <;> linarith [hp.2.1, hp.2.2]
  obtain ⟨k, hk, hkrange, hkfix⟩ := exists_saddle_end_height_clamp
    (ell - 3 * eta) (W.level + 3 * eta) (eta / 2) (by linarith) (by positivity)
  have hkleg (z : ℝ) (q : UnitCircle) : (q, k z) ∈ (W.leg i).source := by
    apply hsleg
    have hz := hkrange z
    refine ⟨mem_univ _, ?_, ?_⟩ <;> dsimp [eta] at * <;> linarith [hz.1, hz.2]
  have hj : ContMDiff (𝓡 2) 𝓘(ℝ, E3) ∞ j := collar_central_contMDiff psi hpsi
  have hji : Injective j := by
    intro q r hqr
    exact congrArg Prod.fst (hpsi.2.1 (x₁ := (q, 0)) (x₂ := (r, 0))
      ⟨mem_univ _, by norm_num⟩ ⟨mem_univ _, by norm_num⟩ hqr)
  let c : ℝ → UnitCircle → E2 := fun z q => (L (j (W.leg i (q, k z)))).1
  have hc : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) 𝓘(ℝ, E2) ∞
      (fun p : ℝ × UnitCircle => c p.1 p.2) := by
    have hq : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 1)) (𝓡 2) ∞
        (fun p : ℝ × UnitCircle => W.leg i (p.2, k p.1)) := by
      apply contMDiffOn_univ.mp
      exact (W.leg_smooth i).comp
        (contMDiff_snd.prodMk (hk.contMDiff.comp contMDiff_fst)).contMDiffOn
        (fun p _ => hkleg p.1 p.2)
    exact contDiff_fst.contMDiff.comp (L.contDiff.contMDiff.comp (hj.comp hq))
  have hcEq (z : ℝ) (hz : z ∈ Icc (ell - 2 * eta) (W.level + 2 * eta))
      (q : UnitCircle) : c z q = (L (j (W.leg i (q, z)))).1 := by
    have hzfix : z ∈ Icc (ell - 3 * eta) (W.level + 3 * eta) := by
      constructor <;> linarith [hz.1, hz.2]
    dsimp only [c]
    rw [hkfix hzfix, id_eq]
  have hcemb (z : ℝ) (hz : z ∈ Icc (ell - 2 * eta) (W.level + 2 * eta)) :
      IsPlanarEmbedding (c z) := by
    have hzs (q : UnitCircle) : (q, z) ∈ (W.leg i).source :=
      hband ⟨mem_univ _, by constructor <;> linarith [hz.1, hz.2]⟩
    obtain ⟨hsm, hinj, himm⟩ := source_collar_slice_smooth_immersion
      (W.leg i) (W.leg_smooth i) (W.leg_inverse i) z hzs
    let v : UnitCircle → E3 := fun q => j (W.leg i (q, z))
    have hv : ContMDiff (𝓡 1) 𝓘(ℝ, E3) ∞ v := hj.comp hsm
    have hvi : Injective v := hji.comp hinj
    have hvd (q : UnitCircle) : Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3) v q) := by
      change Injective (mfderiv (𝓡 1) 𝓘(ℝ, E3)
        (j ∘ fun q => W.leg i (q, z)) q)
      rw [mfderiv_comp q (hj.mdifferentiable (by simp) _)
        (hsm.mdifferentiable (by simp) q)]
      exact (collar_central_mfderiv_injective psi hpsi _).comp (himm q)
    have hvh (q : UnitCircle) : ⟪(u : E3), v q⟫_ℝ = z := W.leg_height i _ (hzs q)
    have h := isPlanarEmbedding_height_projection u v hv hvi hvd z hvh
    have hceq : c z = fun q => (L (v q)).1 := funext (hcEq z hz)
    rw [hceq]
    exact h
  obtain ⟨F⟩ := hP.2 (ell - 2 * eta) (W.level + 2 * eta) c
    (by linarith) hc hcemb
  obtain ⟨G⟩ := F.nonempty_graphChart (by linarith)
  obtain ⟨d0, Q, hd0, hQs, _, _, hQh, hQ, hQbottom⟩ :=
    exists_saddle_cap_source_annulus psi hpsi u C hsign
  have hQ0 (q : UnitCircle) : (q, ell) ∈ Q.source := by
    rw [hQs]
    exact ⟨mem_univ _, by linarith, by linarith⟩
  have hW0 (q : UnitCircle) : (q, ell) ∈ (W.leg i).source :=
    hlegsource ⟨mem_univ _, le_rfl, hell.le⟩
  have hbottom : range (fun q : UnitCircle => Q (q, ell)) =
      range (fun q : UnitCircle => W.leg i (q, ell)) := by
    rw [hQbottom]
    have hw := W.leg_bottom i
    change range (fun q : UnitCircle => W.leg i (q, C.cutHeight + C.sign * C.removal)) =
      C.sourceSeam at hw
    simpa only [hsign, one_mul] using hw.symm
  obtain ⟨d1, hd1, h1Q, _, hcircles⟩ := exists_saddle_end_common_circles
    Q (W.leg i) (fun q => ⟪(u : E3), j q⟫_ℝ) ell hQh
    (W.leg_height i) hQ0 hW0 hbottom
  let d := min d1 (eta / 2)
  have hd : 0 < d := lt_min hd1 (by positivity)
  have hdeta : d < eta := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  refine ⟨eta, d, c, F, G, heta, hd, hdeta, hband, hcEq, ?_⟩
  intro z hz
  have hz1 : z ∈ Icc (ell - d1) (ell + d1) := by
    constructor <;> linarith [min_le_left d1 (eta / 2), hz.1, hz.2]
  have hzF : z ∈ Icc (ell - 2 * eta) (W.level + 2 * eta) := by
    constructor <;> linarith [hz.1, hz.2]
  have hzJ : z ∈ Ioo (ell - d0) (ell + d0) := by
    have q : UnitCircle := Classical.choice
      ((NormedSpace.sphere_nonempty (E := E2) (x := 0)).mpr zero_le_one).coe_sort
    have hp : (q, z) ∈ Q.source := h1Q ⟨mem_univ q, hz1⟩
    exact (hQs ▸ hp).2
  calc
    range (fun q : UnitCircle => (L (C.tube (q.1, z))).1) =
        (fun p : UnitTwoSphere => (L (j p)).1) ''
          range (fun q : UnitCircle => Q (q, z)) := by
      rw [← range_comp]
      congr 1
      funext q
      exact congrArg (fun y : E3 => (L y).1) (hQ q z hzJ).symm
    _ = (fun p : UnitTwoSphere => (L (j p)).1) ''
        range (fun q : UnitCircle => W.leg i (q, z)) := by rw [hcircles z hz1]
    _ = range (c z) := by
      rw [← range_comp]
      congr 1
      exact (funext (hcEq z hzF)).symm

end PoincareConjecture.M25.Topology3D
