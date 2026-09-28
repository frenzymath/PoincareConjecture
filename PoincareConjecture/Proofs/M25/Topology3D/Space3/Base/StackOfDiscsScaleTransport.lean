import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsScaleEvolution
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTransport

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold InnerProductSpace Topology

namespace PoincareConjecture.M25.Topology3D

variable {psi : UnitTwoSphere × ℝ → E3} {u : UnitTwoSphere}

theorem exists_stackCapScaleTransport (C : SurgeryCapTag psi u)
    (hpsi : IsCollarEmbedding psi) (K L : Set E3) (hK : IsCompact K) (hL : IsCompact L)
    (gap lambda : ℝ) (hgap : 0 < gap) (hlambda : 0 < lambda)
    (hsmall : lambda < C.scale)
    (hcover : range (fun q => psi (q, 0)) = K ∪ C.cap ∪ L)
    (hseam : C.seam ⊆ K)
    (hKside : ∀ y ∈ K, 0 ≤ C.sign * (inner ℝ (u : E3) y -
      (C.cutHeight + C.sign * C.removal)))
    (hLside : ∀ y ∈ L, gap ≤ C.sign * (inner ℝ (u : E3) y -
      (C.cutHeight + C.sign * C.removal))) :
    ∃ F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞, ∃ S : Set E3,
      ∃ Cnew : SurgeryCapTag (fun p => F (psi p)) u,
      IsCollarEmbedding (fun p => F (psi p)) ∧ IsCompact S ∧ Disjoint S L ∧
      tsupport (fun y => F y - y) ⊆ S ∧
      tsupport (fun y => F.symm y - y) ⊆ S ∧
      (∀ y, y ∉ S → F y = y ∧ F.symm y = y) ∧
      F '' K = K ∧ F.symm '' K = K ∧
      (∀ y ∈ C.seam, F y = y ∧ F.symm y = y) ∧
      Cnew.profile = C.profile ∧ Cnew.tube = C.tube ∧
      Cnew.cutHeight = C.cutHeight ∧ Cnew.removal = C.removal ∧
      Cnew.sign = C.sign ∧ Cnew.scale = lambda ∧
      Cnew.sourceChart = C.sourceChart ∧ Cnew.flatChart = C.flatChart ∧
      Cnew.beta = (lambda / C.scale) * C.beta ∧
      Cnew.overlapWidth ≤ C.overlapWidth ∧ Cnew.collarWidth ≤ C.collarWidth ∧
      Cnew.sourceCap = C.sourceCap ∧ Cnew.sourceSeam = C.sourceSeam ∧
      Cnew.cap = F '' C.cap ∧ Cnew.seam = C.seam ∧
      Cnew.cap = C.profile.capMap C.tube C.cutHeight C.sign C.removal lambda ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} ∧
      K ∩ Cnew.cap = Cnew.seam ∧ Disjoint Cnew.cap L ∧
      (∀ q : UnitTwoSphere, F (psi (q, 0)) ∈ K ↔ psi (q, 0) ∈ K) ∧
      range (fun q => F (psi (q, 0))) = K ∪ Cnew.cap ∪ L := by
  obtain ⟨Phi, S, N, d, o, w, _, _, _, hSc, _, _, _, _, _, _, _, hS,
    hsupp, hsuppi, hfix, hcore, hseamL, ho, hoo, hw, hwo, htrack, _, hflat⟩ :=
    exists_stackCapScaleEvolution C hpsi K L hK hL gap lambda hgap hlambda hsmall
      hcover hseam hKside hLside
  let F := Phi 1
  have htime : (1 : ℝ) ∈ Ioo (-1 : ℝ) 2 := by norm_num
  obtain ⟨_, _, _, _, _, hstart, hfinish, _, _, hnonpos, hzero, _⟩ :=
    stackCapScaleCap_spec C lambda hlambda hsmall
  have hcollar : IsCollarEmbedding (fun p => F (psi p)) := by
    refine ⟨F.contMDiff.comp_contMDiffOn hpsi.1, ?_, ?_⟩
    · intro x hx y hy hxy
      exact hpsi.2.1 hx hy (F.injective hxy)
    · intro p hp
      have hdpsi := (hpsi.1.contMDiffAt
        ((isOpen_univ.prod isOpen_Ioo).mem_nhds hp)).mdifferentiableAt (by simp)
      have hdF := (F.toOpenPartialHomeomorph_mdifferentiable (by simp)).mfderiv_injective
        (x := psi p) (mem_univ _)
      change Function.Injective
        (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, E3) ((F : E3 → E3) ∘ psi) p)
      rw [mfderiv_comp p (F.mdifferentiable (by simp) (psi p)) hdpsi]
      exact hdF.comp (hpsi.2.2 p hp)
  let Cnew : SurgeryCapTag (fun p => F (psi p)) u := {
    profile := C.profile
    cutHeight := C.cutHeight
    removal := C.removal
    scale := lambda
    sign := C.sign
    removal_pos := C.removal_pos
    scale_pos := hlambda
    sign_abs := C.sign_abs
    scale_small := (mul_lt_mul_of_pos_right hsmall
      (lt_of_lt_of_le zero_lt_one C.profile.one_le_heightBound)).trans C.scale_small
    tube := C.tube
    tube_source := C.tube_source
    tube_smooth := C.tube_smooth
    tube_inverse := C.tube_inverse
    tube_height := C.tube_height
    sourceChart := C.sourceChart
    source_smooth := C.source_smooth
    source_inverse := C.source_inverse
    overlapWidth := o
    overlap_pos := ho
    overlap_le := hoo.trans C.overlap_le
    source_band := fun q hq => C.source_band q (hq.trans_le hoo)
    central_eq := by
      intro q hq
      rw [C.central_eq q (hq.trans_le hoo)]
      exact (htrack 1 htime q hq).trans (hfinish q)
    flatChart := C.flatChart
    flat_source := C.flat_source
    flat_smooth := C.flat_smooth
    flat_inverse := C.flat_inverse
    flat_eq := C.flat_eq
    beta := lambda / C.scale * C.beta
    beta_ne := mul_ne_zero (div_ne_zero hlambda.ne' C.scale_pos.ne') C.beta_ne
    collarWidth := w
    collar_pos := hw
    collar_le := hwo.trans C.collar_le
    collar_eq := by
      intro x hx z hz
      rw [C.collar_eq x hx z (hz.trans_le hwo)]
      have hold : C.cutHeight + C.sign * (C.removal - C.scale) + C.beta * z =
          C.cutHeight + C.sign * C.removal - C.sign * C.scale + C.beta * z := by ring
      rw [hold]
      change Phi 1 _ = _
      rw [hflat 1 htime x hx z hz,
        (stackCapScale_spec C.scale lambda hlambda hsmall).2.2.2.2 1 le_rfl]
      congr 1
      apply Prod.ext
      · rfl
      · field_simp [C.scale_pos.ne']
        ring }
  have hSL : Disjoint S L := disjoint_left.mpr (fun _ hy hyl => (hS hy).2 (Or.inr hyl))
  have hFL : ∀ y ∈ L, F y = y := fun y hy => (hseamL 1 y (Or.inr hy)).1
  have hFS : ∀ y ∈ C.seam, F y = y := fun y hy => (hseamL 1 y (Or.inl hy)).1
  have hFimageL : F '' L = L := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [hFL x hx] using hx
    · intro hy
      exact ⟨y, hy, hFL y hy⟩
  have hcap : Cnew.cap = F '' C.cap := by
    change (fun q => F (psi (q, 0))) '' C.sourceCap =
      F '' ((fun q => psi (q, 0)) '' C.sourceCap)
    rw [image_image]
  have hnewseam : Cnew.seam = C.seam := by
    have heq : Cnew.seam = F '' C.seam := by
      change (fun q => F (psi (q, 0))) '' C.sourceSeam =
        F '' ((fun q => psi (q, 0)) '' C.sourceSeam)
      rw [image_image]
    rw [heq]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa only [hFS x hx] using hx
    · intro hy
      exact ⟨y, hy, hFS y hy⟩
  have hseamcap : C.seam ⊆ C.cap := by
    rw [C.seam_eq_image, C.cap_eq_image]
    exact image_mono (fun q hq => hq.le)
  have hcapK : K ∩ C.cap = C.seam := by
    apply Subset.antisymm
    · rintro y ⟨hyK, hycap⟩
      rw [C.cap_eq_image] at hycap
      obtain ⟨q, hq, rfl⟩ := hycap
      have hn := hnonpos 0 q hq
      rw [hstart q] at hn
      have hz : C.sign * (inner ℝ (u : E3)
          (C.profile.capMap C.tube C.cutHeight C.sign C.removal C.scale q) -
          (C.cutHeight + C.sign * C.removal)) = 0 := le_antisymm hn (hKside _ hyK)
      have hq0 := (hzero 0 q hq).mp (by simpa only [hstart q] using hz)
      rw [C.seam_eq_image]
      exact ⟨q, hq0, rfl⟩
    · exact fun _ hy => ⟨hseam hy, hseamcap hy⟩
  have hcapL : Disjoint C.cap L := by
    apply disjoint_left.mpr
    intro y hy hyL
    rw [C.cap_eq_image] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    have hn := hnonpos 0 q hq
    rw [hstart q] at hn
    exact (not_le_of_gt hgap) ((hLside _ hyL).trans hn)
  have hcoreiff (y : E3) : F y ∈ K ↔ y ∈ K := by
    constructor
    · intro hy
      have hi : F.symm (F y) ∈ F.symm '' K := ⟨F y, hy, rfl⟩
      rw [(hcore 1).2] at hi
      simpa only [Diffeomorph.symm_apply_apply] using hi
    · intro hy
      rw [← (hcore 1).1]
      exact ⟨y, hy, rfl⟩
  have hnewinter : K ∩ Cnew.cap = Cnew.seam := by
    rw [hcap, hnewseam]
    apply Subset.antisymm
    · rintro y ⟨hyK, x, hx, rfl⟩
      have hxS : x ∈ C.seam := hcapK ▸ ⟨(hcoreiff x).mp hyK, hx⟩
      simpa only [hFS x hxS] using hxS
    · intro y hy
      exact ⟨hseam hy, y, hseamcap hy, hFS y hy⟩
  have hnewL : Disjoint Cnew.cap L := by
    rw [hcap]
    apply disjoint_left.mpr
    rintro y ⟨x, hx, rfl⟩ hyL
    have hxy : x = F x := F.injective (hFL (F x) hyL).symm
    exact disjoint_left.mp hcapL hx (hxy.symm ▸ hyL)
  refine ⟨F, S, Cnew, hcollar, hSc, hSL, hsupp 1, hsuppi 1, hfix 1,
    (hcore 1).1, (hcore 1).2, (fun y hy => hseamL 1 y (Or.inl hy)),
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hoo, hwo, rfl, rfl,
    hcap, hnewseam, Cnew.cap_eq_image, hnewinter, hnewL,
    (fun q => hcoreiff (psi (q, 0))), ?_⟩
  calc
    range (fun q => F (psi (q, 0))) = F '' range (fun q => psi (q, 0)) :=
      range_comp' F (fun q => psi (q, 0))
    _ = K ∪ Cnew.cap ∪ L := by
      rw [hcover, image_union, image_union, (hcore 1).1, ← hcap, hFimageL]

theorem exists_stackCapTag_transport_of_fixed_neighborhood
    (D : SurgeryCapTag psi u)
    (F : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) E3 E3 ∞) (U : Set E3)
    (hU : IsOpen U) (hcap : D.cap ⊆ U) (hfix : ∀ y ∈ U, F y = y) :
    ∃ Dnew : SurgeryCapTag (fun p => F (psi p)) u,
      Dnew.profile = D.profile ∧ Dnew.tube = D.tube ∧
      Dnew.cutHeight = D.cutHeight ∧ Dnew.removal = D.removal ∧
      Dnew.sign = D.sign ∧ Dnew.scale = D.scale ∧ Dnew.beta = D.beta ∧
      Dnew.sourceChart = D.sourceChart ∧ Dnew.flatChart = D.flatChart ∧
      Dnew.overlapWidth ≤ D.overlapWidth ∧ Dnew.collarWidth ≤ D.collarWidth ∧
      Dnew.sourceCap = D.sourceCap ∧ Dnew.sourceSeam = D.sourceSeam ∧
      Dnew.cap = D.cap ∧ Dnew.seam = D.seam := by
  let cap := D.profile.capMap D.tube D.cutHeight D.sign D.removal D.scale
  have hcapcont : Continuous cap :=
    (D.profile.capMap_contMDiff D.tube D.tube_source D.tube_smooth
      D.cutHeight D.sign D.removal D.scale).continuous
  have hh : Continuous (fun q : UnitTwoSphere => -(heightCoordinates (q : E3)).2) :=
    ((heightCoordinates.continuous.comp continuous_subtype_val).snd).neg
  have hhalf : {q : UnitTwoSphere | 0 ≤ -(heightCoordinates (q : E3)).2} ⊆ cap ⁻¹' U := by
    intro q hq
    apply hcap
    rw [D.cap_eq_image]
    change 0 ≤ -(heightCoordinates (q : E3)).2 at hq
    exact ⟨q, neg_nonneg.mp hq, rfl⟩
  obtain ⟨o0, ho0, hband⟩ :=
    exists_uniform_upper_level_band _ hh (hU.preimage hcapcont) hhalf
  let X := closedBall (0 : E2) (1 / 8)
  let Z := Icc (-1 : ℝ) 1
  let : CompactSpace X := isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : E2) (1 / 8))
  let : CompactSpace Z := isCompact_iff_compactSpace.mp (isCompact_Icc : IsCompact Z)
  let g : X × Z → E3 := fun p =>
    D.tube (p.1, D.cutHeight + D.sign * (D.removal - D.scale) + D.beta * p.2)
  have hx : Continuous (fun p : X × Z => (p.1 : E2)) :=
    (continuous_fst : Continuous (Prod.fst : X × Z → X)).subtype_val
  have hz : Continuous (fun p : X × Z => (p.2 : ℝ)) :=
    (continuous_snd : Continuous (Prod.snd : X × Z → Z)).subtype_val
  have hg : Continuous g := D.tube.continuousOn.comp_continuous
    (hx.prodMk (continuous_const.add (continuous_const.mul hz))) (by
      intro p
      exact D.tube_source ⟨mem_closedBall_zero_iff.mpr
        ((mem_closedBall_zero_iff.mp p.1.2).trans (by norm_num)), mem_univ _⟩)
  have hcenter : {p : X × Z | (p.2 : ℝ) = 0} ⊆ g ⁻¹' U := by
    intro p hp
    have hxn : ‖(p.1 : E2)‖ ≤ 1 / 8 := mem_closedBall_zero_iff.mp p.1.2
    change D.tube ((p.1 : E2),
      D.cutHeight + D.sign * (D.removal - D.scale) + D.beta * p.2) ∈ U
    change (p.2 : ℝ) = 0 at hp
    rw [hp, ← D.collar_eq (p.1 : E2) hxn 0 (by simpa only [abs_zero] using D.collar_pos)]
    exact hcap ⟨D.flatChart (p.1 : E2),
      D.flatChart_mem_sourceCap _ (hxn.trans (by norm_num)), rfl⟩
  obtain ⟨w0, hw0, hflatband⟩ :=
    exists_uniform_zero_level_band _ hz (hU.preimage hg) hcenter
  let o := min o0 D.overlapWidth
  let w := min w0 D.collarWidth
  have ho : 0 < o := lt_min ho0 D.overlap_pos
  have hw : 0 < w := lt_min hw0 D.collar_pos
  have hflatU (x : E2) (hx : ‖x‖ ≤ 1 / 8) (z : ℝ) (hz : |z| < w) :
      D.tube (x, D.cutHeight + D.sign * (D.removal - D.scale) + D.beta * z) ∈ U := by
    have hz1 : |z| < 1 := hz.trans_le ((min_le_right w0 D.collarWidth).trans D.collar_le)
    exact hflatband (⟨x, mem_closedBall_zero_iff.mpr hx⟩,
      ⟨z, (abs_lt.mp hz1).1.le, (abs_lt.mp hz1).2.le⟩)
      (hz.trans_le (min_le_left _ _))
  let Dnew : SurgeryCapTag (fun p => F (psi p)) u := {
    profile := D.profile
    cutHeight := D.cutHeight
    removal := D.removal
    scale := D.scale
    sign := D.sign
    removal_pos := D.removal_pos
    scale_pos := D.scale_pos
    sign_abs := D.sign_abs
    scale_small := D.scale_small
    tube := D.tube
    tube_source := D.tube_source
    tube_smooth := D.tube_smooth
    tube_inverse := D.tube_inverse
    tube_height := D.tube_height
    sourceChart := D.sourceChart
    source_smooth := D.source_smooth
    source_inverse := D.source_inverse
    overlapWidth := o
    overlap_pos := ho
    overlap_le := (min_le_right o0 D.overlapWidth).trans D.overlap_le
    source_band := fun q hq => D.source_band q (hq.trans_le (min_le_right _ _))
    central_eq := by
      intro q hq
      rw [D.central_eq q (hq.trans_le (min_le_right _ _))]
      apply hfix
      apply hband q
      have hqo := hq.trans_le (min_le_left o0 D.overlapWidth)
      change -o0 < -(heightCoordinates (q : E3)).2
      linarith only [hqo]
    flatChart := D.flatChart
    flat_source := D.flat_source
    flat_smooth := D.flat_smooth
    flat_inverse := D.flat_inverse
    flat_eq := D.flat_eq
    beta := D.beta
    beta_ne := D.beta_ne
    collarWidth := w
    collar_pos := hw
    collar_le := (min_le_right w0 D.collarWidth).trans D.collar_le
    collar_eq := by
      intro x hx z hz
      rw [D.collar_eq x hx z (hz.trans_le (min_le_right _ _))]
      exact hfix _ (hflatU x hx z hz) }
  refine ⟨Dnew, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    min_le_right _ _, min_le_right _ _, rfl, rfl, ?_, ?_⟩
  · rw [Dnew.cap_eq_image, D.cap_eq_image]
  · rw [Dnew.seam_eq_image, D.seam_eq_image]

end PoincareConjecture.M25.Topology3D
