import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.CollarMatching
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Separation.ComplementaryDomain
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCollar
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.SphereCharts.MatchingBalls
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Closing.Certificate













noncomputable section
set_option autoImplicit false

open Set PoincareConjecture TopologicalSpace
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.ClosedModels

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E3 M]

private theorem exists_enclosing_ball (U V : Opens M)
    (f : OpenPartialHomeomorph M E3) (hfs : f.source = V) (hft : f.target = univ)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source)
    (hfi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f.symm f.target)
    (hcompact : IsCompact ((U : Set M) ∪ V)) :
    ∃ b : OpenPartialHomeomorph E3 M,
      b.source = univ ∧ b.target = V ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      ((U : Set M) ∪ V) \ U ⊆ b '' Metric.ball 0 1 := by
  let A := ((U : Set M) ∪ V) \ U
  have hA : IsCompact A := hcompact.diff U.isOpen
  have hAV : A ⊆ V := fun x hx => hx.1.resolve_left hx.2
  have hfA : IsCompact (f '' A) :=
    hA.image_of_continuousOn (f.continuousOn.mono (hfs.symm ▸ hAV))
  obtain ⟨r, hr⟩ := hfA.isBounded.subset_ball 0
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let d := (Homeomorph.smulOfNeZero R hR.ne' : E3 ≃ₜ E3).toOpenPartialHomeomorph
  let b := d.trans f.symm
  have hbs : b.source = univ := by simp [b, d, hft]
  have hbt : b.target = V := by simp [b, d, hfs]
  have hd : ContMDiff (𝓡 3) (𝓡 3) ∞ d := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : E3 => R • x)
    exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : E3 => R)).smul
      (contDiff_id : ContDiff ℝ ∞ (fun x : E3 => x))).contMDiff
  have hdi : ContMDiff (𝓡 3) (𝓡 3) ∞ d.symm := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : E3 => R⁻¹ • x)
    exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : E3 => R⁻¹)).smul
      (contDiff_id : ContDiff ℝ ∞ (fun x : E3 => x))).contMDiff
  refine ⟨b, hbs, hbt, hfi.comp hd.contMDiffOn inter_subset_right,
    hdi.comp_contMDiffOn (hf.mono inter_subset_left), ?_⟩
  intro x hx
  have hxR : ‖f x‖ < R :=
    (mem_ball_zero_iff.mp (hr (mem_image_of_mem f hx))).trans_le (le_max_left _ _)
  refine ⟨R⁻¹ • f x, ?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR), inv_mul_lt_iff₀ hR]
    simpa using hxR
  · change f.symm (R • (R⁻¹ • f x)) = x
    rw [smul_inv_smul₀ hR.ne']
    exact f.left_inv (hfs.symm ▸ hAV hx)

private theorem exists_matching_balls [T2Space M]
    (U V : Opens M) (e f : OpenPartialHomeomorph M E3)
    (hes : e.source = U) (het : e.target = univ)
    (hfs : f.source = V) (hft : f.target = univ)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source)
    (hfi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f.symm f.target)
    (hcompact : IsCompact ((U : Set M) ∪ V)) :
    ∃ (r : ℝ) (b d : OpenPartialHomeomorph E3 M),
      0 < r ∧ Metric.ball 0 (Real.exp r) ⊆ b.source ∧
      Metric.ball 0 (Real.exp r) ⊆ d.source ∧
      b.target ⊆ (U : Set M) ∪ V ∧ d.target ⊆ (U : Set M) ∪ V ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ d d.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ d.symm d.target ∧
      b '' Metric.closedBall 0 1 ∪ d '' Metric.closedBall 0 1 = (U : Set M) ∪ V ∧
      b '' Metric.closedBall 0 1 ∩ d '' Metric.closedBall 0 1 = b '' Metric.sphere 0 1 ∧
      ∀ (q : UnitTwoSphere) (t : ℝ), |t| < r →
        b (Real.exp t • (q : E3)) = d (Real.exp (-t) • (q : E3)) := by
  obtain ⟨b, hbs, hbt, hb, hbi, henclose⟩ :=
    exists_enclosing_ball U V f hfs hft hf hfi hcompact
  let Y := (U : Set M) ∪ V
  let K := b '' Metric.closedBall 0 1
  let L := Y \ b '' Metric.ball 0 1
  have hballsource : Metric.closedBall (0 : E3) 1 ⊆ b.source := hbs.symm ▸ subset_univ _
  have hbV (x : E3) : b x ∈ V := hbt.subset (b.map_source (hbs.symm ▸ mem_univ _))
  have hKY : K ⊆ Y := by
    rintro y ⟨x, _, rfl⟩
    exact Or.inr (hbV x)
  have hK : IsCompact K :=
    (isCompact_closedBall 0 1).image_of_continuousOn (b.continuousOn.mono hballsource)
  have hKi : interior K = b '' Metric.ball 0 1 :=
    (b.image_ball_eq_interior hballsource rfl).symm
  have hKf : frontier K = b '' Metric.sphere 0 1 :=
    (b.image_sphere_eq_frontier hballsource rfl).symm
  have hregular : closure (interior K) = K := by
    rw [hKi]
    obtain ⟨_, _, hclosure, _⟩ := b.image_region_of_isCompact_closure
      (D := Metric.ball (0 : E3) 1) Metric.isOpen_ball
      (by simpa only [closure_ball _ one_ne_zero] using (isCompact_closedBall (0 : E3) 1))
      (by simpa only [closure_ball _ one_ne_zero] using hballsource)
    simpa only [closure_ball _ one_ne_zero] using hclosure
  obtain ⟨hL, _, hLregular, hLf⟩ := Poincare.Topology.complementary_domain
    ⟨hcompact.isClosed, U.isOpen.union V.isOpen⟩ hcompact hK hKY hregular
  rw [hKi] at hL hLregular hLf
  have hLU : L ⊆ U := by
    intro x hx
    by_contra hxU
    exact hx.2 (henclose ⟨hx.1, hxU⟩)
  have hbinj : Function.Injective b := (b.isOpenEmbedding hbs).injective
  have hbball (x : E3) : b x ∈ b '' Metric.ball 0 1 ↔ ‖x‖ < 1 := by
    constructor
    · rintro ⟨y, hy, heq⟩
      exact mem_ball_zero_iff.mp (hbinj heq ▸ hy)
    · intro hx
      exact ⟨x, mem_ball_zero_iff.mpr hx, rfl⟩
  let R : Diffeomorph CylModel CylModel RoundCylinderSpace RoundCylinderSpace ∞ := {
    toEquiv := (Equiv.refl UnitTwoSphere).prodCongr (Equiv.neg ℝ)
    contMDiff_toFun := contMDiff_fst.prodMk contMDiff_snd.neg
    contMDiff_invFun := contMDiff_fst.prodMk contMDiff_snd.neg }
  let c₀ := (R.toHomeomorph.toOpenPartialHomeomorph.trans
    Poincare.radialPartialDiffeomorph.toOpenPartialHomeomorph).trans b
  have hc₀s : c₀.source = univ := by
    ext z
    change (z ∈ univ ∧ R z ∈ Poincare.radialPartialDiffeomorph.source) ∧
      Poincare.radialPartialDiffeomorph (R z) ∈ b.source ↔ z ∈ univ
    simp [hbs]
  have hc₀ : ContMDiffOn CylModel (𝓡 3) ∞ c₀ c₀.source :=
    hb.comp (Poincare.radialPartialDiffeomorph.contMDiffOn.comp
      R.contMDiff.contMDiffOn (fun _ hz => hz.1.2)) (fun _ hz => hz.2)
  have hci₀ : ContMDiffOn (𝓡 3) CylModel ∞ c₀.symm c₀.target :=
    R.symm.contMDiff.comp_contMDiffOn
      (Poincare.radialPartialDiffeomorph.symm.contMDiffOn.comp
        (hbi.mono inter_subset_left) (fun _ hz => hz.2.1))
  have hc₀val (z : RoundCylinderSpace) : c₀ z = b (Real.exp (-z.2) • (z.1 : E3)) := rfl
  have hc₀zero (q : UnitTwoSphere) : c₀ (q, 0) = b q := by simp [hc₀val]
  have hc₀L (z : RoundCylinderSpace) : c₀ z ∈ L ↔ z.2 ≤ 0 := by
    change (c₀ z ∈ Y ∧ ¬c₀ z ∈ b '' Metric.ball 0 1) ↔ _
    rw [hc₀val, hbball]
    have hnorm : ‖Real.exp (-z.2) • (z.1 : E3)‖ = Real.exp (-z.2) := by
      simp [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hnorm, Real.exp_lt_one_iff]
    simp only [show b (Real.exp (-z.2) • (z.1 : E3)) ∈ Y from Or.inr (hbV _), true_and]
    simp only [not_lt, neg_nonneg]
  have hc₀cont : Continuous c₀ := continuousOn_univ.mp (hc₀s ▸ c₀.continuousOn)
  let W : Opens RoundCylinderSpace := ⟨c₀ ⁻¹' e.source, e.open_source.preimage hc₀cont⟩
  have hzeroW (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ W := by
    have hxL : c₀ (q, 0) ∈ L := (hc₀L (q, 0)).mpr le_rfl
    exact hes.symm.subset (hLU hxL)
  obtain ⟨δ, hδ, hδW⟩ := CylinderGluing.exists_cylinder_collar W hzeroW
  let c := c₀.restrOpen W W.isOpen
  have hcs : univ ×ˢ Ioo (-δ) δ ⊆ c.source := by
    intro z hz
    exact ⟨hc₀s.symm ▸ mem_univ _, hδW z (abs_lt.mpr hz.2)⟩
  have hct : c.target ⊆ e.source := by
    intro y hy
    have h := hy.2
    change c₀ (c₀.symm y) ∈ e.source at h
    rwa [c₀.right_inv hy.1] at h
  have hcfront : frontier L = range (fun q : UnitTwoSphere => c (q, 0)) := by
    rw [hLf, hKf]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, hc₀zero ⟨x, hx⟩⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, q.property, (hc₀zero q).symm⟩
  have hcside (y : M) (hy : y ∈ c.target) : y ∈ L ↔ (c.symm y).2 ≤ 0 := by
    have h := hc₀L (c.symm y)
    change c (c.symm y) ∈ L ↔ (c.symm y).2 ≤ 0 at h
    rwa [c.right_inv hy] at h
  obtain ⟨r, d, hr, _, hds, hdt, hd, hdi, hdL, hmatch⟩ :=
    Poincare.Manifold.Schoenflies.ball_neighborhood_matching_collar_in_coordinates
      e het he hei hL (hLU.trans hes.symm.subset) hLregular c
      (hc₀.mono inter_subset_left) (hci₀.mono inter_subset_left)
      hδ hcs hct hcfront hcside
  have hdsource : Metric.ball (0 : E3) (Real.exp r) ⊆ d.source := by
    intro x hx
    by_cases hle : ‖x‖ ≤ 1
    · exact hds (by simpa using hle)
    · have hx1 : 1 < ‖x‖ := lt_of_not_ge hle
      have hx0 : x ≠ 0 := by intro h; norm_num [h] at hx1
      let J := Poincare.sphereCylinderDiffeomorphPunctured
      let p := J.symm ⟨x, hx0⟩
      have hp : Real.exp p.2 • (p.1 : E3) = x :=
        congrArg Subtype.val (J.apply_symm_apply ⟨x, hx0⟩)
      have hnorm : Real.exp p.2 = ‖x‖ := by
        rw [← hp, norm_smul]
        simp [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hp0 : 0 < p.2 := Real.exp_lt_exp.mp (by simpa only [Real.exp_zero, hnorm] using hx1)
      have hpr : p.2 < r := Real.exp_lt_exp.mp (by simpa only [hnorm, mem_ball_zero_iff] using hx)
      exact hp ▸ (hmatch p (by simpa only [abs_of_pos hp0] using hpr)).1
  refine ⟨r, b, d, hr, hbs.symm ▸ subset_univ _, hdsource,
    hbt.symm ▸ subset_union_right, (hdt.trans hes.subset).trans subset_union_left,
    hb, hd, hbi, hdi, ?_, ?_, ?_⟩
  · rw [hdL]
    apply Subset.antisymm
    · exact union_subset hKY sdiff_subset
    · intro x hx
      by_cases hxi : x ∈ b '' Metric.ball 0 1
      · exact Or.inl (image_mono Metric.ball_subset_closedBall hxi)
      · exact Or.inr ⟨hx, hxi⟩
  · rw [hdL, ← hKf, hK.isClosed.frontier_eq, hKi]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hKY hx.1, hx.2⟩⟩
  · intro q t ht
    have hm := (hmatch (q, -t) (by simpa only [abs_neg] using ht)).2
    change d (Real.exp (-t) • (q : E3)) = c₀ (q, -t) at hm
    simpa only [hc₀val, neg_neg] using hm.symm



theorem nonempty_euclidean_pair_certificate [IsManifold (𝓡 3) ∞ M] [T2Space M]
    (U V : Opens M) (e f : OpenPartialHomeomorph M E3)
    (hes : e.source = U) (het : e.target = univ)
    (hfs : f.source = V) (hft : f.target = univ)
    (he : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) (𝓡 3) ∞ e.symm e.target)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f f.source)
    (hfi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f.symm f.target)
    (hcompact : IsCompact ((U : Set M) ∪ V))
    (hcomponent : ∃ x : M, (U : Set M) ∪ V = connectedComponent x) :
    Nonempty (ClosedComponentCertificate .threeSphere ((U : Set M) ∪ V)) := by
  classical
  obtain ⟨r, b, d, hr, hbs, hds, hbt, hdt, hb, hd, hbi, hdi,
      hcover, hintersection, hmatch⟩ :=
    exists_matching_balls U V e f hes het hfs hft he hei hf hfi hcompact
  let W : Opens M := ⟨(U : Set M) ∪ V, U.isOpen.union V.isOpen⟩
  have hW : Nonempty W := by
    obtain ⟨x, hx⟩ := hcomponent
    exact ⟨⟨x, hx.symm.subset mem_connectedComponent⟩⟩
  obtain ⟨F⟩ := SphereCharts.nonempty_diffeomorph_of_matching_balls_in_open
    W hW b d hr hbs hds hbt hdt hb hd hbi hdi hcover hintersection hmatch
  let inv : M → W := fun x => if hx : x ∈ W then ⟨x, hx⟩ else Classical.choice hW
  have hinv (x : M) (hx : x ∈ W) : (inv x : M) = x := by simp [inv, hx]
  have hinv_smooth : ContMDiffOn (𝓡 3) (𝓡 3) ∞ inv (W : Set M) := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff W inv (W : Set M) x).mp
    apply contMDiffWithinAt_id.congr
    · intro y hy
      exact hinv y hy
    · exact hinv x hx
  let S : SmoothClosedComponentModel .threeSphere ((U : Set M) ∪ V) := {
    model := W
    model_topology := inferInstance
    model_charted := inferInstance
    model_manifold := inferInstance
    standard_model := F.toHomeomorph
    standard_smooth := ⟨F⟩
    forward := Subtype.val
    inverse := inv
    forward_mem := fun x => x.property
    left_inverse := hinv
    right_inverse := fun x => Subtype.ext (hinv x x.property)
    forward_smooth := contMDiff_subtype_val
    inverse_smooth := hinv_smooth }
  exact S.nonempty_closedComponentCertificate hcompact hcomponent

end PoincareConjecture.ClosedModels
