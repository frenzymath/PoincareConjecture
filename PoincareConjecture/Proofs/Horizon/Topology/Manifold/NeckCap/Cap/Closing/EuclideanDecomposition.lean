import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.ModelCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.BallImages
import PoincareConjecture.Proofs.Horizon.Topology.Maps.OpenPartialHomeomorph.Compact
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCylinder
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Tube.Gluing.Coordinates.Affine













set_option autoImplicit false

noncomputable section

open Set TopologicalSpace
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.CapCertificate

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M}

omit [T2Space M] in


theorem exists_two_cap_euclidean_enclosing_ball (C D : CapCertificate g)
    (hkind : D.model_kind = .euclidean)
    (hcompact : IsCompact (C.carrier ∪ D.carrier)) :
    ∃ b : OpenPartialHomeomorph E3 M,
      b.source = univ ∧ b.target = D.carrier ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      (C.carrier ∪ D.carrier) \ C.carrier ⊆ b '' Metric.ball 0 1 := by
  obtain ⟨e, hs, ht, he, hei⟩ := D.exists_euclidean_coordinates hkind
  let A := (C.carrier ∪ D.carrier) \ C.carrier
  have hA : IsCompact A := hcompact.diff C.carrier_open
  have hAD : A ⊆ D.carrier := by
    intro x hx
    exact hx.1.resolve_left hx.2
  have heA : IsCompact (e '' A) :=
    hA.image_of_continuousOn (e.continuousOn.mono (hs.symm ▸ hAD))
  obtain ⟨r, hr⟩ := heA.isBounded.subset_ball 0
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let d := (Homeomorph.smulOfNeZero R hR.ne' : E3 ≃ₜ E3).toOpenPartialHomeomorph
  let b := d.trans e.symm
  have hbs : b.source = univ := by simp [b, d, ht]
  have hbt : b.target = D.carrier := by simp [b, d, hs]
  have hd : ContMDiff (𝓡 3) (𝓡 3) ∞ d := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : E3 => R • x)
    exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : E3 => R)).smul
      (contDiff_id : ContDiff ℝ ∞ (fun x : E3 => x))).contMDiff
  have hdi : ContMDiff (𝓡 3) (𝓡 3) ∞ d.symm := by
    change ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : E3 => R⁻¹ • x)
    exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : E3 => R⁻¹)).smul
      (contDiff_id : ContDiff ℝ ∞ (fun x : E3 => x))).contMDiff
  refine ⟨b, hbs, hbt,
    hei.comp hd.contMDiffOn inter_subset_right,
    hdi.comp_contMDiffOn (he.mono inter_subset_left), ?_⟩
  intro x hx
  have hxR : ‖e x‖ < R := by
    have hxr := hr (mem_image_of_mem e hx)
    exact (mem_ball_zero_iff.mp hxr).trans_le (le_max_left _ _)
  refine ⟨R⁻¹ • e x, ?_, ?_⟩
  · rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hR), inv_mul_lt_iff₀ hR]
    simpa using hxR
  · change e.symm (R • (R⁻¹ • e x)) = x
    rw [smul_inv_smul₀ hR.ne']
    exact e.left_inv (hs.symm ▸ hAD hx)

omit [T2Space M] in
private theorem exists_radial_collar_in_cap_overlap (C D : CapCertificate g)
    (b : OpenPartialHomeomorph E3 M) (hbs : b.source = univ) (hbt : b.target = D.carrier)
    (hb : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source)
    (hbi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target)
    (henclose : (C.carrier ∪ D.carrier) \ C.carrier ⊆ b '' Metric.ball 0 1) :
    ∃ c : OpenPartialHomeomorph RoundCylinderSpace M,
      c.source = univ ∧
      ContMDiffOn CylModel (𝓡 3) ∞ c c.source ∧
      ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target ∧
      (∀ z : RoundCylinderSpace, c z = b (Real.exp z.2 • (z.1 : E3))) ∧
      c '' (univ ×ˢ ({0} : Set ℝ)) = b '' Metric.sphere 0 1 ∧
      ∃ δ : ℝ, 0 < δ ∧
        c '' (univ ×ˢ Ioo (-δ) δ) ⊆ C.carrier ∩ D.carrier ∧
        c '' (univ ×ˢ Ioo (-δ) 0) ⊆ b '' Metric.ball 0 1 ∧
        c '' (univ ×ˢ Ioo 0 δ) ⊆
          (C.carrier ∪ D.carrier) \ b '' Metric.closedBall 0 1 := by
  let U := Poincare.puncturedThreeSpace
  have hU : Nonempty U := by
    obtain ⟨q⟩ : Nonempty UnitTwoSphere :=
      (NormedSpace.sphere_nonempty.mpr (zero_le_one : (0 : ℝ) ≤ 1)).coe_sort
    exact ⟨⟨q, ne_zero_of_mem_unit_sphere q⟩⟩
  let a := U.openPartialHomeomorphSubtypeCoe hU
  let F := Poincare.sphereCylinderDiffeomorphPunctured
  let r := F.toHomeomorph.toOpenPartialHomeomorph.trans a
  let c := r.trans b
  have hrs : r.source = univ := by simp [r, a]
  have hcs : c.source = univ := by simp [c, hrs, hbs]
  have ha : ContMDiffOn (𝓡 3) (𝓡 3) ∞ a a.source :=
    contMDiff_subtype_val.contMDiffOn
  have hai : ContMDiffOn (𝓡 3) (𝓡 3) ∞ a.symm a.target := by
    intro x hx
    apply (ContMDiffWithinAt.subtypeVal_comp_iff U a.symm a.target x).mp
    apply contMDiffWithinAt_id.congr
    · intro y hy
      exact a.right_inv hy
    · exact a.right_inv hx
  have hr : ContMDiffOn CylModel (𝓡 3) ∞ r r.source :=
    ha.comp F.contMDiff.contMDiffOn inter_subset_right
  have hri : ContMDiffOn (𝓡 3) CylModel ∞ r.symm r.target :=
    F.symm.contMDiff.comp_contMDiffOn (hai.mono inter_subset_left)
  have hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source :=
    hb.comp (hr.mono inter_subset_left) inter_subset_right
  have hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target :=
    hri.comp (hbi.mono inter_subset_left) inter_subset_right
  have hformula (z : RoundCylinderSpace) : c z = b (Real.exp z.2 • (z.1 : E3)) := rfl
  have hzero (q : UnitTwoSphere) : c (q, 0) = b q := by simp [hformula]
  have hbinj : Function.Injective b := (b.isOpenEmbedding hbs).injective
  have hbD (x : E3) : b x ∈ D.carrier :=
    hbt ▸ b.map_source (hbs.symm ▸ mem_univ x)
  have hzeroCD (q : UnitTwoSphere) : c (q, 0) ∈ C.carrier ∩ D.carrier := by
    rw [hzero]
    refine ⟨?_, hbD q⟩
    by_contra hqC
    obtain ⟨x, hx, hxeq⟩ := henclose ⟨Or.inr (hbD q), hqC⟩
    have hxeq' : x = (q : E3) := hbinj hxeq
    subst x
    have hnorm : ‖(q : E3)‖ = 1 := by simp
    exact (ne_of_lt (mem_ball_zero_iff.mp hx)) hnorm
  have hcc : Continuous c := continuousOn_univ.mp (hcs ▸ c.continuousOn)
  let V : Opens RoundCylinderSpace :=
    ⟨c ⁻¹' (C.carrier ∩ D.carrier), (C.carrier_open.inter D.carrier_open).preimage hcc⟩
  obtain ⟨δ, hδ, hδV⟩ := CylinderGluing.exists_cylinder_collar V hzeroCD
  refine ⟨c, hcs, hc, hci, hformula, ?_, δ, hδ, ?_, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨⟨q, t⟩, ⟨_, ht⟩, rfl⟩
      have ht0 : t = 0 := ht
      subst t
      exact ⟨q, q.property, (hzero q).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(⟨x, hx⟩, 0), ⟨mem_univ _, rfl⟩, hzero ⟨x, hx⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact hδV z (abs_lt.mpr hz.2)
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨Real.exp z.2 • (z.1 : E3), ?_, (hformula z).symm⟩
    rw [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    simpa using (Real.exp_lt_one_iff.mpr hz.2.2)
  · rintro _ ⟨z, hz, rfl⟩
    refine ⟨Or.inr (hformula z ▸ hbD _), ?_⟩
    rintro ⟨x, hx, hxeq⟩
    have hxeq' : x = Real.exp z.2 • (z.1 : E3) :=
      hbinj (hxeq.trans (hformula z))
    rw [hxeq', mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)] at hx
    have hexp : Real.exp z.2 ≤ 1 := by simpa using hx
    exact (not_le_of_gt (Real.one_lt_exp_iff.mpr hz.2.1)) hexp




theorem exists_two_cap_euclidean_ball_decomposition (C D : CapCertificate g)
    (hkind : D.model_kind = .euclidean)
    (hcompact : IsCompact (C.carrier ∪ D.carrier)) :
    ∃ b : OpenPartialHomeomorph E3 M,
      b.source = univ ∧ b.target = D.carrier ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b b.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ b.symm b.target ∧
      (C.carrier ∪ D.carrier) \ C.carrier ⊆ b '' Metric.ball 0 1 ∧
      IsCompact (b '' Metric.closedBall 0 1) ∧
      IsCompact ((C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1) ∧
      (C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1 ⊆ C.carrier ∧
      b '' Metric.closedBall 0 1 ∪
        ((C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1) = C.carrier ∪ D.carrier ∧
      b '' Metric.closedBall 0 1 ∩
        ((C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1) = b '' Metric.sphere 0 1 ∧
      closure (b '' Metric.ball 0 1) = b '' Metric.closedBall 0 1 ∧
      interior (b '' Metric.closedBall 0 1) = b '' Metric.ball 0 1 ∧
      frontier (b '' Metric.closedBall 0 1) = b '' Metric.sphere 0 1 ∧
      interior ((C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1) =
        (C.carrier ∪ D.carrier) \ b '' Metric.closedBall 0 1 ∧
      closure ((C.carrier ∪ D.carrier) \ b '' Metric.closedBall 0 1) =
        (C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1 ∧
      frontier ((C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1) =
        b '' Metric.sphere 0 1 ∧
      ∃ c : OpenPartialHomeomorph RoundCylinderSpace M,
        c.source = univ ∧
        ContMDiffOn CylModel (𝓡 3) ∞ c c.source ∧
        ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target ∧
        (∀ z : RoundCylinderSpace, c z = b (Real.exp z.2 • (z.1 : E3))) ∧
        c '' (univ ×ˢ ({0} : Set ℝ)) = b '' Metric.sphere 0 1 ∧
        ∃ δ : ℝ, 0 < δ ∧
          c '' (univ ×ˢ Ioo (-δ) δ) ⊆ C.carrier ∩ D.carrier ∧
          c '' (univ ×ˢ Ioo (-δ) 0) ⊆ b '' Metric.ball 0 1 ∧
          c '' (univ ×ˢ Ioo 0 δ) ⊆
            (C.carrier ∪ D.carrier) \ b '' Metric.closedBall 0 1 := by
  obtain ⟨b, hbs, hbt, hb, hbi, henclose⟩ :=
    C.exists_two_cap_euclidean_enclosing_ball D hkind hcompact
  have hbsource : Metric.closedBall (0 : E3) 1 ⊆ b.source := by rw [hbs]; exact subset_univ _
  have hKD : b '' Metric.closedBall 0 1 ⊆ D.carrier := by
    rintro _ ⟨x, hx, rfl⟩
    exact hbt ▸ b.map_source (hbsource hx)
  have hKY : b '' Metric.closedBall 0 1 ⊆ C.carrier ∪ D.carrier :=
    hKD.trans subset_union_right
  have hUK : b '' Metric.ball 0 1 ⊆ b '' Metric.closedBall 0 1 :=
    image_mono Metric.ball_subset_closedBall
  have hK : IsCompact (b '' Metric.closedBall 0 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn (b.continuousOn.mono hbsource)
  obtain ⟨hU, _, hclosure, _⟩ := b.image_region_of_isCompact_closure
    (D := Metric.ball (0 : E3) 1) Metric.isOpen_ball
    (by simpa only [closure_ball _ one_ne_zero] using (isCompact_closedBall (0 : E3) 1))
    (by simpa only [closure_ball _ one_ne_zero] using hbsource)
  have hLC : (C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1 ⊆ C.carrier := by
    intro x hx
    by_contra hxC
    exact hx.2 (henclose ⟨hx.1, hxC⟩)
  have hi := b.image_ball_eq_interior hbsource rfl
  have hf := b.image_sphere_eq_frontier hbsource rfl
  have hcl : closure (b '' Metric.ball 0 1) = b '' Metric.closedBall 0 1 := by
    simpa only [closure_ball _ one_ne_zero] using hclosure
  have hYi : IsOpen (C.carrier ∪ D.carrier) := C.carrier_open.union D.carrier_open
  have hLi : interior ((C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1) =
      (C.carrier ∪ D.carrier) \ b '' Metric.closedBall 0 1 := by
    rw [sdiff_eq, interior_inter, hYi.interior_eq, interior_compl, hcl]
    rfl
  have hLcl : closure ((C.carrier ∪ D.carrier) \ b '' Metric.closedBall 0 1) =
      (C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1 := by
    have hinter : closure ((C.carrier ∪ D.carrier) ∩ (b '' Metric.closedBall 0 1)ᶜ) =
        (C.carrier ∪ D.carrier) ∩ closure (b '' Metric.closedBall 0 1)ᶜ := by
      apply Subset.antisymm
      · simpa only [hcompact.isClosed.closure_eq] using
          (closure_inter_subset (s := C.carrier ∪ D.carrier)
            (t := (b '' Metric.closedBall 0 1)ᶜ))
      · exact hYi.inter_closure
    simpa only [sdiff_eq, closure_compl, ← hi] using hinter
  have hLf : frontier ((C.carrier ∪ D.carrier) \ b '' Metric.ball 0 1) =
      b '' Metric.sphere 0 1 := by
    rw [(hcompact.diff hU).isClosed.frontier_eq, hLi, hf, hK.isClosed.frontier_eq, ← hi]
    ext x
    constructor
    · rintro ⟨⟨hxY, hxU⟩, hx⟩
      refine ⟨?_, hxU⟩
      by_contra hxK
      exact hx ⟨hxY, hxK⟩
    · rintro ⟨hxK, hxU⟩
      exact ⟨⟨hKY hxK, hxU⟩, fun hx => hx.2 hxK⟩
  refine ⟨b, hbs, hbt, hb, hbi, henclose, hK, hcompact.diff hU, hLC, ?_, ?_,
    hcl, hi.symm, hf.symm, hLi, hLcl, hLf,
    exists_radial_collar_in_cap_overlap C D b hbs hbt hb hbi henclose⟩
  · apply Subset.antisymm
    · exact union_subset hKY sdiff_subset
    · intro x hx
      by_cases hxU : x ∈ b '' Metric.ball 0 1
      · exact Or.inl (hUK hxU)
      · exact Or.inr ⟨hx, hxU⟩
  · rw [hf, hK.isClosed.frontier_eq, ← hi]
    ext x
    exact ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, hKY hx.1, hx.2⟩⟩

end PoincareConjecture.CapCertificate
