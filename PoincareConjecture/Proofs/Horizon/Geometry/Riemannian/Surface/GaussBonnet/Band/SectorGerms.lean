import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Bands.OuterFaces
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.DerivativeTest

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

theorem eventually_graph_side_of_hasStrictFDerivAt
    {f : (ℝ × ℝ) → ℝ} {f' : (ℝ × ℝ) →L[ℝ] ℝ} {h : ℝ → ℝ} {t : ℝ}
    (hf : HasStrictFDerivAt f f' (t, h t)) (hpos : 0 < f' (0, 1))
    (hh : ContinuousAt h t) (hzero : ∀ᶠ s in 𝓝 t, f (s, h s) = 0) :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (t, h t), f q ≤ 0 ↔ q.2 ≤ h q.1 := by
  have hpair : Tendsto (fun q : ℝ × ℝ => (q, (q.1, h q.1)))
      (𝓝 (t, h t)) (𝓝 ((t, h t), (t, h t))) := by
    exact continuousAt_id.prodMk (continuousAt_fst.prodMk (hh.comp continuousAt_fst))
  have hbound := hpair.eventually (hf.isLittleO.bound (half_pos hpos))
  have hz := (continuousAt_fst : ContinuousAt Prod.fst (t, h t)).eventually hzero
  filter_upwards [hbound, hz] with q hq hqzero
  have hdiff : q - (q.1, h q.1) = (q.2 - h q.1) • (0, 1) := by
    ext <;> simp
  have hn : ‖q - (q.1, h q.1)‖ = |q.2 - h q.1| := by
    simp [hdiff]
  rw [hqzero, sub_zero, hn, hdiff, map_smul] at hq
  change |f q - (q.2 - h q.1) * f' (0, 1)| ≤
    f' (0, 1) / 2 * |q.2 - h q.1| at hq
  constructor
  · intro hnonpos
    by_contra hbad
    have hp : 0 < q.2 - h q.1 := sub_pos.mpr (lt_of_not_ge hbad)
    rw [abs_of_pos hp] at hq
    have hb := (abs_le.mp hq).1
    nlinarith [mul_pos hp hpos]
  · intro hle
    by_cases he : q.2 = h q.1
    · have hqeq : q = (q.1, h q.1) := Prod.ext rfl he
      rw [hqeq, hqzero]
    · have hn : q.2 - h q.1 < 0 := sub_neg.mpr (lt_of_le_of_ne hle he)
      rw [abs_of_neg hn] at hq
      have hb := (abs_le.mp hq).2
      nlinarith [mul_neg_of_neg_of_pos hn hpos]

end PoincareConjecture.Topology.Surface

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

noncomputable def topLineExcess (i : Fin B.interface.count)
    (z : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (collarParameterEquiv z).2 - B.interface.piece i (collarParameterEquiv z).1

noncomputable def topLineFunctional (i : Fin B.interface.count) :
    EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
  ((LinearMap.snd ℝ ℝ ℝ).toAffineMap -
    (B.interface.piece i).comp (LinearMap.fst ℝ ℝ ℝ).toAffineMap).comp
      collarParameterEquiv.toContinuousLinearMap.toLinearMap.toAffineMap

@[simp] theorem topLineFunctional_apply (i : Fin B.interface.count)
    (z : EuclideanSpace ℝ (Fin 2)) : B.topLineFunctional i z = B.topLineExcess i z := rfl

theorem topLineFunctional_vertical (i : Fin B.interface.count) :
    (B.topLineFunctional i).linear (collarParameterEquiv.symm (0, 1)) = 1 := by
  simp [topLineFunctional]

theorem topLineFunctional_linear_ne_zero (i : Fin B.interface.count) :
    (B.topLineFunctional i).linear ≠ 0 := by
  intro h
  have hv := B.topLineFunctional_vertical i
  rw [h, LinearMap.zero_apply] at hv
  exact zero_ne_one hv

theorem topLineFunctional_left_vertex (i : Fin B.interface.count) :
    B.topLineFunctional i (collarParameterEquiv.symm
      (B.interface.cut i.castSucc,
        lo (B.interface.cut i.castSucc) + B.interface.height i.castSucc)) = 0 := by
  simp only [topLineFunctional_apply, topLineExcess, collarParameterEquiv.apply_symm_apply,
    (B.interface.piece_endpoints i).1, sub_self]

theorem topLineFunctional_right_vertex (i : Fin B.interface.count) :
    B.topLineFunctional i (collarParameterEquiv.symm
      (B.interface.cut i.succ,
        lo (B.interface.cut i.succ) + B.interface.height i.succ)) = 0 := by
  simp only [topLineFunctional_apply, topLineExcess, collarParameterEquiv.apply_symm_apply,
    (B.interface.piece_endpoints i).2, sub_self]

private theorem upperGraph_strip_eq_of_mem_target
    (i : Fin B.interface.count) {t : ℝ}
    (ht : t ∈ (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter.target) :
    obliqueStripMap B.cuts.A B.cuts.B lo (t, B.upperGraph i t) =
      ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter.symm t,
        B.interface.piece i
          ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter.symm t)) := by
  let C := B.interface.pieceCoordinates B.open_domain B.smooth_lower i
  have hz : C.upperGraph t ∈ Ioo (-B.cuts.radius) B.cuts.radius :=
    (C.source_subset (C.parameter.map_target ht)).2
  have hgap := (sub_pos.mpr (B.cuts.separated _ hz)).ne'
  have hparam := C.parameter.right_inv ht
  rw [C.map_eq] at hparam
  change obliqueProjection B.cuts.A B.cuts.B (C.parameter.symm t) (C.upperGraph t) = t at hparam
  have hx : B.cuts.A (C.upperGraph t) +
      t * (B.cuts.B (C.upperGraph t) - B.cuts.A (C.upperGraph t)) = C.parameter.symm t := by
    have hm := congrArg (fun r => r * (B.cuts.B (C.upperGraph t) - B.cuts.A (C.upperGraph t))) hparam
    dsimp [obliqueProjection] at hm
    rw [div_mul_cancel₀ _ hgap] at hm
    linarith
  change obliqueStripMap B.cuts.A B.cuts.B lo (t, C.upperGraph t) = _
  simp only [obliqueStripMap, hx]
  dsimp [ObliquePolygonalBoundary.PieceCoordinates.upperGraph]
  simp [C]

theorem topLineExcess_eventually_nonpos_iff
    (i : Fin B.interface.count) {t : ℝ}
    (ht : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ)) :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (t, B.upperGraph i t),
      B.topLineExcess i (collarParameterEquiv.symm
        (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0 ↔
          q.2 ≤ B.upperGraph i q.1 := by
  let C := B.interface.pieceCoordinates B.open_domain B.smooth_lower i
  let η := B.upperGraph i t
  let x := C.parameter.symm t
  let f : (ℝ × ℝ) → ℝ := fun q =>
    (B.cuts.coordinates B.open_domain B.smooth_lower q).2 -
      B.interface.piece i (B.cuts.coordinates B.open_domain B.smooth_lower q).1
  have htC : t ∈ C.parameter.target := C.parameter_mem_target ht
  have hxcell := C.inverse_mem_cell ht
  have hz : η ∈ Ioo (-B.cuts.radius) B.cuts.radius :=
    (C.source_subset (C.parameter.map_target htC)).2
  have hxdom : x ∈ B.domain := (C.source_subset (C.parameter.map_target htC)).1
  have hsource : (t, η) ∈ (B.cuts.coordinates B.open_domain B.smooth_lower).source :=
    C.band_subset_coordinates_source B.open_domain B.smooth_lower
      ⟨ht, (C.upperGraph_bounds ht).1.le, le_rfl⟩
  have hpiece : ContDiff ℝ ∞ (B.interface.piece i) := by
    rw [(B.interface.piece i).decomp]
    exact (B.interface.piece i).linear.toContinuousLinearMap.contDiff.add contDiff_const
  have hc := (B.cuts.smooth_coordinates B.open_domain B.smooth_lower).contDiffAt
    ((B.cuts.coordinates B.open_domain B.smooth_lower).open_source.mem_nhds hsource)
  have hfc : ContDiffAt ℝ ∞ f (t, η) := hc.snd.sub (hpiece.contDiffAt.comp _ hc.fst)
  have hA := ((B.cuts.smooth_A η hz).contDiffAt (isOpen_Ioo.mem_nhds hz)).differentiableAt
    (by simp)
  have hB := ((B.cuts.smooth_B η hz).contDiffAt (isOpen_Ioo.mem_nhds hz)).differentiableAt
    (by simp)
  have hlo := ((B.smooth_lower x hxdom).contDiffAt (B.open_domain.mem_nhds hxdom)).differentiableAt
    (by simp)
  have hmap := B.upperGraph_strip_eq_of_mem_target i htC
  have hx : B.cuts.A η + t * (B.cuts.B η - B.cuts.A η) = x := congrArg Prod.fst hmap
  let v := deriv B.cuts.A η + t * (deriv B.cuts.B η - deriv B.cuts.A η)
  have hhorizontal : HasDerivAt
      (fun z => B.cuts.A z + t * (B.cuts.B z - B.cuts.A z)) v η :=
    hA.hasDerivAt.add ((hB.hasDerivAt.sub hA.hasDerivAt).const_mul t)
  have hlo' : HasDerivAt lo (deriv lo x)
      (B.cuts.A η + t * (B.cuts.B η - B.cuts.A η)) := hx.symm ▸ hlo.hasDerivAt
  have hd : HasDerivAt (fun z => f (t, z))
      ((deriv lo x - (B.interface.piece i).linear 1) * v + 1) η := by
    convert! ((hlo'.comp η hhorizontal).add (hasDerivAt_id η)).sub
      ((B.interface.piece i).hasDerivAt.comp η hhorizontal) using 1
    · funext z
      simp [f, B.cuts.coordinates_apply, obliqueStripMap]
    · ring
  have hfderiv : fderiv ℝ f (t, η) (0, 1) =
      (deriv lo x - (B.interface.piece i).linear 1) * v + 1 := by
    have hd' := (hfc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt η
      ((hasDerivAt_const η t).prodMk (hasDerivAt_id η))
    exact hd'.unique hd
  have hpositive : 0 < fderiv ℝ f (t, η) (0, 1) := by
    rw [hfderiv]
    have hp := B.interface.projection_deriv_pos i x hxcell
    have hg : 0 < B.cuts.B η - B.cuts.A η := sub_pos.mpr (B.cuts.separated η hz)
    change 0 < obliqueProjectionDerivative B.cuts.A B.cuts.B
      (x, (η, (B.interface.piece i).linear 1 - deriv lo x)) at hp
    unfold obliqueProjectionDerivative at hp
    have hn : 0 <
        (1 - deriv B.cuts.A η * ((B.interface.piece i).linear 1 - deriv lo x)) *
            (B.cuts.B η - B.cuts.A η) -
          (x - B.cuts.A η) * ((deriv B.cuts.B η - deriv B.cuts.A η) *
            ((B.interface.piece i).linear 1 - deriv lo x)) :=
      (div_pos_iff_of_pos_right (sq_pos_of_pos hg)).mp hp
    have hid :
        (1 - deriv B.cuts.A η * ((B.interface.piece i).linear 1 - deriv lo x)) *
            (B.cuts.B η - B.cuts.A η) -
          (x - B.cuts.A η) * ((deriv B.cuts.B η - deriv B.cuts.A η) *
            ((B.interface.piece i).linear 1 - deriv lo x)) =
        (B.cuts.B η - B.cuts.A η) *
          ((deriv lo x - (B.interface.piece i).linear 1) * v + 1) := by
      rw [← hx]
      dsimp [v]
      ring
    rw [hid] at hn
    exact (mul_pos_iff_of_pos_left hg).mp hn
  have hh : ContinuousAt (B.upperGraph i) t :=
    ((C.smooth_upperGraph B.smooth_lower).continuousOn t htC).continuousAt
      (C.parameter.open_target.mem_nhds htC)
  have hzero : ∀ᶠ s in 𝓝 t, f (s, B.upperGraph i s) = 0 := by
    filter_upwards [C.parameter.open_target.mem_nhds htC] with s hs
    have h := B.upperGraph_strip_eq_of_mem_target i hs
    change (B.cuts.coordinates B.open_domain B.smooth_lower (s, B.upperGraph i s)).2 -
      B.interface.piece i (B.cuts.coordinates B.open_domain B.smooth_lower (s, B.upperGraph i s)).1 = 0
    rw [B.cuts.coordinates_apply, h]
    exact sub_self _
  simpa only [topLineExcess, collarParameterEquiv.apply_symm_apply] using
    eventually_graph_side_of_hasStrictFDerivAt (hfc.hasStrictFDerivAt (by simp)) hpositive hh hzero

theorem band_top_eventually_mem_iff_active_constraints
    {q : EuclideanSpace ℝ (Fin 2)}
    (hq : (collarParameterEquiv q).1 ∈ Icc (0 : ℝ) 1)
    (hheight : (collarParameterEquiv q).2 = B.height (collarParameterEquiv q).1) :
    ∀ᶠ z in 𝓝 q, z ∈ B.band ↔
      ∃ i : Fin B.interface.count,
        (collarParameterEquiv q).1 ∈ Icc (B.cut i.castSucc) (B.cut i.succ) ∧
        (B.cut i.castSucc = (collarParameterEquiv q).1 →
          B.cut i.castSucc ≤ (collarParameterEquiv z).1) ∧
        ((collarParameterEquiv q).1 = B.cut i.succ →
          (collarParameterEquiv z).1 ≤ B.cut i.succ) ∧
        (collarParameterEquiv z).2 ≤ B.upperGraph i (collarParameterEquiv z).1 := by
  have hpos : 0 < (collarParameterEquiv q).2 := hheight ▸ B.height_pos hq
  have hsnd := (continuous_snd.comp collarParameterEquiv.continuous).continuousAt.eventually
    (Ioi_mem_nhds hpos)
  have hcell : ∀ᶠ z in 𝓝 q, ∀ i : Fin B.interface.count,
      (collarParameterEquiv z).1 ∈ Icc (B.cut i.castSucc) (B.cut i.succ) ↔
        (collarParameterEquiv q).1 ∈ Icc (B.cut i.castSucc) (B.cut i.succ) ∧
        (B.cut i.castSucc = (collarParameterEquiv q).1 →
          B.cut i.castSucc ≤ (collarParameterEquiv z).1) ∧
        ((collarParameterEquiv q).1 = B.cut i.succ →
          (collarParameterEquiv z).1 ≤ B.cut i.succ) := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : ContinuousAt (fun z => (collarParameterEquiv z).1) q :=
      (continuous_fst.comp collarParameterEquiv.continuous).continuousAt
    by_cases hi : (collarParameterEquiv q).1 ∈ Icc (B.cut i.castSucc) (B.cut i.succ)
    · have hleft : ∀ᶠ z in 𝓝 q,
          B.cut i.castSucc ≠ (collarParameterEquiv q).1 →
            B.cut i.castSucc < (collarParameterEquiv z).1 := by
        by_cases he : B.cut i.castSucc = (collarParameterEquiv q).1
        · exact Eventually.of_forall (fun _ hn => False.elim (hn he))
        · exact (hc.eventually (Ioi_mem_nhds (lt_of_le_of_ne hi.1 he))).mono
            (fun _ hz _ => hz)
      have hright : ∀ᶠ z in 𝓝 q,
          (collarParameterEquiv q).1 ≠ B.cut i.succ →
            (collarParameterEquiv z).1 < B.cut i.succ := by
        by_cases he : (collarParameterEquiv q).1 = B.cut i.succ
        · exact Eventually.of_forall (fun _ hn => False.elim (hn he))
        · exact (hc.eventually (Iio_mem_nhds (lt_of_le_of_ne hi.2 he))).mono
            (fun _ hz _ => hz)
      filter_upwards [hleft, hright] with z hl hr
      simp only [hi, true_and, mem_Icc]
      constructor
      · exact fun hz => ⟨fun _ => hz.1, fun _ => hz.2⟩
      · rintro ⟨hzl, hzr⟩
        constructor
        · by_cases he : B.cut i.castSucc = (collarParameterEquiv q).1
          · exact hzl he
          · exact (hl he).le
        · by_cases he : (collarParameterEquiv q).1 = B.cut i.succ
          · exact hzr he
          · exact (hr he).le
    · filter_upwards [hc.eventually (isClosed_Icc.isOpen_compl.mem_nhds hi)] with z hz
      simp only [hi, false_and]
      exact iff_false_intro hz
  filter_upwards [hsnd, hcell] with z hz hc
  simp only [band, mem_iUnion, coordinateGraphBand, mem_preimage, mem_ofPred_eq]
  constructor
  · rintro ⟨i, hi, _, htop⟩
    exact ⟨i, (hc i).mp hi |>.1, (hc i).mp hi |>.2.1, (hc i).mp hi |>.2.2, htop⟩
  · rintro ⟨i, hi, hl, hr, htop⟩
    exact ⟨i, (hc i).mpr ⟨hi, hl, hr⟩, hz.le, htop⟩

theorem band_open_top_eventually_mem_iff_topLineExcess
    (i : Fin B.interface.count) {t : ℝ}
    (ht : t ∈ Ioo (B.cut i.castSucc) (B.cut i.succ)) :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (t, B.upperGraph i t),
      collarParameterEquiv.symm q ∈ B.band ↔
        B.topLineExcess i (collarParameterEquiv.symm
          (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0 := by
  have hti : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ) := ⟨ht.1.le, ht.2.le⟩
  have hI : t ∈ Icc (0 : ℝ) 1 := by
    rw [← B.cut_interval_cover]
    exact mem_iUnion.mpr ⟨i, hti⟩
  have hg := B.band_top_eventually_mem_iff_active_constraints
    (q := collarParameterEquiv.symm (t, B.upperGraph i t))
    (by simpa using hI) (by simp [B.height_eq_upperGraph hti])
  have hcont : ContinuousAt (fun q : ℝ × ℝ => collarParameterEquiv.symm q)
      (t, B.upperGraph i t) := collarParameterEquiv.symm.continuous.continuousAt
  filter_upwards [hcont.eventually hg, B.topLineExcess_eventually_nonpos_iff i hti] with q hq hs
  simp only [collarParameterEquiv.apply_symm_apply] at hq
  rw [hq, hs]
  have huniq (j : Fin B.interface.count)
      (hj : t ∈ Icc (B.cut j.castSucc) (B.cut j.succ)) : j = i := by
    apply le_antisymm
    · by_contra hn
      have hij : i.succ ≤ j.castSucc := by
        change (i : ℕ) + 1 ≤ j
        exact lt_of_not_ge hn
      exact (not_lt_of_ge ((B.cut_strictMono.monotone hij).trans hj.1)) ht.2
    · by_contra hn
      have hji : j.succ ≤ i.castSucc := by
        change (j : ℕ) + 1 ≤ i
        exact lt_of_not_ge hn
      exact (not_lt_of_ge (hj.2.trans (B.cut_strictMono.monotone hji))) ht.1
  constructor
  · rintro ⟨j, hj, _, _, hh⟩
    rwa [huniq j hj] at hh
  · intro hh
    exact ⟨i, hti, fun h => False.elim (ht.1.ne h),
      fun h => False.elim (ht.2.ne h), hh⟩

theorem planar_carrier_eq_oblique_image :
    F.symm '' B.carrier =
      (fun q : EuclideanSpace ℝ (Fin 2) => collarParameterEquiv.symm
        (B.cuts.coordinates B.open_domain B.smooth_lower (collarParameterEquiv q))) '' B.band := by
  rw [B.carrier_eq_image, image_image]
  apply image_congr
  intro q hq
  have hsource : collarParameterEquiv.symm
      (B.cuts.coordinates B.open_domain B.smooth_lower (collarParameterEquiv q)) ∈ F.source :=
    (B.band_subset_source hq).2
  exact F.left_inv hsource

theorem planar_carrier_open_top_eventually_iff
    (i : Fin B.interface.count) {t : ℝ}
    (ht : t ∈ Ioo (B.cut i.castSucc) (B.cut i.succ)) :
    ∀ᶠ z in 𝓝 (collarParameterEquiv.symm
      (B.cuts.coordinates B.open_domain B.smooth_lower (t, B.upperGraph i t))),
      z ∈ F.symm '' B.carrier ↔ B.topLineExcess i z ≤ 0 := by
  let G := B.cuts.coordinates B.open_domain B.smooth_lower
  let q : ℝ × ℝ := (t, B.upperGraph i t)
  have hti : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ) := ⟨ht.1.le, ht.2.le⟩
  have hq : q ∈ G.source :=
    (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).band_subset_coordinates_source
      B.open_domain B.smooth_lower ⟨hti,
        ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).upperGraph_bounds hti).1.le,
        le_rfl⟩
  have hzinv : ContinuousAt (fun z : EuclideanSpace ℝ (Fin 2) => G.symm (collarParameterEquiv z))
      (collarParameterEquiv.symm (G q)) := by
    apply (G.continuousAt_symm (G.map_source hq)).comp_of_eq
      collarParameterEquiv.continuous.continuousAt
    exact collarParameterEquiv.apply_symm_apply _
  have hevent := hzinv.eventually (by
    simpa only [collarParameterEquiv.apply_symm_apply, G.left_inv hq] using
      B.band_open_top_eventually_mem_iff_topLineExcess i ht)
  have htarget := (G.open_target.preimage collarParameterEquiv.continuous).mem_nhds
    (show collarParameterEquiv (collarParameterEquiv.symm (G q)) ∈ G.target by
      simpa using G.map_source hq)
  filter_upwards [hevent, htarget] with z hz hzt
  change collarParameterEquiv.symm (G.symm (collarParameterEquiv z)) ∈ B.band ↔
    B.topLineExcess i (collarParameterEquiv.symm (G (G.symm (collarParameterEquiv z)))) ≤ 0 at hz
  rw [G.right_inv hzt, collarParameterEquiv.symm_apply_apply] at hz
  rw [← hz, B.planar_carrier_eq_oblique_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwG : collarParameterEquiv w ∈ G.source := (B.band_subset_source hw).1.1.2
    change collarParameterEquiv.symm (G.symm (collarParameterEquiv
      (collarParameterEquiv.symm (G (collarParameterEquiv w))))) ∈ B.band
    simpa only [collarParameterEquiv.apply_symm_apply, G.left_inv hwG,
      collarParameterEquiv.symm_apply_apply] using hw
  · intro hw
    refine ⟨collarParameterEquiv.symm (G.symm (collarParameterEquiv z)), hw, ?_⟩
    change collarParameterEquiv.symm (G (collarParameterEquiv
      (collarParameterEquiv.symm (G.symm (collarParameterEquiv z))))) = z
    simp only [collarParameterEquiv.apply_symm_apply, G.right_inv hzt,
      collarParameterEquiv.symm_apply_apply]

private theorem inverse_piece_eventually_order
    (i : Fin B.interface.count) {x : ℝ}
    (hx : x ∈ Icc (B.interface.cut i.castSucc) (B.interface.cut i.succ)) :
    let C := B.interface.pieceCoordinates B.open_domain B.smooth_lower i
    ∀ᶠ t in 𝓝 (C.parameter x),
      (C.parameter.symm t ≤ x ↔ t ≤ C.parameter x) ∧
        (x ≤ C.parameter.symm t ↔ C.parameter x ≤ t) := by
  dsimp only
  let C := B.interface.pieceCoordinates B.open_domain B.smooth_lower i
  have hd : HasDerivAt (fun y => B.interface.projection i y - B.interface.projection i x)
      (deriv (B.interface.projection i) x) x :=
    (((B.interface.smooth_projection B.smooth_lower i) x
      (B.interface.cell_subset_pieceDomain i hx)).contDiffAt
        ((B.interface.isOpen_pieceDomain B.open_domain B.smooth_lower i).mem_nhds
          (B.interface.cell_subset_pieceDomain i hx))).differentiableAt (by simp)
            |>.hasDerivAt.sub_const _
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos
    (f := fun y => B.interface.projection i y - B.interface.projection i x) (x₀ := x)
    (by rw [hd.deriv]; exact B.interface.positive_deriv_projection B.open_domain B.smooth_lower i hx)
    (by exact sub_self _)
  have hinv := C.parameter.continuousAt_symm (C.parameter.map_source (C.source_contains hx))
  have hsign' := hinv.eventually (by
    simpa only [C.parameter.left_inv (C.source_contains hx)] using hsign)
  filter_upwards [hsign', C.parameter.open_target.mem_nhds
    (C.parameter.map_source (C.source_contains hx))] with t ht htC
  have htx : B.interface.projection i (C.parameter.symm t) = t := by
    rw [← C.map_eq, C.parameter.right_inv htC]
  rw [htx, ← C.map_eq] at ht
  constructor
  · have he := congrArg (fun z : SignType => z ≤ 0) ht
    simpa only [sign_nonpos_iff, sub_nonpos] using Iff.of_eq he.symm
  · have he := congrArg (fun z : SignType => 0 ≤ z) ht
    simpa only [sign_nonneg_iff, sub_nonneg] using Iff.of_eq he.symm

private theorem topGraphs_eventually_compare_on_line
    (i j : Fin B.interface.count) {t : ℝ}
    (hi : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ))
    (hj : t ∈ Icc (B.cut j.castSucc) (B.cut j.succ)) :
    let C := B.interface.pieceCoordinates B.open_domain B.smooth_lower i
    ∀ᶠ s in 𝓝 t, B.upperGraph i s ≤ B.upperGraph j s ↔
      B.interface.piece i (C.parameter.symm s) ≤ B.interface.piece j (C.parameter.symm s) := by
  dsimp only
  let C := B.interface.pieceCoordinates B.open_domain B.smooth_lower i
  have hti : t ∈ C.parameter.target := C.parameter_mem_target hi
  have hh : ContinuousAt (fun s => (s, B.upperGraph i s)) t :=
    continuousAt_id.prodMk (((C.smooth_upperGraph B.smooth_lower).continuousOn t hti).continuousAt
      (C.parameter.open_target.mem_nhds hti))
  have hevent := hh.eventually (by
    simpa only [B.upperGraphs_eq_on_overlap hi hj] using
      B.topLineExcess_eventually_nonpos_iff j hj)
  filter_upwards [hevent, C.parameter.open_target.mem_nhds hti] with s hs hsC
  change B.topLineExcess j (collarParameterEquiv.symm
    (B.cuts.coordinates B.open_domain B.smooth_lower (s, B.upperGraph i s))) ≤ 0 ↔
      B.upperGraph i s ≤ B.upperGraph j s at hs
  rw [topLineExcess, collarParameterEquiv.apply_symm_apply, B.cuts.coordinates_apply,
    B.upperGraph_strip_eq_of_mem_target i hsC] at hs
  simpa only [sub_nonpos] using hs.symm

private theorem band_internal_top_eventually_two_cells
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (B.cut i.succ, B.interface.height i.succ),
      collarParameterEquiv.symm q ∈ B.band ↔
        (q.1 ≤ B.cut i.succ ∧ q.2 ≤ B.upperGraph i q.1) ∨
        (B.cut i.succ ≤ q.1 ∧ q.2 ≤ B.upperGraph j q.1) := by
  have hi : B.cut i.succ ∈ Icc (B.cut i.castSucc) (B.cut i.succ) :=
    ⟨(B.cut_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩
  have hj : B.cut i.succ ∈ Icc (B.cut j.castSucc) (B.cut j.succ) := by
    rw [hij]
    exact ⟨le_rfl, (B.cut_strictMono Fin.castSucc_lt_succ).le⟩
  have hI : B.cut i.succ ∈ Icc (0 : ℝ) 1 := by
    rw [← B.cut_interval_cover]
    exact mem_iUnion.mpr ⟨i, hi⟩
  have hg := B.band_top_eventually_mem_iff_active_constraints
    (q := collarParameterEquiv.symm (B.cut i.succ, B.interface.height i.succ))
    (by simpa using hI) (by simp [B.height_eq_upperGraph hi, (B.upperGraph_endpoints i).2])
  have hc : ContinuousAt (fun q : ℝ × ℝ => collarParameterEquiv.symm q)
      (B.cut i.succ, B.interface.height i.succ) := collarParameterEquiv.symm.continuous.continuousAt
  filter_upwards [hc.eventually hg] with q hq
  simp only [collarParameterEquiv.apply_symm_apply] at hq
  rw [hq]
  have hunique (k : Fin B.interface.count)
      (hk : B.cut i.succ ∈ Icc (B.cut k.castSucc) (B.cut k.succ)) : k = i ∨ k = j := by
    have hk₁ : k.castSucc ≤ i.succ := B.cut_strictMono.le_iff_le.mp hk.1
    have hk₂ : i.succ ≤ k.succ := B.cut_strictMono.le_iff_le.mp hk.2
    have he : (i : ℕ) + 1 = j := congrArg Fin.val hij
    have hk₁' : (k : ℕ) ≤ (i : ℕ) + 1 := hk₁
    have hk₂' : (i : ℕ) + 1 ≤ (k : ℕ) + 1 := hk₂
    rcases (show (k : ℕ) = i ∨ (k : ℕ) = j by omega) with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  constructor
  · rintro ⟨k, hk, hl, hr, htop⟩
    rcases hunique k hk with rfl | rfl
    · exact Or.inl ⟨hr rfl, htop⟩
    · exact Or.inr ⟨hij.symm ▸ hl (congrArg B.cut hij.symm), htop⟩
  · rintro (⟨hside, htop⟩ | ⟨hside, htop⟩)
    · exact ⟨i, hi, fun h => False.elim ((B.cut_strictMono Fin.castSucc_lt_succ).ne h),
        fun _ => hside, htop⟩
    · refine ⟨j, hj, fun _ => hij ▸ hside, ?_, htop⟩
      intro h
      exact False.elim ((B.cut_strictMono (Fin.castSucc_lt_succ (i := j))).ne
        ((congrArg B.cut hij.symm).trans h))

private theorem affine_line_difference
    (f g : ℝ →ᵃ[ℝ] ℝ) {x : ℝ} (hx : f x = g x) (y : ℝ) :
    f y - g y = (f.linear 1 - g.linear 1) * (y - x) := by
  have hf : f y - f x = (y - x) * f.linear 1 := by
    have h := f.linearMap_vsub y x
    simp only [vsub_eq_sub] at h
    rw [show y - x = (y - x) • (1 : ℝ) by simp, map_smul] at h
    exact h.symm
  have hg : g y - g x = (y - x) * g.linear 1 := by
    have h := g.linearMap_vsub y x
    simp only [vsub_eq_sub] at h
    rw [show y - x = (y - x) • (1 : ℝ) by simp, map_smul] at h
    exact h.symm
  rw [hx] at hf
  linarith

private theorem internal_top_graph_order
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    ∀ᶠ s in 𝓝 (B.cut i.succ),
      (s ≤ B.cut i.succ →
        (if (B.interface.piece i).linear 1 ≤ (B.interface.piece j).linear 1 then
          B.upperGraph j s ≤ B.upperGraph i s else B.upperGraph i s ≤ B.upperGraph j s)) ∧
      (B.cut i.succ ≤ s →
        (if (B.interface.piece i).linear 1 ≤ (B.interface.piece j).linear 1 then
          B.upperGraph i s ≤ B.upperGraph j s else B.upperGraph j s ≤ B.upperGraph i s)) := by
  let C := B.interface.pieceCoordinates B.open_domain B.smooth_lower i
  let x := B.interface.cut i.succ
  let t := B.cut i.succ
  have hi : t ∈ Icc (B.cut i.castSucc) (B.cut i.succ) :=
    ⟨(B.cut_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩
  have hj : t ∈ Icc (B.cut j.castSucc) (B.cut j.succ) := by
    dsimp [t]
    rw [hij]
    exact ⟨le_rfl, (B.cut_strictMono Fin.castSucc_lt_succ).le⟩
  have hx : x ∈ Icc (B.interface.cut i.castSucc) (B.interface.cut i.succ) :=
    ⟨(B.interface.cut_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩
  have htx : C.parameter x = t := by
    rw [C.map_eq]
    exact (B.interface.projection_endpoints i).2
  have hord := B.inverse_piece_eventually_order i hx
  change ∀ᶠ s in 𝓝 (C.parameter x),
    (C.parameter.symm s ≤ x ↔ s ≤ C.parameter x) ∧
      (x ≤ C.parameter.symm s ↔ C.parameter x ≤ s) at hord
  rw [htx] at hord
  have hline : B.interface.piece i x = B.interface.piece j x := by
    dsimp [x]
    rw [(B.interface.piece_endpoints i).2, hij, ← (B.interface.piece_endpoints j).1]
  let D := B.interface.pieceCoordinates B.open_domain B.smooth_lower j
  have hxj : x ∈ Icc (B.interface.cut j.castSucc) (B.interface.cut j.succ) := by
    dsimp [x]
    rw [hij]
    exact ⟨le_rfl, (B.interface.cut_strictMono Fin.castSucc_lt_succ).le⟩
  have htxj : D.parameter x = t := by
    rw [D.map_eq]
    dsimp [x, t]
    rw [hij]
    exact (B.interface.projection_endpoints j).1
  have hordj := B.inverse_piece_eventually_order j hxj
  change ∀ᶠ s in 𝓝 (D.parameter x),
    (D.parameter.symm s ≤ x ↔ s ≤ D.parameter x) ∧
      (x ≤ D.parameter.symm s ↔ D.parameter x ≤ s) at hordj
  rw [htxj] at hordj
  filter_upwards [hord, hordj, B.topGraphs_eventually_compare_on_line i j hi hj,
    B.topGraphs_eventually_compare_on_line j i hj hi] with s hs hs' hc hc'
  have hdiff := affine_line_difference (B.interface.piece i) (B.interface.piece j) hline
    (C.parameter.symm s)
  have hdiff' := affine_line_difference (B.interface.piece i) (B.interface.piece j) hline
    (D.parameter.symm s)
  constructor <;> intro hside
  · have hxle := hs.1.mpr hside
    have hxle' := hs'.1.mpr hside
    split_ifs with h
    · apply hc'.mpr
      nlinarith [mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr h) (sub_nonpos.mpr hxle')]
    · apply hc.mpr
      nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (le_of_not_ge h))
        (sub_nonpos.mpr hxle)]
  · have hxle := hs.2.mpr hside
    have hxle' := hs'.2.mpr hside
    split_ifs with h
    · apply hc.mpr
      nlinarith [mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h) (sub_nonneg.mpr hxle)]
    · apply hc'.mpr
      nlinarith [mul_nonneg (sub_nonneg.mpr (le_of_not_ge h)) (sub_nonneg.mpr hxle')]

theorem band_internal_top_eventually_mem_iff_affine_sectors
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (B.cut i.succ, B.interface.height i.succ),
      collarParameterEquiv.symm q ∈ B.band ↔
        if (B.interface.piece i).linear 1 ≤ (B.interface.piece j).linear 1 then
          B.topLineExcess i (collarParameterEquiv.symm
            (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0 ∨
          B.topLineExcess j (collarParameterEquiv.symm
            (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0
        else
          B.topLineExcess i (collarParameterEquiv.symm
            (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0 ∧
          B.topLineExcess j (collarParameterEquiv.symm
            (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0 := by
  have hi : B.cut i.succ ∈ Icc (B.cut i.castSucc) (B.cut i.succ) :=
    ⟨(B.cut_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩
  have hj : B.cut i.succ ∈ Icc (B.cut j.castSucc) (B.cut j.succ) := by
    rw [hij]
    exact ⟨le_rfl, (B.cut_strictMono Fin.castSucc_lt_succ).le⟩
  have heq : B.upperGraph j (B.cut i.succ) = B.interface.height i.succ := by
    rw [hij, (B.upperGraph_endpoints j).1]
  have hsi := B.topLineExcess_eventually_nonpos_iff i hi
  have hsj := B.topLineExcess_eventually_nonpos_iff j hj
  rw [(B.upperGraph_endpoints i).2] at hsi
  rw [heq] at hsj
  have ho := (continuousAt_fst : ContinuousAt Prod.fst
    (B.cut i.succ, B.interface.height i.succ)).eventually (B.internal_top_graph_order i j hij)
  filter_upwards [B.band_internal_top_eventually_two_cells i j hij, ho, hsi, hsj]
    with q hq horder hiq hjq
  rw [hq]
  split_ifs with hslope
  · rw [hiq, hjq]
    simp only [if_pos hslope] at horder
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩)
      · exact Or.inl h
      · exact Or.inr h
    · intro h
      rcases le_total q.1 (B.cut i.succ) with hleft | hright
      · exact Or.inl ⟨hleft, h.elim id (fun hh => hh.trans (horder.1 hleft))⟩
      · exact Or.inr ⟨hright, h.elim (fun hh => hh.trans (horder.2 hright)) id⟩
  · rw [hiq, hjq]
    simp only [if_neg hslope] at horder
    constructor
    · rintro (⟨hside, h⟩ | ⟨hside, h⟩)
      · exact ⟨h, h.trans (horder.1 hside)⟩
      · exact ⟨h.trans (horder.2 hside), h⟩
    · intro h
      exact (le_total q.1 (B.cut i.succ)).elim
        (fun hs => Or.inl ⟨hs, h.1⟩) (fun hs => Or.inr ⟨hs, h.2⟩)

noncomputable def planarTopVertex (k : Fin (B.interface.count + 1)) :
    EuclideanSpace ℝ (Fin 2) := collarParameterEquiv.symm
      (B.interface.cut k, lo (B.interface.cut k) + B.interface.height k)

theorem planar_carrier_internal_top_eventually_iff
    (i j : Fin B.interface.count) (hij : i.succ = j.castSucc) :
    ∀ᶠ z in 𝓝 (B.planarTopVertex i.succ), z ∈ F.symm '' B.carrier ↔
      if (B.interface.piece i).linear 1 ≤ (B.interface.piece j).linear 1 then
        B.topLineExcess i z ≤ 0 ∨ B.topLineExcess j z ≤ 0
      else B.topLineExcess i z ≤ 0 ∧ B.topLineExcess j z ≤ 0 := by
  let G := B.cuts.coordinates B.open_domain B.smooth_lower
  let q : ℝ × ℝ := (B.cut i.succ, B.interface.height i.succ)
  have hi : B.cut i.succ ∈ Icc (B.cut i.castSucc) (B.cut i.succ) :=
    ⟨(B.cut_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩
  have hq : q ∈ G.source := by
    have h : (B.cut i.succ, B.upperGraph i (B.cut i.succ)) ∈ G.source :=
      (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).band_subset_coordinates_source
      B.open_domain B.smooth_lower ⟨hi,
        ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).upperGraph_bounds hi).1.le,
        le_rfl⟩
    simpa only [(B.upperGraph_endpoints i).2] using h
  have hmap : collarParameterEquiv.symm (G q) = B.planarTopVertex i.succ := by
    have htC := (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter_mem_target hi
    have h := B.upperGraph_strip_eq_of_mem_target i htC
    have hparameter : (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter.symm
        (B.cut i.succ) = B.interface.cut i.succ := by
      have hp := (B.interface.pieceCoordinates B.open_domain B.smooth_lower i).parameter.left_inv
        ((B.interface.pieceCoordinates B.open_domain B.smooth_lower i).source_contains
          ⟨(B.interface.cut_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩)
      rwa [(B.interface.pieceCoordinates B.open_domain B.smooth_lower i).map_eq,
        (B.interface.projection_endpoints i).2] at hp
    rw [(B.upperGraph_endpoints i).2, hparameter, (B.interface.piece_endpoints i).2] at h
    change collarParameterEquiv.symm
      (B.cuts.coordinates B.open_domain B.smooth_lower q) = _
    rw [B.cuts.coordinates_apply]
    exact congrArg collarParameterEquiv.symm h
  rw [← hmap]
  have hzinv : ContinuousAt (fun z : EuclideanSpace ℝ (Fin 2) => G.symm (collarParameterEquiv z))
      (collarParameterEquiv.symm (G q)) := by
    apply (G.continuousAt_symm (G.map_source hq)).comp_of_eq
      collarParameterEquiv.continuous.continuousAt
    exact collarParameterEquiv.apply_symm_apply _
  have hevent := hzinv.eventually (by
    simpa only [collarParameterEquiv.apply_symm_apply, G.left_inv hq] using
      B.band_internal_top_eventually_mem_iff_affine_sectors i j hij)
  have htarget := (G.open_target.preimage collarParameterEquiv.continuous).mem_nhds
    (show collarParameterEquiv (collarParameterEquiv.symm (G q)) ∈ G.target by
      simpa using G.map_source hq)
  filter_upwards [hevent, htarget] with z hz hzt
  have hzG : B.cuts.coordinates B.open_domain B.smooth_lower (G.symm (collarParameterEquiv z)) =
      collarParameterEquiv z := G.right_inv hzt
  rw [hzG, collarParameterEquiv.symm_apply_apply] at hz
  rw [← hz, B.planar_carrier_eq_oblique_image]
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hwG : collarParameterEquiv w ∈ G.source := (B.band_subset_source hw).1.1.2
    change collarParameterEquiv.symm (G.symm (collarParameterEquiv
      (collarParameterEquiv.symm (G (collarParameterEquiv w))))) ∈ B.band
    simpa only [collarParameterEquiv.apply_symm_apply, G.left_inv hwG,
      collarParameterEquiv.symm_apply_apply] using hw
  · intro hw
    refine ⟨collarParameterEquiv.symm (G.symm (collarParameterEquiv z)), hw, ?_⟩
    change collarParameterEquiv.symm (G (collarParameterEquiv
      (collarParameterEquiv.symm (G.symm (collarParameterEquiv z))))) = z
    simp only [collarParameterEquiv.apply_symm_apply, G.right_inv hzt,
      collarParameterEquiv.symm_apply_apply]

end PoincareConjecture.Topology.Surface.ObliqueBandFaces
