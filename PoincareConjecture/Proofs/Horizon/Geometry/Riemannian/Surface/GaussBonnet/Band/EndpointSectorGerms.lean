import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Band.SectorGerms








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology Manifold ContDiff
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

private theorem eventually_graph_nonneg_of_hasStrictFDerivAt
    {f : (ℝ × ℝ) → ℝ} {f' : (ℝ × ℝ) →L[ℝ] ℝ} {h : ℝ → ℝ} {t : ℝ}
    (hf : HasStrictFDerivAt f f' (t, h t)) (hpos : 0 < f' (0, 1))
    (hh : ContinuousAt h t) (hzero : ∀ᶠ s in 𝓝 t, f (s, h s) = 0) :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (t, h t), 0 ≤ f q ↔ h q.1 ≤ q.2 := by
  have hpair : Tendsto (fun q : ℝ × ℝ => (q, (q.1, h q.1)))
      (𝓝 (t, h t)) (𝓝 ((t, h t), (t, h t))) :=
    continuousAt_id.prodMk (continuousAt_fst.prodMk (hh.comp continuousAt_fst))
  have hbound := hpair.eventually (hf.isLittleO.bound (half_pos hpos))
  have hz := (continuousAt_fst : ContinuousAt Prod.fst (t, h t)).eventually hzero
  filter_upwards [hbound, hz] with q hq hqzero
  have hdiff : q - (q.1, h q.1) = (q.2 - h q.1) • (0, 1) := by
    ext <;> simp
  have hn : ‖q - (q.1, h q.1)‖ = |q.2 - h q.1| := by simp [hdiff]
  rw [hqzero, sub_zero, hn, hdiff, map_smul] at hq
  change |f q - (q.2 - h q.1) * f' (0, 1)| ≤
    f' (0, 1) / 2 * |q.2 - h q.1| at hq
  constructor
  · intro hnonneg
    by_contra hbad
    have hn : q.2 - h q.1 < 0 := sub_neg.mpr (lt_of_not_ge hbad)
    rw [abs_of_neg hn] at hq
    have hb := (abs_le.mp hq).2
    nlinarith [mul_neg_of_neg_of_pos hn hpos]
  · intro hle
    by_cases he : q.2 = h q.1
    · have hqeq : q = (q.1, h q.1) := Prod.ext rfl he
      rw [hqeq, hqzero]
    · have hp : 0 < q.2 - h q.1 := sub_pos.mpr (lt_of_le_of_ne hle (Ne.symm he))
      rw [abs_of_pos hp] at hq
      have hb := (abs_le.mp hq).1
      nlinarith [mul_pos hp hpos]


noncomputable def transverseCutLine (lo : ℝ → ℝ) (a u w : ℝ) :
    EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
  ((w • ((LinearMap.fst ℝ ℝ ℝ).toAffineMap - AffineMap.const ℝ (ℝ × ℝ) a)) -
    u • ((LinearMap.snd ℝ ℝ ℝ).toAffineMap - AffineMap.const ℝ (ℝ × ℝ) (lo a))).comp
      collarParameterEquiv.toContinuousLinearMap.toLinearMap.toAffineMap

@[simp] theorem transverseCutLine_apply (lo : ℝ → ℝ) (a u w : ℝ)
    (q : EuclideanSpace ℝ (Fin 2)) :
    transverseCutLine lo a u w q =
      w * ((collarParameterEquiv q).1 - a) - u * ((collarParameterEquiv q).2 - lo a) := rfl



theorem transverseCutLine_linear_ne_zero
    {lo : ℝ → ℝ} {a u w : ℝ} (C : TransverseCutCoordinates lo a u w) :
    (transverseCutLine lo a u w).linear ≠ 0 := by
  intro h
  have hx : (transverseCutLine lo a u w).linear (collarParameterEquiv.symm (1, 0)) = w := by
    simp [transverseCutLine]
  have hy : (transverseCutLine lo a u w).linear (collarParameterEquiv.symm (0, 1)) = -u := by
    simp [transverseCutLine]
  rw [h, LinearMap.zero_apply] at hx hy
  have hw : w = 0 := hx.symm
  have hu : u = 0 := neg_eq_zero.mp hy.symm
  have heq : (C.parameter : ℝ → ℝ) = fun _ => 0 := by
    funext r
    rw [C.map_eq]
    simp [transverseCutHeight, hu, hw]
  have hp := C.positive_deriv 0 C.zero_mem_source
  rw [heq] at hp
  simp at hp



theorem transverseCutLine_eventually_sides
    {lo : ℝ → ℝ} {a u w η : ℝ} (C : TransverseCutCoordinates lo a u w)
    (hη : η ∈ C.parameter.target) (hlo : ContDiffAt ℝ ∞ lo (C.horizontal η)) :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (η, C.horizontal η),
      (transverseCutLine lo a u w
        (collarParameterEquiv.symm (q.2, lo q.2 + q.1)) ≤ 0 ↔ q.2 ≤ C.horizontal q.1) ∧
      (0 ≤ transverseCutLine lo a u w
        (collarParameterEquiv.symm (q.2, lo q.2 + q.1)) ↔ C.horizontal q.1 ≤ q.2) := by
  let f : (ℝ × ℝ) → ℝ := fun q => w * (q.2 - a) - u * (lo q.2 + q.1 - lo a)
  have hfc : ContDiffAt ℝ ∞ f (η, C.horizontal η) :=
    (contDiffAt_const.mul (contDiffAt_snd.sub contDiffAt_const)).sub
      (contDiffAt_const.mul (((hlo.comp (η, C.horizontal η) contDiffAt_snd).add contDiffAt_fst).sub
        contDiffAt_const))
  have hdlo := (hlo.differentiableAt (by simp)).hasDerivAt
  have hd : HasDerivAt (fun x => f (η, x)) (w - u * deriv lo (C.horizontal η)) (C.horizontal η) := by
    convert! (((hasDerivAt_id _).sub_const a).const_mul w).sub
      (((hdlo.add_const η).sub_const (lo a)).const_mul u) using 1
    simp
  have heval : fderiv ℝ f (η, C.horizontal η) (0, 1) = w - u * deriv lo (C.horizontal η) := by
    have h := (hfc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt (C.horizontal η)
      ((hasDerivAt_const _ η).prodMk (hasDerivAt_id _))
    exact h.unique hd
  have hpos : 0 < w - u * deriv lo (C.horizontal η) := by
    have hdx : HasDerivAt (fun r : ℝ => a + r * u) u (C.parameter.symm η) := by
      simpa using ((hasDerivAt_id (C.parameter.symm η)).mul_const u).const_add a
    have hdlo' : HasDerivAt lo (deriv lo (C.horizontal η)) (a + C.parameter.symm η * u) := hdlo
    have hheight : HasDerivAt C.parameter (w - deriv lo (C.horizontal η) * u) (C.parameter.symm η) := by
      have heq : (C.parameter : ℝ → ℝ) = transverseCutHeight lo a u w := funext C.map_eq
      rw [heq]
      convert! (((hasDerivAt_id (C.parameter.symm η)).mul_const w).const_add (lo a)).sub
        (hdlo'.comp (C.parameter.symm η) hdx) using 1
      simp
    have h := C.positive_deriv (C.parameter.symm η) (C.parameter.map_target hη)
    rw [hheight.deriv] at h
    nlinarith
  have hh : ContinuousAt C.horizontal η :=
    C.smooth_horizontal.continuousOn.continuousAt (C.parameter.open_target.mem_nhds hη)
  have hz : ∀ᶠ s in 𝓝 η, f (s, C.horizontal s) = 0 := by
    filter_upwards [C.parameter.open_target.mem_nhds hη] with s hs
    have hline := congrArg Prod.snd (C.line_identity hs)
    change lo (C.horizontal s) + s = lo a + C.parameter.symm s * w at hline
    dsimp only [f]
    rw [hline]
    dsimp [TransverseCutCoordinates.horizontal]
    ring
  have hf := hfc.hasStrictFDerivAt (by simp)
  have hp : 0 < fderiv ℝ f (η, C.horizontal η) (0, 1) := heval.symm ▸ hpos
  filter_upwards [eventually_graph_side_of_hasStrictFDerivAt hf hp hh hz,
    eventually_graph_nonneg_of_hasStrictFDerivAt hf hp hh hz] with q hle hge
  simpa only [transverseCutLine_apply, collarParameterEquiv.apply_symm_apply] using And.intro hle hge

end PoincareConjecture.Topology.Surface

namespace PoincareConjecture.Topology.Surface.ObliqueBandFaces

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M}
  {lo : ℝ → ℝ} {a b ua wa ub wb ra rb : ℝ}
  (B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)

private theorem transverseCutLine_eventually_oblique_sides
    {c u w ξ η : ℝ} (C : TransverseCutCoordinates lo c u w)
    (hη : η ∈ Ioo (-B.cuts.radius) B.cuts.radius)
    (hCη : η ∈ C.parameter.target)
    (hcurve : ∀ z, C.horizontal z = B.cuts.A z + ξ * (B.cuts.B z - B.cuts.A z))
    (hlo : ContDiffAt ℝ ∞ lo (C.horizontal η)) :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (ξ, η),
      (transverseCutLine lo c u w (collarParameterEquiv.symm
        (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0 ↔ q.1 ≤ ξ) ∧
      (0 ≤ transverseCutLine lo c u w (collarParameterEquiv.symm
        (B.cuts.coordinates B.open_domain B.smooth_lower q)) ↔ ξ ≤ q.1) := by
  have hA : ContinuousAt B.cuts.A η :=
    B.cuts.smooth_A.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hη)
  have hBc : ContinuousAt B.cuts.B η :=
    B.cuts.smooth_B.continuousOn.continuousAt (isOpen_Ioo.mem_nhds hη)
  have hA' : ContinuousAt (fun q : ℝ × ℝ => B.cuts.A q.2) (ξ, η) :=
    ContinuousAt.comp (g := B.cuts.A) (f := Prod.snd) hA continuousAt_snd
  have hB' : ContinuousAt (fun q : ℝ × ℝ => B.cuts.B q.2) (ξ, η) :=
    ContinuousAt.comp (g := B.cuts.B) (f := Prod.snd) hBc continuousAt_snd
  have hmap : ContinuousAt (fun q : ℝ × ℝ =>
      (q.2, B.cuts.A q.2 + q.1 * (B.cuts.B q.2 - B.cuts.A q.2))) (ξ, η) :=
    continuousAt_snd.prodMk (hA'.add (continuousAt_fst.mul (hB'.sub hA')))
  have hg := hmap.eventually (by
    simpa only [hcurve η] using transverseCutLine_eventually_sides C hCη hlo)
  have hz := (continuousAt_snd : ContinuousAt Prod.snd (ξ, η)).eventually
    (isOpen_Ioo.mem_nhds hη)
  filter_upwards [hg, hz] with q hq hqη
  have hgap := B.cuts.separated q.2 hqη
  simp only [B.cuts.coordinates_apply, obliqueStripMap]
  change (transverseCutLine lo c u w (collarParameterEquiv.symm
    (B.cuts.A q.2 + q.1 * (B.cuts.B q.2 - B.cuts.A q.2),
      lo (B.cuts.A q.2 + q.1 * (B.cuts.B q.2 - B.cuts.A q.2)) + q.2)) ≤ 0 ↔ _) ∧ _
  rw [hq.1, hq.2, hcurve q.2]
  constructor <;> constructor <;> intro h <;> nlinarith


noncomputable def endpointCutFunctional (_B : ObliqueBandFaces F lo a b ua wa ub wb ra rb)
    (right : Bool) :
    EuclideanSpace ℝ (Fin 2) →ᵃ[ℝ] ℝ :=
  if right then transverseCutLine lo b ub wb else -transverseCutLine lo a ua wa

theorem endpointCutFunctional_linear_ne_zero (right : Bool) :
    (B.endpointCutFunctional right).linear ≠ 0 := by
  cases right
  · have h := transverseCutLine_linear_ne_zero B.cuts.left
    simpa [endpointCutFunctional] using h
  · exact transverseCutLine_linear_ne_zero B.cuts.right

theorem endpointCutFunctional_first_vertex :
    B.endpointCutFunctional false (B.planarTopVertex 0) = 0 := by
  change -transverseCutLine lo a ua wa (collarParameterEquiv.symm
    (B.interface.cut 0, lo (B.interface.cut 0) + B.interface.height 0)) = 0
  rw [B.interface.first_vertex, transverseCutLine_apply, collarParameterEquiv.apply_symm_apply]
  ring

theorem endpointCutFunctional_last_vertex :
    B.endpointCutFunctional true (B.planarTopVertex (Fin.last B.interface.count)) = 0 := by
  change transverseCutLine lo b ub wb (collarParameterEquiv.symm
    (B.interface.cut (Fin.last B.interface.count),
      lo (B.interface.cut (Fin.last B.interface.count)) + B.interface.height (Fin.last B.interface.count))) = 0
  rw [B.interface.last_vertex, transverseCutLine_apply, collarParameterEquiv.apply_symm_apply]
  ring


theorem firstCutFunctional_eventually_nonpos_iff :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (0, B.interface.height 0),
      B.endpointCutFunctional false (collarParameterEquiv.symm
        (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0 ↔ 0 ≤ q.1 := by
  have hη := B.interface.vertex_height_bounds 0
  have hx : B.cuts.A (B.interface.height 0) = B.interface.cut 0 := by
    change B.cuts.left.horizontal (B.interface.height 0) = _
    rw [B.interface.height_first, B.cuts.left.horizontal_parameter B.interface.left_parameter_mem,
      B.interface.cut_first]
  have hdom : B.interface.cut 0 ∈ B.domain :=
    B.interface.cell_domain B.firstCell ⟨le_rfl,
      (B.interface.cut_strictMono (Fin.castSucc_lt_succ (i := B.firstCell))).le⟩
  have hlo : ContDiffAt ℝ ∞ lo (B.cuts.left.horizontal (B.interface.height 0)) := by
    rw [show B.cuts.left.horizontal (B.interface.height 0) = B.interface.cut 0 from hx]
    exact (B.smooth_lower _ hdom).contDiffAt (B.open_domain.mem_nhds hdom)
  have hg := B.transverseCutLine_eventually_oblique_sides B.cuts.left (ξ := 0)
    (η := B.interface.height 0) ⟨by linarith [B.cuts.radius_pos], hη.2⟩
    (by rw [B.interface.height_first]; exact B.cuts.left.parameter.map_source B.interface.left_parameter_mem)
    (fun _ => by simp) hlo
  filter_upwards [hg] with q hq
  change -transverseCutLine lo a ua wa _ ≤ 0 ↔ _
  simpa only [neg_nonpos] using hq.2

private theorem lastCell_succ : B.lastCell.succ = Fin.last B.interface.count := by
  apply Fin.ext
  simp only [lastCell, Fin.val_succ, Fin.val_last]
  have hn := B.interface.count_pos
  omega


theorem lastCutFunctional_eventually_nonpos_iff :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (1, B.interface.height (Fin.last B.interface.count)),
      B.endpointCutFunctional true (collarParameterEquiv.symm
        (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0 ↔ q.1 ≤ 1 := by
  have hη := B.interface.vertex_height_bounds (Fin.last B.interface.count)
  have hx : B.cuts.B (B.interface.height (Fin.last B.interface.count)) =
      B.interface.cut (Fin.last B.interface.count) := by
    change B.cuts.right.horizontal (B.interface.height (Fin.last B.interface.count)) = _
    rw [B.interface.height_last, B.cuts.right.horizontal_parameter B.interface.right_parameter_mem,
      B.interface.cut_last]
  have hdom : B.interface.cut (Fin.last B.interface.count) ∈ B.domain := by
    rw [← B.lastCell_succ]
    exact B.interface.cell_domain B.lastCell
      ⟨(B.interface.cut_strictMono Fin.castSucc_lt_succ).le, le_rfl⟩
  have hlo : ContDiffAt ℝ ∞ lo (B.cuts.right.horizontal
      (B.interface.height (Fin.last B.interface.count))) := by
    rw [show B.cuts.right.horizontal (B.interface.height (Fin.last B.interface.count)) =
      B.interface.cut (Fin.last B.interface.count) from hx]
    exact (B.smooth_lower _ hdom).contDiffAt (B.open_domain.mem_nhds hdom)
  have hg := B.transverseCutLine_eventually_oblique_sides B.cuts.right (ξ := 1)
    (η := B.interface.height (Fin.last B.interface.count)) ⟨by linarith [B.cuts.radius_pos], hη.2⟩
    (by rw [B.interface.height_last]; exact B.cuts.right.parameter.map_source B.interface.right_parameter_mem)
    (fun _ => by simp) hlo
  filter_upwards [hg] with q hq
  simpa only [endpointCutFunctional, ↓reduceIte] using hq.1



theorem band_first_top_eventually_mem_iff_affine_sector :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (0, B.interface.height 0),
      collarParameterEquiv.symm q ∈ B.band ↔
        B.endpointCutFunctional false (collarParameterEquiv.symm
          (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0 ∧
        B.topLineFunctional B.firstCell (collarParameterEquiv.symm
          (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0 := by
  have hi : (0 : ℝ) ∈ Icc (B.cut B.firstCell.castSucc) (B.cut B.firstCell.succ) := by
    change 0 ∈ Icc (B.cut 0) (B.cut B.firstCell.succ)
    rw [B.cut_first]
    exact ⟨le_rfl, by simpa using (B.cut_strictMono (show 0 < B.firstCell.succ by change 0 < 1; norm_num)).le⟩
  have hheight : B.upperGraph B.firstCell 0 = B.interface.height 0 := by
    simpa only [show B.firstCell.castSucc = 0 from rfl, B.cut_first] using
      (B.upperGraph_endpoints B.firstCell).1
  have hg := B.band_top_eventually_mem_iff_active_constraints
    (q := collarParameterEquiv.symm (0, B.interface.height 0))
    (by simp) (by simp [B.height_eq_upperGraph hi, hheight])
  have hc : ContinuousAt (fun q : ℝ × ℝ => collarParameterEquiv.symm q)
      (0, B.interface.height 0) := collarParameterEquiv.symm.continuous.continuousAt
  have htop := B.topLineExcess_eventually_nonpos_iff B.firstCell hi
  rw [hheight] at htop
  filter_upwards [hc.eventually hg, htop, B.firstCutFunctional_eventually_nonpos_iff]
    with q hq htop hcut
  simp only [collarParameterEquiv.apply_symm_apply] at hq
  rw [hq, topLineFunctional_apply, htop, hcut]
  have huniq (k : Fin B.interface.count)
      (hk : (0 : ℝ) ∈ Icc (B.cut k.castSucc) (B.cut k.succ)) : k = B.firstCell := by
    have hzero : B.cut k.castSucc = B.cut 0 := by
      rw [B.cut_first]
      exact le_antisymm hk.1 (by simpa using B.cut_strictMono.monotone (Fin.zero_le k.castSucc))
    have he := congrArg Fin.val (B.cut_strictMono.injective hzero)
    exact Fin.ext he
  constructor
  · rintro ⟨k, hk, hl, _, htop⟩
    have he := huniq k hk
    subst k
    exact ⟨by simpa [firstCell] using hl (by simp [firstCell]), htop⟩
  · rintro ⟨hside, htop⟩
    refine ⟨B.firstCell, hi, fun _ => by simpa [firstCell] using hside, ?_, htop⟩
    intro h
    have hp : 0 < B.cut B.firstCell.succ := by
      simpa using B.cut_strictMono (show 0 < B.firstCell.succ by change 0 < 1; norm_num)
    exact False.elim (hp.ne h)


theorem band_last_top_eventually_mem_iff_affine_sector :
    ∀ᶠ q : ℝ × ℝ in 𝓝 (1, B.interface.height (Fin.last B.interface.count)),
      collarParameterEquiv.symm q ∈ B.band ↔
        B.endpointCutFunctional true (collarParameterEquiv.symm
          (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0 ∧
        B.topLineFunctional B.lastCell (collarParameterEquiv.symm
          (B.cuts.coordinates B.open_domain B.smooth_lower q)) ≤ 0 := by
  have hi : (1 : ℝ) ∈ Icc (B.cut B.lastCell.castSucc) (B.cut B.lastCell.succ) := by
    rw [B.lastCell_succ, B.cut_last]
    exact ⟨by simpa using B.cut_strictMono.monotone (Fin.le_last B.lastCell.castSucc), le_rfl⟩
  have hheight : B.upperGraph B.lastCell 1 = B.interface.height (Fin.last B.interface.count) := by
    simpa only [B.lastCell_succ, B.cut_last] using (B.upperGraph_endpoints B.lastCell).2
  have hg := B.band_top_eventually_mem_iff_active_constraints
    (q := collarParameterEquiv.symm (1, B.interface.height (Fin.last B.interface.count)))
    (by simp) (by simp [B.height_eq_upperGraph hi, hheight])
  have hc : ContinuousAt (fun q : ℝ × ℝ => collarParameterEquiv.symm q)
      (1, B.interface.height (Fin.last B.interface.count)) := collarParameterEquiv.symm.continuous.continuousAt
  have htop := B.topLineExcess_eventually_nonpos_iff B.lastCell hi
  rw [hheight] at htop
  filter_upwards [hc.eventually hg, htop, B.lastCutFunctional_eventually_nonpos_iff]
    with q hq htop hcut
  simp only [collarParameterEquiv.apply_symm_apply] at hq
  rw [hq, topLineFunctional_apply, htop, hcut]
  have huniq (k : Fin B.interface.count)
      (hk : (1 : ℝ) ∈ Icc (B.cut k.castSucc) (B.cut k.succ)) : k = B.lastCell := by
    have hlast : B.cut k.succ = B.cut (Fin.last B.interface.count) := by
      rw [B.cut_last]
      exact le_antisymm (by simpa using B.cut_strictMono.monotone (Fin.le_last k.succ)) hk.2
    have he := B.cut_strictMono.injective hlast
    rw [← B.lastCell_succ] at he
    exact Fin.succ_injective _ he
  constructor
  · rintro ⟨k, hk, _, hr, htop⟩
    have he := huniq k hk
    subst k
    exact ⟨by simpa [B.lastCell_succ] using hr (by simp [B.lastCell_succ]), htop⟩
  · rintro ⟨hside, htop⟩
    refine ⟨B.lastCell, hi, ?_, fun _ => by simpa [B.lastCell_succ] using hside, htop⟩
    intro h
    have hp : B.cut B.lastCell.castSucc < 1 := by
      simpa only [B.lastCell_succ, B.cut_last] using B.cut_strictMono
        (Fin.castSucc_lt_succ (i := B.lastCell))
    exact False.elim (hp.ne h)

private theorem planar_carrier_eventually_of_oblique
    (q : ℝ × ℝ) (hq : q ∈ (B.cuts.coordinates B.open_domain B.smooth_lower).source)
    (P : EuclideanSpace ℝ (Fin 2) → Prop)
    (hlocal : ∀ᶠ w in 𝓝 q, collarParameterEquiv.symm w ∈ B.band ↔
      P (collarParameterEquiv.symm (B.cuts.coordinates B.open_domain B.smooth_lower w))) :
    ∀ᶠ z in 𝓝 (collarParameterEquiv.symm (B.cuts.coordinates B.open_domain B.smooth_lower q)),
      z ∈ F.symm '' B.carrier ↔ P z := by
  let G := B.cuts.coordinates B.open_domain B.smooth_lower
  have hzinv : ContinuousAt (fun z : EuclideanSpace ℝ (Fin 2) => G.symm (collarParameterEquiv z))
      (collarParameterEquiv.symm (G q)) := by
    apply (G.continuousAt_symm (G.map_source hq)).comp_of_eq
      collarParameterEquiv.continuous.continuousAt
    exact collarParameterEquiv.apply_symm_apply _
  have hevent := hzinv.eventually (by
    simpa only [collarParameterEquiv.apply_symm_apply, G.left_inv hq] using hlocal)
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



theorem planar_carrier_first_top_eventually_iff :
    ∀ᶠ z in 𝓝 (B.planarTopVertex 0), z ∈ F.symm '' B.carrier ↔
      B.endpointCutFunctional false z ≤ 0 ∧ B.topLineFunctional B.firstCell z ≤ 0 := by
  have hi : (0 : ℝ) ∈ Icc (B.cut B.firstCell.castSucc) (B.cut B.firstCell.succ) := by
    change 0 ∈ Icc (B.cut 0) (B.cut B.firstCell.succ)
    rw [B.cut_first]
    exact ⟨le_rfl, by simpa using (B.cut_strictMono (show 0 < B.firstCell.succ by change 0 < 1; norm_num)).le⟩
  have hh : B.upperGraph B.firstCell 0 = B.interface.height 0 := by
    simpa only [show B.firstCell.castSucc = 0 from rfl, B.cut_first] using
      (B.upperGraph_endpoints B.firstCell).1
  have hq : (0, B.interface.height 0) ∈ (B.cuts.coordinates B.open_domain B.smooth_lower).source := by
    rw [← hh]
    exact (B.interface.pieceCoordinates B.open_domain B.smooth_lower B.firstCell).band_subset_coordinates_source
      B.open_domain B.smooth_lower ⟨hi,
        ((B.interface.pieceCoordinates B.open_domain B.smooth_lower B.firstCell).upperGraph_bounds hi).1.le,
        le_rfl⟩
  have hx : B.cuts.A (B.interface.height 0) = B.interface.cut 0 := by
    change B.cuts.left.horizontal (B.interface.height 0) = _
    rw [B.interface.height_first, B.cuts.left.horizontal_parameter B.interface.left_parameter_mem,
      B.interface.cut_first]
  have hmap : collarParameterEquiv.symm
      (B.cuts.coordinates B.open_domain B.smooth_lower (0, B.interface.height 0)) = B.planarTopVertex 0 := by
    rw [B.cuts.coordinates_apply, obliqueStripMap_left, hx]
    rfl
  rw [← hmap]
  exact B.planar_carrier_eventually_of_oblique _ hq _ B.band_first_top_eventually_mem_iff_affine_sector


theorem planar_carrier_last_top_eventually_iff :
    ∀ᶠ z in 𝓝 (B.planarTopVertex (Fin.last B.interface.count)), z ∈ F.symm '' B.carrier ↔
      B.endpointCutFunctional true z ≤ 0 ∧ B.topLineFunctional B.lastCell z ≤ 0 := by
  have hi : (1 : ℝ) ∈ Icc (B.cut B.lastCell.castSucc) (B.cut B.lastCell.succ) := by
    rw [B.lastCell_succ, B.cut_last]
    exact ⟨by simpa using B.cut_strictMono.monotone (Fin.le_last B.lastCell.castSucc), le_rfl⟩
  have hh : B.upperGraph B.lastCell 1 = B.interface.height (Fin.last B.interface.count) := by
    simpa only [B.lastCell_succ, B.cut_last] using (B.upperGraph_endpoints B.lastCell).2
  have hq : (1, B.interface.height (Fin.last B.interface.count)) ∈
      (B.cuts.coordinates B.open_domain B.smooth_lower).source := by
    rw [← hh]
    exact (B.interface.pieceCoordinates B.open_domain B.smooth_lower B.lastCell).band_subset_coordinates_source
      B.open_domain B.smooth_lower ⟨hi,
        ((B.interface.pieceCoordinates B.open_domain B.smooth_lower B.lastCell).upperGraph_bounds hi).1.le,
        le_rfl⟩
  have hx : B.cuts.B (B.interface.height (Fin.last B.interface.count)) =
      B.interface.cut (Fin.last B.interface.count) := by
    change B.cuts.right.horizontal (B.interface.height (Fin.last B.interface.count)) = _
    rw [B.interface.height_last, B.cuts.right.horizontal_parameter B.interface.right_parameter_mem,
      B.interface.cut_last]
  have hmap : collarParameterEquiv.symm
      (B.cuts.coordinates B.open_domain B.smooth_lower
        (1, B.interface.height (Fin.last B.interface.count))) = B.planarTopVertex (Fin.last B.interface.count) := by
    rw [B.cuts.coordinates_apply, obliqueStripMap_right, hx]
    rfl
  rw [← hmap]
  exact B.planar_carrier_eventually_of_oblique _ hq _ B.band_last_top_eventually_mem_iff_affine_sector

end PoincareConjecture.Topology.Surface.ObliqueBandFaces
