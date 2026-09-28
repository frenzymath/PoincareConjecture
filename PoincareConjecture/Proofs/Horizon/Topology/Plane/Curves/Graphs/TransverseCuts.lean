import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Coordinates
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.ObliqueStrip

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves

private theorem exists_local_interval_inverse
    {g : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (hg : ContDiffOn ℝ ∞ g U)
    (h0 : (0 : ℝ) ∈ U) (hpos : 0 < deriv g 0) :
    ∃ (l u : ℝ) (G : OpenPartialHomeomorph ℝ ℝ),
      l < 0 ∧ 0 < u ∧ G.source = Ioo l u ∧ (∀ t, G t = g t) ∧
      (∀ t ∈ G.source, 0 < deriv g t) ∧ StrictMonoOn G G.source ∧
      ContDiffOn ℝ ∞ G G.source ∧ ContDiffOn ℝ ∞ G.symm G.target := by
  have hdc := hg.continuousOn_deriv_of_isOpen hU (by simp)
  have hopen : IsOpen (U ∩ {t | 0 < deriv g t}) :=
    hdc.isOpen_inter_preimage hU isOpen_Ioi
  obtain ⟨l, u, hzero, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hopen.mem_nhds ⟨h0, hpos⟩)
  have hWU : Ioo l u ⊆ U := fun _ ht => (hsub ht).1
  have hWpos : ∀ t ∈ Ioo l u, 0 < deriv g t := fun _ ht => (hsub ht).2
  have hmono : StrictMonoOn g (Ioo l u) :=
    strictMonoOn_of_deriv_pos (convex_Ioo _ _) (hg.continuousOn.mono hWU)
      (fun t ht => hWpos t (interior_subset ht))
  have hopenmap : IsOpenMap ((Ioo l u).domRestrict g) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro t
    have hgat : ContDiffAt ℝ ∞ g t :=
      (hg t (hWU t.property)).contDiffAt (hU.mem_nhds (hWU t.property))
    have hd := (hgat.hasStrictDerivAt (by simp)).hasStrictFDerivAt_equiv
      (ne_of_gt (hWpos t t.property))
    change 𝓝 (g t) ≤ Filter.map (g ∘ Subtype.val) (𝓝 t)
    rw [← Filter.map_map, isOpen_Ioo.isOpenEmbedding_subtypeVal.map_nhds_eq,
      hd.map_nhds_eq_of_equiv]
  let G := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hmono.injOn.toPartialEquiv g (Ioo l u)) (hg.continuousOn.mono hWU) hopenmap isOpen_Ioo
  refine ⟨l, u, G, hzero.1, hzero.2, rfl, fun _ => rfl, hWpos, hmono,
    hg.mono hWU, ?_⟩
  intro y hy
  have hys : G.symm y ∈ Ioo l u := G.map_target hy
  have hgat : ContDiffAt ℝ ∞ g (G.symm y) :=
    (hg _ (hWU hys)).contDiffAt (hU.mem_nhds (hWU hys))
  have hd := (hgat.hasStrictDerivAt (by simp)).hasStrictFDerivAt_equiv
    (ne_of_gt (hWpos _ hys))
  exact (G.contDiffAt_symm hy hd.hasFDerivAt hgat).contDiffWithinAt

def transverseCutHeight (lo : ℝ → ℝ) (a u w r : ℝ) : ℝ :=
  lo a + r * w - lo (a + r * u)

@[simp] theorem transverseCutHeight_zero (lo : ℝ → ℝ) (a u w : ℝ) :
    transverseCutHeight lo a u w 0 = 0 := by simp [transverseCutHeight]

structure TransverseCutCoordinates (lo : ℝ → ℝ) (a u w : ℝ) where
  parameter : OpenPartialHomeomorph ℝ ℝ
  source_interval : ∃ l < (0 : ℝ), ∃ r > (0 : ℝ), parameter.source = Ioo l r
  map_eq : ∀ r, parameter r = transverseCutHeight lo a u w r
  positive_deriv : ∀ r ∈ parameter.source, 0 < deriv parameter r
  strictMono : StrictMonoOn parameter parameter.source
  smooth : ContDiffOn ℝ ∞ parameter parameter.source
  smooth_symm : ContDiffOn ℝ ∞ parameter.symm parameter.target

theorem exists_transverseCutCoordinates {lo : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hlo : ContDiffOn ℝ ∞ lo U) {a u w : ℝ} (ha : a ∈ U)
    (htrans : 0 < w - deriv lo a * u) : Nonempty (TransverseCutCoordinates lo a u w) := by
  let V : Set ℝ := (fun r => a + r * u) ⁻¹' U
  have hV : IsOpen V := hU.preimage (by fun_prop)
  have hV0 : (0 : ℝ) ∈ V := by simpa [V] using ha
  have hheight : ContDiffOn ℝ ∞ (transverseCutHeight lo a u w) V := by
    exact (contDiffOn_const.add (contDiffOn_id.mul contDiffOn_const)).sub
      (hlo.comp (contDiffOn_const.add (contDiffOn_id.mul contDiffOn_const)) (fun _ hr => hr))
  have hdlo : HasDerivAt lo (deriv lo a) a :=
    ((hlo a ha).contDiffAt (hU.mem_nhds ha)).differentiableAt (by simp) |>.hasDerivAt
  have hdarg : HasDerivAt (fun r : ℝ => a + r * u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).const_add a
  have hdcomp : HasDerivAt (fun r : ℝ => lo (a + r * u)) (deriv lo a * u) 0 := by
    have hdlo' : HasDerivAt lo (deriv lo a) (a + 0 * u) := by simpa using hdlo
    exact hdlo'.comp (0 : ℝ) hdarg
  have hd : HasDerivAt (transverseCutHeight lo a u w) (w - deriv lo a * u) 0 := by
    change HasDerivAt (fun r : ℝ => lo a + r * w - lo (a + r * u)) _ _
    convert! (((hasDerivAt_id (0 : ℝ)).mul_const w).const_add (lo a)).sub hdcomp using 1
    simp
  obtain ⟨l, r, G, hl, hr, hsource, hmap, hpositive, hmono, hsmooth, hinv⟩ :=
    exists_local_interval_inverse hV hheight hV0 (hd.deriv.symm ▸ htrans)
  refine ⟨⟨G, ⟨l, hl, r, hr, hsource⟩, hmap, ?_, hmono, hsmooth, hinv⟩⟩
  have heq : (G : ℝ → ℝ) = transverseCutHeight lo a u w := funext hmap
  simpa only [heq] using hpositive

namespace TransverseCutCoordinates

variable {lo : ℝ → ℝ} {a u w : ℝ} (C : TransverseCutCoordinates lo a u w)

theorem zero_mem_source : (0 : ℝ) ∈ C.parameter.source := by
  obtain ⟨l, hl, r, hr, heq⟩ := C.source_interval
  rw [heq]
  exact ⟨hl, hr⟩

@[simp] theorem parameter_zero : C.parameter 0 = 0 := by rw [C.map_eq]; simp

theorem zero_mem_target : (0 : ℝ) ∈ C.parameter.target := by
  simpa only [C.parameter_zero] using C.parameter.map_source C.zero_mem_source

@[simp] theorem inverse_zero : C.parameter.symm 0 = 0 := by
  simpa only [C.parameter_zero] using C.parameter.left_inv C.zero_mem_source

noncomputable def horizontal (z : ℝ) : ℝ := a + C.parameter.symm z * u

@[simp] theorem horizontal_zero : C.horizontal 0 = a := by simp [horizontal]

theorem smooth_horizontal : ContDiffOn ℝ ∞ C.horizontal C.parameter.target :=
  contDiffOn_const.add (C.smooth_symm.mul contDiffOn_const)

theorem line_identity {z : ℝ} (hz : z ∈ C.parameter.target) :
    (C.horizontal z, lo (C.horizontal z) + z) =
      (a + C.parameter.symm z * u, lo a + C.parameter.symm z * w) := by
  have h := C.parameter.right_inv hz
  rw [C.map_eq] at h
  refine Prod.ext (by rfl) ?_
  dsimp [horizontal, transverseCutHeight] at *
  linarith

theorem inverse_positive_deriv {z : ℝ} (hz : z ∈ C.parameter.target) :
    0 < deriv C.parameter.symm z := by
  have hs := C.parameter.map_target hz
  have hp := C.positive_deriv _ hs
  have hd : HasDerivAt C.parameter (deriv C.parameter (C.parameter.symm z))
      (C.parameter.symm z) :=
    ((C.smooth _ hs).contDiffAt (C.parameter.open_source.mem_nhds hs)).differentiableAt
      (by simp) |>.hasDerivAt
  rw [(C.parameter.hasDerivAt_symm hz hp.ne' hd).deriv]
  exact inv_pos.mpr hp

theorem inverse_strictMono : StrictMonoOn C.parameter.symm C.parameter.target := by
  intro x hx y hy hxy
  apply lt_of_not_ge
  intro hle
  have h := C.strictMono.monotoneOn (C.parameter.map_target hy)
    (C.parameter.map_target hx) hle
  rw [C.parameter.right_inv hy, C.parameter.right_inv hx] at h
  exact (not_le_of_gt hxy) h

theorem horizontal_parameter {r : ℝ} (hr : r ∈ C.parameter.source) :
    C.horizontal (C.parameter r) = a + r * u := by
  simp only [horizontal, C.parameter.left_inv hr]

theorem exists_small_positive_parameters {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ r ∈ Ioo (0 : ℝ) ε,
      r ∈ C.parameter.source ∧ C.parameter r ∈ Ioo (0 : ℝ) δ := by
  have hheight : ∀ᶠ r in 𝓝 (0 : ℝ), C.parameter r ∈ Ioo (-δ) δ := by
    apply (C.parameter.continuousAt C.zero_mem_source).preimage_mem_nhds
    rw [C.parameter_zero]
    exact isOpen_Ioo.mem_nhds ⟨by linarith, hδ⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (C.parameter.open_source.mem_nhds C.zero_mem_source) hheight)
  refine ⟨ε, hε, fun r hr => ?_⟩
  have h := hball (show r ∈ Metric.ball (0 : ℝ) ε by
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr.1] using hr.2)
  refine ⟨h.1, ?_, h.2.2⟩
  simpa only [C.parameter_zero] using C.strictMono C.zero_mem_source h.1 hr.1

end TransverseCutCoordinates

structure TransverseGraphCuts (lo : ℝ → ℝ) (a b ua wa ub wb : ℝ) where
  left : TransverseCutCoordinates lo a ua wa
  right : TransverseCutCoordinates lo b ub wb
  radius : ℝ
  radius_pos : 0 < radius
  height_subset : Ioo (-radius) radius ⊆ left.parameter.target ∩ right.parameter.target
  separated : ∀ z ∈ Ioo (-radius) radius, left.horizontal z < right.horizontal z

theorem exists_transverseGraphCuts {lo : ℝ → ℝ} {Ua Ub : Set ℝ}
    (hUa : IsOpen Ua) (hloA : ContDiffOn ℝ ∞ lo Ua)
    (hUb : IsOpen Ub) (hloB : ContDiffOn ℝ ∞ lo Ub)
    {a b ua wa ub wb : ℝ} (hab : a < b) (ha : a ∈ Ua) (hb : b ∈ Ub)
    (htransA : 0 < wa - deriv lo a * ua) (htransB : 0 < wb - deriv lo b * ub) :
    Nonempty (TransverseGraphCuts lo a b ua wa ub wb) := by
  obtain ⟨L⟩ := exists_transverseCutCoordinates hUa hloA ha htransA
  obtain ⟨R⟩ := exists_transverseCutCoordinates hUb hloB hb htransB
  have hLc : ContinuousAt L.horizontal 0 :=
    L.smooth_horizontal.continuousOn.continuousAt
      (L.parameter.open_target.mem_nhds L.zero_mem_target)
  have hRc : ContinuousAt R.horizontal 0 :=
    R.smooth_horizontal.continuousOn.continuousAt
      (R.parameter.open_target.mem_nhds R.zero_mem_target)
  have hsep : ∀ᶠ z in 𝓝 (0 : ℝ), L.horizontal z < R.horizontal z :=
    hLc.eventually_lt hRc (by simpa only [L.horizontal_zero, R.horizontal_zero] using hab)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem (L.parameter.open_target.mem_nhds L.zero_mem_target)
      (R.parameter.open_target.mem_nhds R.zero_mem_target)) hsep)
  have hgood {z : ℝ} (hz : z ∈ Ioo (-δ) δ) :
      (z ∈ L.parameter.target ∧ z ∈ R.parameter.target) ∧ L.horizontal z < R.horizontal z := by
    apply hball
    simpa only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_lt, mem_Ioo] using hz
  exact ⟨⟨L, R, δ, hδ, fun _ hz => (hgood hz).1, fun _ hz => (hgood hz).2⟩⟩

namespace TransverseGraphCuts

variable {lo : ℝ → ℝ} {a b ua wa ub wb : ℝ}
  (P : TransverseGraphCuts lo a b ua wa ub wb)

noncomputable abbrev A : ℝ → ℝ := P.left.horizontal

noncomputable abbrev B : ℝ → ℝ := P.right.horizontal

@[simp] theorem A_zero : P.A 0 = a := P.left.horizontal_zero

@[simp] theorem B_zero : P.B 0 = b := P.right.horizontal_zero

theorem smooth_A : ContDiffOn ℝ ∞ P.A (Ioo (-P.radius) P.radius) :=
  P.left.smooth_horizontal.mono (fun _ hz => (P.height_subset hz).1)

theorem smooth_B : ContDiffOn ℝ ∞ P.B (Ioo (-P.radius) P.radius) :=
  P.right.smooth_horizontal.mono (fun _ hz => (P.height_subset hz).2)

theorem left_line_identity {z : ℝ} (hz : z ∈ Ioo (-P.radius) P.radius) :
    (P.A z, lo (P.A z) + z) =
      (a + P.left.parameter.symm z * ua, lo a + P.left.parameter.symm z * wa) :=
  P.left.line_identity (P.height_subset hz).1

theorem right_line_identity {z : ℝ} (hz : z ∈ Ioo (-P.radius) P.radius) :
    (P.B z, lo (P.B z) + z) =
      (b + P.right.parameter.symm z * ub, lo b + P.right.parameter.symm z * wb) :=
  P.right.line_identity (P.height_subset hz).2

theorem exists_small_positive_cut_lengths :
    ∃ ε > 0, ∀ ra ∈ Ioo (0 : ℝ) ε, ∀ rb ∈ Ioo (0 : ℝ) ε,
      ra ∈ P.left.parameter.source ∧ rb ∈ P.right.parameter.source ∧
      P.left.parameter ra ∈ Ioo (0 : ℝ) P.radius ∧
      P.right.parameter rb ∈ Ioo (0 : ℝ) P.radius ∧
      P.A (P.left.parameter ra) = a + ra * ua ∧
      P.B (P.right.parameter rb) = b + rb * ub ∧
      P.left.parameter.symm (P.left.parameter ra) = ra ∧
      P.right.parameter.symm (P.right.parameter rb) = rb := by
  obtain ⟨εa, hεa, hleft⟩ := P.left.exists_small_positive_parameters P.radius_pos
  obtain ⟨εb, hεb, hright⟩ := P.right.exists_small_positive_parameters P.radius_pos
  refine ⟨min εa εb, lt_min hεa hεb, fun ra hra rb hrb => ?_⟩
  have ha := hleft ra ⟨hra.1, hra.2.trans_le (min_le_left _ _)⟩
  have hb := hright rb ⟨hrb.1, hrb.2.trans_le (min_le_right _ _)⟩
  exact ⟨ha.1, hb.1, ha.2, hb.2, P.left.horizontal_parameter ha.1,
    P.right.horizontal_parameter hb.1, P.left.parameter.left_inv ha.1,
    P.right.parameter.left_inv hb.1⟩

noncomputable def coordinates {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) :
    OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
  obliqueStripCoordinates isOpen_Ioo P.smooth_A P.smooth_B P.separated hX hlo

theorem coordinates_apply {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (q : ℝ × ℝ) : P.coordinates hX hlo q = obliqueStripMap P.A P.B lo q :=
  obliqueStripCoordinates_apply isOpen_Ioo P.smooth_A P.smooth_B P.separated hX hlo q

theorem smooth_coordinates {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) :
    ContDiffOn ℝ ∞ (P.coordinates hX hlo) (P.coordinates hX hlo).source :=
  contDiffOn_obliqueStripCoordinates isOpen_Ioo P.smooth_A P.smooth_B P.separated hX hlo

theorem smooth_coordinates_symm {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) :
    ContDiffOn ℝ ∞ (P.coordinates hX hlo).symm (P.coordinates hX hlo).target :=
  contDiffOn_obliqueStripCoordinates_symm isOpen_Ioo P.smooth_A P.smooth_B P.separated hX hlo

end TransverseGraphCuts

end Poincare.Topology.Plane.Curves
