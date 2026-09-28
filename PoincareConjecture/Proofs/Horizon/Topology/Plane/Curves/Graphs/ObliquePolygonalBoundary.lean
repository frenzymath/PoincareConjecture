


import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.TransverseCuts
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.AffineApproximation
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.Deriv.Inv









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped ContDiff Topology

namespace Poincare.Topology.Plane.Curves


noncomputable def obliqueProjection (A B : ℝ → ℝ) (x z : ℝ) : ℝ :=
  (x - A z) / (B z - A z)


noncomputable def obliqueProjectionDerivative (A B : ℝ → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  ((1 - deriv A q.2.1 * q.2.2) * (B q.2.1 - A q.2.1) -
    (q.1 - A q.2.1) * ((deriv B q.2.1 - deriv A q.2.1) * q.2.2)) /
      (B q.2.1 - A q.2.1) ^ 2

private theorem continuousOn_obliqueProjectionDerivative
    {A B : ℝ → ℝ} {Z : Set ℝ} (hZ : IsOpen Z)
    (hA : ContDiffOn ℝ ∞ A Z) (hB : ContDiffOn ℝ ∞ B Z)
    (hgap : ∀ z ∈ Z, A z < B z) :
    ContinuousOn (obliqueProjectionDerivative A B) {q | q.2.1 ∈ Z} := by
  have hz : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => q.2.1) {q | q.2.1 ∈ Z} := by fun_prop
  have hd : ContinuousOn (fun q : ℝ × (ℝ × ℝ) => q.2.2) {q | q.2.1 ∈ Z} := by fun_prop
  have hAc := hA.continuousOn.comp hz (fun _ hq => hq)
  have hBc := hB.continuousOn.comp hz (fun _ hq => hq)
  have hAd := (hA.continuousOn_deriv_of_isOpen hZ (by simp)).comp hz (fun _ hq => hq)
  have hBd := (hB.continuousOn_deriv_of_isOpen hZ (by simp)).comp hz (fun _ hq => hq)
  exact (((continuousOn_const.sub (hAd.mul hd)).mul (hBc.sub hAc)).sub
    ((continuousOn_fst.sub hAc).mul ((hBd.sub hAd).mul hd))).div
      ((hBc.sub hAc).pow 2) (fun q hq => pow_ne_zero _ (sub_pos.mpr (hgap _ hq)).ne')



theorem TransverseGraphCuts.exists_projection_derivative_tolerance
    {lo : ℝ → ℝ} {a b ua wa ub wb : ℝ}
    (P : TransverseGraphCuts lo a b ua wa ub wb) (hab : a < b) (l r : ℝ) :
    ∃ η > 0, ∀ x ∈ Icc l r, ∀ z d : ℝ, |z| < η → |d| < η →
      z ∈ Ioo (-P.radius) P.radius ∧
        0 < obliqueProjectionDerivative P.A P.B (x, (z, d)) := by
  let Z := Ioo (-P.radius) P.radius
  let W : Set (ℝ × (ℝ × ℝ)) :=
    {q | q.2.1 ∈ Z} ∩ {q | 0 < obliqueProjectionDerivative P.A P.B q}
  have hW : IsOpen W :=
    (continuousOn_obliqueProjectionDerivative isOpen_Ioo P.smooth_A P.smooth_B P.separated).isOpen_inter_preimage
      (isOpen_Ioo.preimage (by fun_prop)) isOpen_Ioi
  have haxis : Icc l r ×ˢ {(0 : ℝ × ℝ)} ⊆ W := by
    rintro ⟨x, z, d⟩ ⟨_, hzd⟩
    have hzero : (z, d) = (0 : ℝ × ℝ) := hzd
    have hz : z = 0 := congrArg Prod.fst hzero
    have hd : d = 0 := congrArg Prod.snd hzero
    subst z
    subst d
    refine ⟨⟨by linarith [P.radius_pos], P.radius_pos⟩, ?_⟩
    change 0 < obliqueProjectionDerivative P.A P.B (x, (0, 0))
    simp only [obliqueProjectionDerivative, mul_zero, sub_zero, one_mul,
      P.A_zero, P.B_zero]
    exact div_pos (sub_pos.mpr hab) (sq_pos_of_pos (sub_pos.mpr hab))
  obtain ⟨U, V, _, hV, hIU, h0V, hUV⟩ :=
    generalized_tube_lemma isCompact_Icc isCompact_singleton hW haxis
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp
    (hV.mem_nhds (h0V (mem_singleton (0 : ℝ × ℝ))))
  refine ⟨η, hη, ?_⟩
  intro x hx z d hz hd
  apply hUV (a := (x, (z, d)))
  refine ⟨hIU hx, hball ?_⟩
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  exact max_lt hz hd


theorem hasDerivAt_obliqueProjection
    {A B z : ℝ → ℝ} {x dz : ℝ}
    (hA : DifferentiableAt ℝ A (z x)) (hB : DifferentiableAt ℝ B (z x))
    (hz : HasDerivAt z dz x) (hgap : A (z x) < B (z x)) :
    HasDerivAt (fun t => obliqueProjection A B t (z t))
      (obliqueProjectionDerivative A B (x, (z x, dz))) x := by
  have hAc := hA.hasDerivAt.comp x hz
  have hBc := hB.hasDerivAt.comp x hz
  convert! ((hasDerivAt_id x).sub hAc).div (hBc.sub hAc)
    (sub_pos.mpr hgap).ne' using 1
  dsimp [obliqueProjectionDerivative]
  ring


noncomputable def affineHeightBridge (c d ηa ηb x : ℝ) : ℝ :=
  ηa + ((ηb - ηa) / (d - c)) * (x - c)

private theorem affineHeightBridge_bounds {c d ηa ηb x : ℝ} (hcd : c < d)
    (hx : x ∈ Icc c d) :
    min ηa ηb ≤ affineHeightBridge c d ηa ηb x ∧
      affineHeightBridge c d ηa ηb x ≤ max ηa ηb := by
  have he : affineHeightBridge c d ηa ηb x =
      AffineMap.lineMap ηa ηb ((x - c) / (d - c)) := by
    simp only [affineHeightBridge, AffineMap.lineMap_apply, vsub_eq_sub,
      smul_eq_mul, vadd_eq_add]
    ring
  rw [he]
  apply (convex_Icc (min ηa ηb) (max ηa ηb)).lineMap_mem
    ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
  exact ⟨div_nonneg (sub_nonneg.mpr hx.1) (sub_pos.mpr hcd).le,
    (div_le_one (sub_pos.mpr hcd)).mpr (sub_le_sub_right hx.2 _)⟩



theorem exists_piecewiseAffine_height_bridge
    {lo : ℝ → ℝ} {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    {c d ηa ηb ν ρ : ℝ} (hcd : c < d) (hI : Icc c d ⊆ X)
    (hν : 0 < ν) (hρ : 0 < ρ) (ha : ηa ∈ Ioo (0 : ℝ) ν) (hb : ηb ∈ Ioo (0 : ℝ) ν)
    (hslope : |(ηb - ηa) / (d - c)| < ρ / 2) :
    ∃ (n : ℕ) (cut : Fin (n + 1) → ℝ) (piece : Fin n → ℝ →ᵃ[ℝ] ℝ),
      0 < n ∧ StrictMono cut ∧ cut 0 = c ∧ cut (Fin.last n) = d ∧
      (∀ i, piece i (cut i.castSucc) = lo (cut i.castSucc) +
          affineHeightBridge c d ηa ηb (cut i.castSucc) ∧
        piece i (cut i.succ) = lo (cut i.succ) + affineHeightBridge c d ηa ηb (cut i.succ)) ∧
      (∀ i x, x ∈ Icc (cut i.castSucc) (cut i.succ) →
        0 < piece i x - lo x ∧ piece i x - lo x < 2 * ν ∧
          |(piece i).linear 1 - deriv lo x| < ρ) := by
  let g (x : ℝ) := lo x + affineHeightBridge c d ηa ηb x
  have hbridge : ContDiff ℝ ∞ (affineHeightBridge c d ηa ηb) := by
    change ContDiff ℝ ∞ (fun x : ℝ => ηa + ((ηb - ηa) / (d - c)) * (x - c))
    fun_prop
  have hg : ContDiffOn ℝ ∞ g X := hlo.add hbridge.contDiffOn
  let ε := min (min ηa ηb / 2) (min (ν / 2) (ρ / 2))
  have hε : 0 < ε := lt_min (div_pos (lt_min ha.1 hb.1) (by norm_num))
    (lt_min (by positivity) (by positivity))
  have hεη : ε ≤ min ηa ηb / 2 := min_le_left _ _
  have hεν : ε ≤ ν / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hερ : ε ≤ ρ / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨n, cut, piece, hn, hcut, hfirst, hlast, hends, _, hclose⟩ :=
    exists_piecewiseAffine_approximation hX (hg.of_le (by simp)) hcd hI hε
  refine ⟨n, cut, piece, hn, hcut, hfirst, hlast, hends, ?_⟩
  intro i x hx
  have hxI : x ∈ Icc c d := by
    constructor
    · rw [← hfirst]
      exact (hcut.monotone (Fin.zero_le i.castSucc)).trans hx.1
    · rw [← hlast]
      exact hx.2.trans (hcut.monotone (Fin.le_last i.succ))
  have he := affineHeightBridge_bounds (ηa := ηa) (ηb := ηb) hcd hxI
  have herr := (hclose i x hx).1
  rw [abs_lt] at herr
  have hmin : 0 < min ηa ηb := lt_min ha.1 hb.1
  have hmax : max ηa ηb < ν := max_lt ha.2 hb.2
  have hderiv : deriv g x = deriv lo x + (ηb - ηa) / (d - c) := by
    have hdlo : HasDerivAt lo (deriv lo x) x :=
      ((hlo x (hI hxI)).contDiffAt (hX.mem_nhds (hI hxI))).differentiableAt
        (by simp) |>.hasDerivAt
    have hdbridge : HasDerivAt (affineHeightBridge c d ηa ηb)
        ((ηb - ηa) / (d - c)) x := by
      convert! (((hasDerivAt_id x).sub_const c).const_mul
        ((ηb - ηa) / (d - c))).const_add ηa using 1
      simp
    exact (hdlo.add hdbridge).deriv
  refine ⟨?_, ?_, ?_⟩
  · dsimp [g] at herr
    linarith [he.1, herr.1]
  · dsimp [g] at herr
    linarith [he.2, herr.2]
  · have heq : (piece i).linear 1 - deriv lo x =
        ((piece i).linear 1 - deriv g x) + (ηb - ηa) / (d - c) := by rw [hderiv]; ring
    rw [heq]
    exact (abs_add_le _ _).trans_lt (by linarith [(hclose i x hx).2])

private theorem exists_larger_closed_interval {X : Set ℝ} (hX : IsOpen X)
    {a b : ℝ} (hab : a ≤ b) (hI : Icc a b ⊆ X) :
    ∃ l r : ℝ, l < a ∧ b < r ∧ Icc l r ⊆ X := by
  obtain ⟨l, l', hl, hleft⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hX.mem_nhds (hI (left_mem_Icc.mpr hab)))
  obtain ⟨r', r, hr, hright⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (hX.mem_nhds (hI (right_mem_Icc.mpr hab)))
  refine ⟨(l + a) / 2, (b + r) / 2, by linarith [hl.1], by linarith [hr.2], ?_⟩
  intro x hx
  by_cases hxa : x < a
  · exact hleft ⟨by linarith [hx.1, hl.1], hxa.trans hl.2⟩
  by_cases hbx : b < x
  · exact hright ⟨hr.1.trans hbx, by linarith [hx.2, hr.2]⟩
  exact hI ⟨le_of_not_gt hxa, le_of_not_gt hbx⟩



structure ObliquePolygonalBoundary {lo : ℝ → ℝ} {a b ua wa ub wb : ℝ}
    (P : TransverseGraphCuts lo a b ua wa ub wb) (X : Set ℝ) (ra rb : ℝ) where
  count : ℕ
  count_pos : 0 < count
  cut : Fin (count + 1) → ℝ
  height : Fin (count + 1) → ℝ
  piece : Fin count → ℝ →ᵃ[ℝ] ℝ
  cut_strictMono : StrictMono cut
  cut_first : cut 0 = a + ra * ua
  cut_last : cut (Fin.last count) = b + rb * ub
  height_first : height 0 = P.left.parameter ra
  height_last : height (Fin.last count) = P.right.parameter rb
  left_parameter_mem : ra ∈ P.left.parameter.source
  right_parameter_mem : rb ∈ P.right.parameter.source
  piece_endpoints : ∀ i,
    piece i (cut i.castSucc) = lo (cut i.castSucc) + height i.castSucc ∧
    piece i (cut i.succ) = lo (cut i.succ) + height i.succ
  cell_domain : ∀ i : Fin count, Icc (cut i.castSucc) (cut i.succ) ⊆ X
  height_cap : ℝ
  height_cap_pos : 0 < height_cap
  height_cap_lt_radius : height_cap < P.radius
  height_cap_domain : ∀ z ∈ Icc (0 : ℝ) height_cap, Icc (P.A z) (P.B z) ⊆ X
  height_lt_cap : ∀ i x, x ∈ Icc (cut i.castSucc) (cut i.succ) →
    piece i x - lo x < height_cap
  height_bounds : ∀ i x, x ∈ Icc (cut i.castSucc) (cut i.succ) →
    0 < piece i x - lo x ∧ piece i x - lo x < P.radius
  projection_deriv_pos : ∀ i x, x ∈ Icc (cut i.castSucc) (cut i.succ) →
    0 < obliqueProjectionDerivative P.A P.B
      (x, (piece i x - lo x, (piece i).linear 1 - deriv lo x))



theorem exists_obliquePolygonalBoundary
    {lo : ℝ → ℝ} {a b ua wa ub wb : ℝ}
    (P : TransverseGraphCuts lo a b ua wa ub wb) (hab : a < b)
    {X : Set ℝ} (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) (hI : Icc a b ⊆ X) :
    ∃ ε > 0, ∀ ra ∈ Ioo (0 : ℝ) ε, ∀ rb ∈ Ioo (0 : ℝ) ε,
      Nonempty (ObliquePolygonalBoundary P X ra rb) := by
  obtain ⟨l, r, hla, hbr, hJ⟩ := exists_larger_closed_interval hX hab.le hI
  obtain ⟨ρ, hρ, htol⟩ := P.exists_projection_derivative_tolerance hab l r
  have hAc : ContinuousAt P.A 0 := P.left.smooth_horizontal.continuousOn.continuousAt
    (P.left.parameter.open_target.mem_nhds P.left.zero_mem_target)
  have hBc : ContinuousAt P.B 0 := P.right.smooth_horizontal.continuousOn.continuousAt
    (P.right.parameter.open_target.mem_nhds P.right.zero_mem_target)
  have hAn : ∀ᶠ z in 𝓝 (0 : ℝ), P.A z ∈ Ioo l (a + (b - a) / 4) := by
    apply hAc.preimage_mem_nhds
    rw [P.A_zero]
    exact isOpen_Ioo.mem_nhds ⟨hla, by linarith⟩
  have hBn : ∀ᶠ z in 𝓝 (0 : ℝ), P.B z ∈ Ioo (b - (b - a) / 4) r := by
    apply hBc.preimage_mem_nhds
    rw [P.B_zero]
    exact isOpen_Ioo.mem_nhds ⟨by linarith, hbr⟩
  obtain ⟨σ, hσ, hposition⟩ := Metric.mem_nhds_iff.mp (hAn.and hBn)
  let ν := min (σ / 4) (min (ρ / 4) (ρ * (b - a) / 16))
  have hν : 0 < ν := by dsimp [ν]; positivity
  have hνσ : ν ≤ σ / 4 := min_le_left _ _
  have hνρ : ν ≤ ρ / 4 := (min_le_right _ _).trans (min_le_left _ _)
  have hνwidth : ν ≤ ρ * (b - a) / 16 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨εa, hεa, hleft⟩ := P.left.exists_small_positive_parameters hν
  obtain ⟨εb, hεb, hright⟩ := P.right.exists_small_positive_parameters hν
  refine ⟨min εa εb, lt_min hεa hεb, ?_⟩
  intro ra hra rb hrb
  have ha := hleft ra ⟨hra.1, hra.2.trans_le (min_le_left _ _)⟩
  have hb := hright rb ⟨hrb.1, hrb.2.trans_le (min_le_right _ _)⟩
  let ηa := P.left.parameter ra
  let ηb := P.right.parameter rb
  have hηa : 0 < ηa ∧ ηa < ν := ha.2
  have hηb : 0 < ηb ∧ ηb < ν := hb.2
  let c := a + ra * ua
  let d := b + rb * ub
  have hca : P.A ηa = c := P.left.horizontal_parameter ha.1
  have hdb : P.B ηb = d := P.right.horizontal_parameter hb.1
  have hsmall {z : ℝ} (hz : z ∈ Ioo (0 : ℝ) ν) : z ∈ Metric.ball (0 : ℝ) σ := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hz.1]
    linarith [hz.2]
  have hcbounds : c ∈ Ioo l (a + (b - a) / 4) := by
    rw [← hca]
    exact (hposition (hsmall ha.2)).1
  have hdbounds : d ∈ Ioo (b - (b - a) / 4) r := by
    rw [← hdb]
    exact (hposition (hsmall hb.2)).2
  have hwidth : (b - a) / 2 < d - c := by linarith [hcbounds.2, hdbounds.1]
  have hcd : c < d := by linarith
  have hcdJ : Icc c d ⊆ Icc l r := fun _ hx =>
    ⟨hcbounds.1.le.trans hx.1, hx.2.trans hdbounds.2.le⟩
  have hslope : |(ηb - ηa) / (d - c)| < ρ / 2 := by
    rw [abs_div, abs_of_pos (sub_pos.mpr hcd), div_lt_iff₀ (sub_pos.mpr hcd)]
    have habs : |ηb - ηa| < ν := by rw [abs_lt]; exact ⟨by linarith [hηa.2, hηb.1],
      by linarith [hηb.2, hηa.1]⟩
    nlinarith
  obtain ⟨n, cut, piece, hn, hcut, hfirst, hlast, hends, hbound⟩ :=
    exists_piecewiseAffine_height_bridge hX hlo hcd (hcdJ.trans hJ) hν hρ ha.2 hb.2 hslope
  have hcell (i : Fin n) : Icc (cut i.castSucc) (cut i.succ) ⊆ Icc c d := by
    intro x hx
    constructor
    · rw [← hfirst]
      exact (hcut.monotone (Fin.zero_le i.castSucc)).trans hx.1
    · rw [← hlast]
      exact hx.2.trans (hcut.monotone (Fin.le_last i.succ))
  have hgood (i : Fin n) (x : ℝ) (hx : x ∈ Icc (cut i.castSucc) (cut i.succ)) :=
    htol x (hcdJ (hcell i hx)) (piece i x - lo x) ((piece i).linear 1 - deriv lo x)
      (by rw [abs_of_pos (hbound i x hx).1]; linarith [(hbound i x hx).2.1])
      (hbound i x hx).2.2
  have hcap : 2 * ν < P.radius := by
    have h := htol l (left_mem_Icc.mpr (by linarith : l ≤ r)) (2 * ν) 0
      (by rw [abs_of_pos (by positivity : 0 < 2 * ν)]; linarith) (by simpa using hρ)
    exact h.1.2
  have hcapdomain (z : ℝ) (hz : z ∈ Icc (0 : ℝ) (2 * ν)) : Icc (P.A z) (P.B z) ⊆ X := by
    have hzb : z ∈ Metric.ball (0 : ℝ) σ := by
      rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hz.1]
      linarith [hz.2]
    have hpos := hposition hzb
    exact fun x hx => hJ ⟨hpos.1.1.le.trans hx.1, hx.2.trans hpos.2.2.le⟩
  refine ⟨{
    count := n
    count_pos := hn
    cut := cut
    height := fun i => affineHeightBridge c d ηa ηb (cut i)
    piece := piece
    cut_strictMono := hcut
    cut_first := hfirst
    cut_last := hlast
    height_first := ?_
    height_last := ?_
    left_parameter_mem := ha.1
    right_parameter_mem := hb.1
    piece_endpoints := hends
    cell_domain := fun i => ((hcell i).trans hcdJ).trans hJ
    height_cap := 2 * ν
    height_cap_pos := by positivity
    height_cap_lt_radius := hcap
    height_cap_domain := hcapdomain
    height_lt_cap := fun i x hx => (hbound i x hx).2.1
    height_bounds := fun i x hx => ⟨(hbound i x hx).1, (hgood i x hx).1.2⟩
    projection_deriv_pos := fun i x hx => (hgood i x hx).2 }⟩
  · simp [hfirst, affineHeightBridge, ηa]
  · rw [hlast]
    change ηa + ((ηb - ηa) / (d - c)) * (d - c) = ηb
    rw [div_mul_cancel₀ _ (sub_pos.mpr hcd).ne']
    ring

namespace ObliquePolygonalBoundary

variable {lo : ℝ → ℝ} {a b ua wa ub wb : ℝ}
  {P : TransverseGraphCuts lo a b ua wa ub wb} {X : Set ℝ} {ra rb : ℝ}
  (Q : ObliquePolygonalBoundary P X ra rb)


noncomputable def parameterCut (j : Fin (Q.count + 1)) : ℝ :=
  obliqueProjection P.A P.B (Q.cut j) (Q.height j)


noncomputable def projection (i : Fin Q.count) (x : ℝ) : ℝ :=
  obliqueProjection P.A P.B x (Q.piece i x - lo x)

theorem projection_endpoints (i : Fin Q.count) :
    Q.projection i (Q.cut i.castSucc) = Q.parameterCut i.castSucc ∧
      Q.projection i (Q.cut i.succ) = Q.parameterCut i.succ := by
  simp [projection, parameterCut, (Q.piece_endpoints i).1, (Q.piece_endpoints i).2]

theorem vertex_height_bounds (j : Fin (Q.count + 1)) :
    0 < Q.height j ∧ Q.height j < P.radius := by
  refine Fin.cases ?_ (fun i => ?_) j
  · let i : Fin Q.count := ⟨0, Q.count_pos⟩
    have h := Q.height_bounds i (Q.cut i.castSucc)
      (left_mem_Icc.mpr (Q.cut_strictMono (Fin.castSucc_lt_succ (i := i))).le)
    rw [(Q.piece_endpoints i).1, add_sub_cancel_left] at h
    exact h
  · have h := Q.height_bounds i (Q.cut i.succ)
      (right_mem_Icc.mpr (Q.cut_strictMono (Fin.castSucc_lt_succ (i := i))).le)
    rwa [(Q.piece_endpoints i).2, add_sub_cancel_left] at h

theorem first_vertex : (Q.cut 0, lo (Q.cut 0) + Q.height 0) =
    (a + ra * ua, lo a + ra * wa) := by
  rw [Q.cut_first, Q.height_first, P.left.map_eq]
  simp [transverseCutHeight]

theorem last_vertex :
    (Q.cut (Fin.last Q.count), lo (Q.cut (Fin.last Q.count)) + Q.height (Fin.last Q.count)) =
      (b + rb * ub, lo b + rb * wb) := by
  rw [Q.cut_last, Q.height_last, P.right.map_eq]
  simp [transverseCutHeight]

theorem parameterCut_first : Q.parameterCut 0 = 0 := by
  have h := P.left.horizontal_parameter Q.left_parameter_mem
  change P.A (P.left.parameter ra) = a + ra * ua at h
  simp only [parameterCut, Q.cut_first, Q.height_first, obliqueProjection, h,
    sub_self, zero_div]

theorem parameterCut_last : Q.parameterCut (Fin.last Q.count) = 1 := by
  have h := P.right.horizontal_parameter Q.right_parameter_mem
  change P.B (P.right.parameter rb) = b + rb * ub at h
  have hz : Q.height (Fin.last Q.count) ∈ Ioo (-P.radius) P.radius :=
    ⟨by linarith [(Q.vertex_height_bounds (Fin.last Q.count)).1, P.radius_pos],
      (Q.vertex_height_bounds (Fin.last Q.count)).2⟩
  have hg := (sub_pos.mpr (P.separated _ hz)).ne'
  rw [Q.height_last] at hg
  simp only [parameterCut, Q.cut_last, Q.height_last, obliqueProjection, ← h, div_self hg]

private theorem smooth_piece (i : Fin Q.count) : ContDiff ℝ ∞ (Q.piece i) := by
  rw [(Q.piece i).decomp]
  exact (Q.piece i).linear.toContinuousLinearMap.contDiff.add contDiff_const


def pieceDomain (i : Fin Q.count) : Set ℝ :=
  X ∩ {x | Q.piece i x - lo x ∈ Ioo (-P.radius) P.radius}

theorem isOpen_pieceDomain (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) (i : Fin Q.count) :
    IsOpen (Q.pieceDomain i) :=
  (((Q.smooth_piece i).continuous.continuousOn).sub hlo.continuousOn).isOpen_inter_preimage
    hX isOpen_Ioo

theorem cell_subset_pieceDomain (i : Fin Q.count) :
    Icc (Q.cut i.castSucc) (Q.cut i.succ) ⊆ Q.pieceDomain i := by
  intro x hx
  have hb := Q.height_bounds i x hx
  exact ⟨Q.cell_domain i hx, by linarith [hb.1, P.radius_pos], hb.2⟩

theorem smooth_projection (hlo : ContDiffOn ℝ ∞ lo X) (i : Fin Q.count) :
    ContDiffOn ℝ ∞ (Q.projection i) (Q.pieceDomain i) := by
  have hz : ContDiffOn ℝ ∞ (fun x => Q.piece i x - lo x) (Q.pieceDomain i) :=
    (Q.smooth_piece i).contDiffOn.sub (hlo.mono (fun _ hx => hx.1))
  have hAc := P.smooth_A.comp hz (fun _ hx => hx.2)
  have hBc := P.smooth_B.comp hz (fun _ hx => hx.2)
  exact (contDiffOn_id.sub hAc).div (hBc.sub hAc)
    (fun x hx => (sub_pos.mpr (P.separated _ hx.2)).ne')

theorem positive_deriv_projection (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (i : Fin Q.count) {x : ℝ} (hx : x ∈ Icc (Q.cut i.castSucc) (Q.cut i.succ)) :
    0 < deriv (Q.projection i) x := by
  have hdom := Q.cell_subset_pieceDomain i hx
  have hdlo : HasDerivAt lo (deriv lo x) x :=
    ((hlo x hdom.1).contDiffAt (hX.mem_nhds hdom.1)).differentiableAt (by simp) |>.hasDerivAt
  have hAz := (P.smooth_A _ hdom.2).contDiffAt (isOpen_Ioo.mem_nhds hdom.2)
  have hBz := (P.smooth_B _ hdom.2).contDiffAt (isOpen_Ioo.mem_nhds hdom.2)
  have hd := hasDerivAt_obliqueProjection (z := fun t => Q.piece i t - lo t) (x := x)
    (hAz.differentiableAt (by simp)) (hBz.differentiableAt (by simp))
    ((Q.piece i).hasDerivAt.sub hdlo) (P.separated _ hdom.2)
  rw [show deriv (Q.projection i) x = obliqueProjectionDerivative P.A P.B
      (x, (Q.piece i x - lo x, (Q.piece i).linear 1 - deriv lo x)) from hd.deriv]
  exact Q.projection_deriv_pos i x hx

theorem strictMonoOn_projection (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (i : Fin Q.count) :
    StrictMonoOn (Q.projection i) (Icc (Q.cut i.castSucc) (Q.cut i.succ)) :=
  strictMonoOn_of_deriv_pos (convex_Icc _ _)
    ((Q.smooth_projection hlo i).continuousOn.mono (Q.cell_subset_pieceDomain i))
    (fun _ hx => Q.positive_deriv_projection hX hlo i (interior_subset hx))

theorem strictMono_parameterCut (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) :
    StrictMono Q.parameterCut := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [← (Q.projection_endpoints i).1, ← (Q.projection_endpoints i).2]
  have hlt := Q.cut_strictMono (Fin.castSucc_lt_succ (i := i))
  exact Q.strictMonoOn_projection hX hlo i
    (left_mem_Icc.mpr hlt.le) (right_mem_Icc.mpr hlt.le) hlt

theorem parameter_cell_subset_unitInterval (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (i : Fin Q.count) : Icc (Q.parameterCut i.castSucc) (Q.parameterCut i.succ) ⊆ Icc (0 : ℝ) 1 := by
  intro t ht
  constructor
  · rw [← Q.parameterCut_first]
    exact ((Q.strictMono_parameterCut hX hlo).monotone (Fin.zero_le i.castSucc)).trans ht.1
  · rw [← Q.parameterCut_last]
    exact ht.2.trans ((Q.strictMono_parameterCut hX hlo).monotone (Fin.le_last i.succ))

private theorem exists_interval_inverse_on {g : ℝ → ℝ} {V : Set ℝ}
    (hV : IsOpen V) (hg : ContDiffOn ℝ ∞ g V) {c d : ℝ} (hcd : c ≤ d)
    (hI : Icc c d ⊆ V) (hpos : ∀ x ∈ Icc c d, 0 < deriv g x) :
    ∃ G : OpenPartialHomeomorph ℝ ℝ,
      Icc c d ⊆ G.source ∧ G.source ⊆ V ∧ (∀ x, G x = g x) ∧
      ContDiffOn ℝ ∞ G G.source ∧ ContDiffOn ℝ ∞ G.symm G.target ∧
      g '' Icc c d = Icc (g c) (g d) := by
  have hP : IsOpen (V ∩ {x | 0 < deriv g x}) :=
    (hg.continuousOn_deriv_of_isOpen hV (by simp)).isOpen_inter_preimage hV isOpen_Ioi
  obtain ⟨l, r, hl, hr, hclosed⟩ := exists_larger_closed_interval hP hcd
    (fun x hx => ⟨hI hx, hpos x hx⟩)
  have hWV : Ioo l r ⊆ V := fun x hx => (hclosed ⟨hx.1.le, hx.2.le⟩).1
  have hWpos : ∀ x ∈ Ioo l r, 0 < deriv g x :=
    fun x hx => (hclosed ⟨hx.1.le, hx.2.le⟩).2
  have hIW : Icc c d ⊆ Ioo l r := fun x hx => ⟨hl.trans_le hx.1, hx.2.trans_lt hr⟩
  have hmono : StrictMonoOn g (Ioo l r) :=
    strictMonoOn_of_deriv_pos (convex_Ioo _ _) (hg.continuousOn.mono hWV)
      (fun x hx => hWpos x (interior_subset hx))
  have hopenmap : IsOpenMap ((Ioo l r).domRestrict g) := by
    apply isOpenMap_iff_nhds_le.mpr
    intro x
    have hat := (hg x (hWV x.property)).contDiffAt (hV.mem_nhds (hWV x.property))
    have hd := (hat.hasStrictDerivAt (by simp)).hasStrictFDerivAt_equiv
      (hWpos x x.property).ne'
    change 𝓝 (g x) ≤ Filter.map (g ∘ Subtype.val) (𝓝 x)
    rw [← Filter.map_map, isOpen_Ioo.isOpenEmbedding_subtypeVal.map_nhds_eq,
      hd.map_nhds_eq_of_equiv]
  let G := OpenPartialHomeomorph.ofContinuousOpenRestrict
    (hmono.injOn.toPartialEquiv g (Ioo l r)) (hg.continuousOn.mono hWV) hopenmap isOpen_Ioo
  refine ⟨G, hIW, hWV, fun _ => rfl, hg.mono hWV, ?_, ?_⟩
  · intro y hy
    have hs : G.symm y ∈ Ioo l r := G.map_target hy
    have hat := (hg _ (hWV hs)).contDiffAt (hV.mem_nhds (hWV hs))
    have hd := (hat.hasStrictDerivAt (by simp)).hasStrictFDerivAt_equiv (hWpos _ hs).ne'
    exact (G.contDiffAt_symm hy hd.hasFDerivAt hat).contDiffWithinAt
  · exact (hg.continuousOn.mono hI).image_Icc_of_monotoneOn hcd
      (hmono.monotoneOn.mono hIW)


structure PieceCoordinates (i : Fin Q.count) where
  parameter : OpenPartialHomeomorph ℝ ℝ
  source_contains : Icc (Q.cut i.castSucc) (Q.cut i.succ) ⊆ parameter.source
  source_subset : parameter.source ⊆ Q.pieceDomain i
  map_eq : ∀ x, parameter x = Q.projection i x
  smooth : ContDiffOn ℝ ∞ parameter parameter.source
  smooth_symm : ContDiffOn ℝ ∞ parameter.symm parameter.target
  image_cell : Q.projection i '' Icc (Q.cut i.castSucc) (Q.cut i.succ) =
    Icc (Q.parameterCut i.castSucc) (Q.parameterCut i.succ)

theorem exists_pieceCoordinates (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (i : Fin Q.count) : Nonempty (Q.PieceCoordinates i) := by
  obtain ⟨G, hsource, hsub, heq, hsmooth, hinv, himage⟩ :=
    exists_interval_inverse_on (Q.isOpen_pieceDomain hX hlo i) (Q.smooth_projection hlo i)
      (Q.cut_strictMono (Fin.castSucc_lt_succ (i := i))).le
      (Q.cell_subset_pieceDomain i) (fun x hx => Q.positive_deriv_projection hX hlo i hx)
  refine ⟨⟨G, hsource, hsub, heq, hsmooth, hinv, ?_⟩⟩
  simpa only [(Q.projection_endpoints i).1, (Q.projection_endpoints i).2] using himage


noncomputable def pieceCoordinates (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X)
    (i : Fin Q.count) : Q.PieceCoordinates i := Classical.choice (Q.exists_pieceCoordinates hX hlo i)

namespace PieceCoordinates

variable {Q} {i : Fin Q.count} (C : Q.PieceCoordinates i)


noncomputable def upperGraph (t : ℝ) : ℝ :=
  Q.piece i (C.parameter.symm t) - lo (C.parameter.symm t)

theorem smooth_upperGraph (hlo : ContDiffOn ℝ ∞ lo X) :
    ContDiffOn ℝ ∞ C.upperGraph C.parameter.target := by
  have hz : ContDiffOn ℝ ∞ (fun x => Q.piece i x - lo x) C.parameter.source :=
    (Q.smooth_piece i).contDiffOn.sub (hlo.mono (fun _ hx => (C.source_subset hx).1))
  exact hz.comp C.smooth_symm (fun _ ht => C.parameter.map_target ht)

theorem parameter_mem_target {t : ℝ}
    (ht : t ∈ Icc (Q.parameterCut i.castSucc) (Q.parameterCut i.succ)) :
    t ∈ C.parameter.target := by
  rw [← C.image_cell] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  rw [← C.map_eq]
  exact C.parameter.map_source (C.source_contains hx)

theorem inverse_mem_cell {t : ℝ}
    (ht : t ∈ Icc (Q.parameterCut i.castSucc) (Q.parameterCut i.succ)) :
    C.parameter.symm t ∈ Icc (Q.cut i.castSucc) (Q.cut i.succ) := by
  rw [← C.image_cell] at ht
  obtain ⟨x, hx, rfl⟩ := ht
  rw [← C.map_eq, C.parameter.left_inv (C.source_contains hx)]
  exact hx

theorem upperGraph_bounds {t : ℝ}
    (ht : t ∈ Icc (Q.parameterCut i.castSucc) (Q.parameterCut i.succ)) :
    0 < C.upperGraph t ∧ C.upperGraph t < P.radius :=
  Q.height_bounds i _ (C.inverse_mem_cell ht)

theorem upperGraph_lt_cap {t : ℝ}
    (ht : t ∈ Icc (Q.parameterCut i.castSucc) (Q.parameterCut i.succ)) :
    C.upperGraph t < Q.height_cap := Q.height_lt_cap i _ (C.inverse_mem_cell ht)



theorem band_subset_coordinates_source (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) :
    {q : ℝ × ℝ | q.1 ∈ Icc (Q.parameterCut i.castSucc) (Q.parameterCut i.succ) ∧
      0 ≤ q.2 ∧ q.2 ≤ C.upperGraph q.1} ⊆ (P.coordinates hX hlo).source := by
  intro q hq
  have ht := Q.parameter_cell_subset_unitInterval hX hlo i hq.1
  have hz : q.2 ∈ Icc (0 : ℝ) Q.height_cap :=
    ⟨hq.2.1, hq.2.2.trans (C.upperGraph_lt_cap hq.1).le⟩
  have hzradius : q.2 ∈ Ioo (-P.radius) P.radius :=
    ⟨by linarith [hz.1, P.radius_pos], hz.2.trans_lt Q.height_cap_lt_radius⟩
  change q ∈ (obliqueStripCoordinates isOpen_Ioo P.smooth_A P.smooth_B P.separated hX hlo).source
  rw [obliqueStripCoordinates_source]
  refine ⟨hzradius, Q.height_cap_domain q.2 hz ?_⟩
  have hg := P.separated q.2 hzradius
  constructor
  · nlinarith [mul_nonneg ht.1 (sub_pos.mpr hg).le]
  · nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_pos.mpr hg).le]

theorem upperGraph_endpoints :
    C.upperGraph (Q.parameterCut i.castSucc) = Q.height i.castSucc ∧
      C.upperGraph (Q.parameterCut i.succ) = Q.height i.succ := by
  have hle := (Q.cut_strictMono (Fin.castSucc_lt_succ (i := i))).le
  have hleft := C.parameter.left_inv (C.source_contains (left_mem_Icc.mpr hle))
  have hright := C.parameter.left_inv (C.source_contains (right_mem_Icc.mpr hle))
  rw [C.map_eq, (Q.projection_endpoints i).1] at hleft
  rw [C.map_eq, (Q.projection_endpoints i).2] at hright
  simp [upperGraph, hleft, hright, (Q.piece_endpoints i).1, (Q.piece_endpoints i).2]

theorem strip_upperGraph_eq {t : ℝ}
    (ht : t ∈ Icc (Q.parameterCut i.castSucc) (Q.parameterCut i.succ)) :
    obliqueStripMap P.A P.B lo (t, C.upperGraph t) =
      (C.parameter.symm t, Q.piece i (C.parameter.symm t)) := by
  have hcell := C.inverse_mem_cell ht
  have hz : C.upperGraph t ∈ Ioo (-P.radius) P.radius :=
    ⟨by linarith [(C.upperGraph_bounds ht).1, P.radius_pos], (C.upperGraph_bounds ht).2⟩
  have hgap := (sub_pos.mpr (P.separated _ hz)).ne'
  have hparam := C.parameter.right_inv (C.parameter_mem_target ht)
  rw [C.map_eq] at hparam
  change obliqueProjection P.A P.B (C.parameter.symm t) (C.upperGraph t) = t at hparam
  have hx : P.A (C.upperGraph t) + t * (P.B (C.upperGraph t) - P.A (C.upperGraph t)) =
      C.parameter.symm t := by
    have hm := congrArg (fun r => r * (P.B (C.upperGraph t) - P.A (C.upperGraph t))) hparam
    dsimp [obliqueProjection] at hm
    rw [div_mul_cancel₀ _ hgap] at hm
    linarith
  simp only [obliqueStripMap, hx]
  dsimp [upperGraph]
  simp



theorem image_upperGraph_eq_segment :
    (fun t => obliqueStripMap P.A P.B lo (t, C.upperGraph t)) ''
        Icc (Q.parameterCut i.castSucc) (Q.parameterCut i.succ) =
      segment ℝ (Q.cut i.castSucc, lo (Q.cut i.castSucc) + Q.height i.castSucc)
        (Q.cut i.succ, lo (Q.cut i.succ) + Q.height i.succ) := by
  let J := Icc (Q.cut i.castSucc) (Q.cut i.succ)
  have himage : (fun t => obliqueStripMap P.A P.B lo (t, C.upperGraph t)) ''
      Icc (Q.parameterCut i.castSucc) (Q.parameterCut i.succ) =
      (fun x => (x, Q.piece i x)) '' J := by
    apply Subset.antisymm
    · rintro _ ⟨t, ht, rfl⟩
      exact ⟨C.parameter.symm t, C.inverse_mem_cell ht, (C.strip_upperGraph_eq ht).symm⟩
    · rintro _ ⟨x, hx, rfl⟩
      have ht : C.parameter x ∈ Icc (Q.parameterCut i.castSucc) (Q.parameterCut i.succ) := by
        rw [C.map_eq, ← C.image_cell]
        exact mem_image_of_mem _ hx
      refine ⟨C.parameter x, ht, ?_⟩
      change obliqueStripMap P.A P.B lo (C.parameter x, C.upperGraph (C.parameter x)) =
        (x, Q.piece i x)
      rw [C.strip_upperGraph_eq ht, C.parameter.left_inv (C.source_contains hx)]
  rw [himage]
  have hseg := image_segment ℝ ((AffineMap.id ℝ ℝ).prod (Q.piece i))
    (Q.cut i.castSucc) (Q.cut i.succ)
  rw [segment_eq_Icc (Q.cut_strictMono (Fin.castSucc_lt_succ (i := i))).le] at hseg
  simpa only [AffineMap.prod_apply, AffineMap.id_apply,
    (Q.piece_endpoints i).1, (Q.piece_endpoints i).2] using hseg

theorem coordinates_image_upperGraph_eq_segment
    (hX : IsOpen X) (hlo : ContDiffOn ℝ ∞ lo X) :
    (fun t => P.coordinates hX hlo (t, C.upperGraph t)) ''
        Icc (Q.parameterCut i.castSucc) (Q.parameterCut i.succ) =
      segment ℝ (Q.cut i.castSucc, lo (Q.cut i.castSucc) + Q.height i.castSucc)
        (Q.cut i.succ, lo (Q.cut i.succ) + Q.height i.succ) := by
  simpa only [P.coordinates_apply] using C.image_upperGraph_eq_segment

end PieceCoordinates

end ObliquePolygonalBoundary

end Poincare.Topology.Plane.Curves
