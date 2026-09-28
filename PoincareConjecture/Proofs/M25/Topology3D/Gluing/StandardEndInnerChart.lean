import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SchoenfliesCompactSide

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M25.Topology3D.SchoenfliesData

theorem exists_buffered_interior_chart
    {W : Type u} [TopologicalSpace W] [ChartedSpace E3 W]
    [IsManifold (𝓡 3) ∞ W]
    (Phi0 : Diffeomorph (𝓡 3) (𝓡 3) W E3 ∞)
    (e : OpenPartialHomeomorph (UnitTwoSphere × ℝ) W)
    {a b c h δ tl tm : ℝ}
    (S : SchoenfliesData (fun p => Phi0 (e (p.1, c + h * p.2))) δ)
    (hsource : e.source = univ ×ˢ Ioo a b)
    (hend : ∀ d ∈ Ioo a b, IsCompact (e.cylinderTail b d)ᶜ)
    (hh : 0 < h) (ha : a < c - h) (hb : c + h < b)
    (hδ : 0 ≤ δ) (hlo : δ < tl) (hlm : tl < tm) (hhi : tm < 1) :
    let l := c + h * tl
    let m := c + h * tm
    let rL := S.radial tl
    let rM := S.radial tm
    ∃ I : OpenPartialHomeomorph W E3,
      I.source = interior (e.cylinderTail b m)ᶜ ∧
      I.target = ball 0 rM ∧
      (I.symm : E3 → W) = (fun z => Phi0.symm (S.chart z)) ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ I I.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ I.symm I.target ∧
      (∀ x ∈ I.source, S.chart (I x) = Phi0 x) ∧
      (∀ q : UnitTwoSphere, ∀ t ∈ Ico δ tm,
        e (q, c + h * t) ∈ I.source ∧
        I (e (q, c + h * t)) = S.radial t • (S.boundary_map q).1) ∧
      I.source ∪ e.cylinderTail b l = univ ∧
      I.source ∩ e.cylinderTail b l = e '' (univ ×ˢ Ioo l m) ∧
      I.target ∪ {z : E3 | rL < ‖z‖} = univ ∧
      I.target ∩ {z : E3 | rL < ‖z‖} = {z : E3 | rL < ‖z‖ ∧ ‖z‖ < rM} := by
  let l := c + h * tl
  let m := c + h * tm
  let rL := S.radial tl
  let rM := S.radial tm
  have htl : tl ∈ Ico δ 1 := ⟨hlo.le, hlm.trans hhi⟩
  have htm : tm ∈ Ico δ 1 := ⟨(hlo.trans hlm).le, hhi⟩
  have hheight (t : ℝ) (ht : t ∈ Ico δ 1) : c + h * t ∈ Ioo a b := by
    have ht0 : 0 ≤ t := hδ.trans ht.1
    have hmul := mul_lt_mul_of_pos_left ht.2 hh
    have hnonneg : 0 ≤ h * t := mul_nonneg hh.le ht0
    constructor <;> nlinarith
  have hl : l ∈ Ioo a b := hheight tl htl
  have hm : m ∈ Ioo a b := hheight tm htm
  have hlm' : l < m := by
    change c + h * tl < c + h * tm
    linarith [mul_lt_mul_of_pos_left hlm hh]
  have hrLM : rL < rM := S.radial_strictMono htl htm hlm
  have hrM : rM < S.radius := S.radial_lt tm htm
  have hside := S.side_eq_one_of_cofinal_cylinder
    Phi0.toHomeomorph e hsource hend hh ha hb hδ (hlo.trans (hlm.trans hhi))
  obtain ⟨C, hCs, _, hC, _, hCi⟩ := S.exists_chart_openPartialHomeomorph
  have hsmall : ball (0 : E3) rM ⊆ C.source := by
    rw [hCs]
    exact ball_subset_ball hrM.le
  let CM := C.restrOpen (ball 0 rM) isOpen_ball
  have hCMs : CM.source = ball 0 rM := inter_eq_right.mpr hsmall
  have hCMfun : (CM : E3 → E3) = S.chart := hC
  have hCMt : CM.target = S.chart '' ball 0 rM := by
    rw [← CM.image_source_eq_target, hCMs, hCMfun]
  have hCMt_sub : CM.target ⊆ C.target := by
    rw [hCMt, ← hC]
    rintro x ⟨z, hz, rfl⟩
    exact C.map_source (hsmall hz)
  let I := Phi0.toHomeomorph.transOpenPartialHomeomorph CM.symm
  have hIt : I.target = ball 0 rM := hCMs
  have hIi : (I.symm : E3 → W) = fun z => Phi0.symm (S.chart z) := by
    funext z
    change Phi0.symm (CM z) = Phi0.symm (S.chart z)
    rw [hCMfun]
  have hIs : I.source = interior (e.cylinderTail b m)ᶜ := by
    rw [S.interior_compl_cylinderTail_eq_buffered_ball
      Phi0.toHomeomorph e hsource hend hh ha hb hδ htm]
    change Phi0 ⁻¹' CM.target = Phi0.symm '' (S.chart '' ball 0 rM)
    rw [hCMt]
    ext x
    constructor
    · intro hx
      exact ⟨Phi0 x, hx, Phi0.symm_apply_apply x⟩
    · rintro ⟨z, hz, rfl⟩
      change Phi0 (Phi0.symm z) ∈ S.chart '' ball 0 rM
      rwa [Phi0.apply_symm_apply]
  have hfront : frontier (e.cylinderTail b m) = e.cylinderSlice m := by
    calc
      frontier (e.cylinderTail b m) = frontier (e.cylinderTail b m)ᶜ :=
        (frontier_compl _).symm
      _ = frontier (Phi0.symm '' (S.chart '' closedBall 0 rM)) := by
        rw [S.compl_cylinderTail_eq_buffered_ball
          Phi0.toHomeomorph e hsource hend hh ha hb hδ htm]
        rfl
      _ = e.cylinderSlice m := by
        simpa only [hside, one_mul, Diffeomorph.coe_toHomeomorph_symm, rM, m] using
          S.frontier_buffered_ball Phi0.toHomeomorph e htm
  have hclosure : closure (e.cylinderTail b m) =
      e.cylinderTail b m ∪ e.cylinderSlice m := by
    rw [closure_eq_self_union_frontier, hfront]
  have hclosure_sub : closure (e.cylinderTail b m) ⊆ e.cylinderTail b l := by
    rw [hclosure]
    apply union_subset ((e.cylinderTail_antitone b) hlm'.le)
    rintro x ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩
    have hs' : s = m := hs
    exact ⟨(q, s), ⟨mem_univ _, hs' ▸ ⟨hlm', hm.2⟩⟩, rfl⟩
  have hIclosure : I.source = (closure (e.cylinderTail b m))ᶜ := by
    rw [hIs, interior_compl]
  have hslice (x : W) (hx : x ∈ e.target) :
      x ∈ e.cylinderSlice m ↔ (e.symm x).2 = m := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzm : z.2 = m := hz.2
      have hzs : z ∈ e.source := by
        rw [hsource]
        exact ⟨mem_univ _, hzm ▸ hm⟩
      rw [e.left_inv hzs]
      exact hzm
    · intro hxm
      exact ⟨e.symm x, ⟨mem_univ _, hxm⟩, e.right_inv hx⟩
  refine ⟨I, hIs, hIt, hIi, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ CM.symm CM.target :=
      hCi.contMDiffOn.mono hCMt_sub
    exact hi.comp Phi0.contMDiff.contMDiffOn (fun _ hx => hx)
  · rw [hIi, hIt]
    exact Phi0.symm.contMDiff.comp_contMDiffOn
      (S.chart_smooth.mono (ball_subset_ball hrM.le)).contMDiffOn
  · intro x hx
    change S.chart (CM.symm (Phi0 x)) = Phi0 x
    rw [← hCMfun]
    exact CM.right_inv hx
  · intro q t ht
    have ht1 : t ∈ Ico δ 1 := ⟨ht.1, ht.2.trans hhi⟩
    have hv : S.radial t • (S.boundary_map q).1 ∈ CM.source := by
      rw [hCMs, mem_ball_zero_iff, norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp (S.boundary_map q).2, mul_one,
        abs_of_pos (S.radial_pos t ht1)]
      exact S.radial_strictMono ht1 htm ht.2
    have hcollar : S.chart (S.radial t • (S.boundary_map q).1) =
        Phi0 (e (q, c + h * t)) := by
      simpa only [hside, one_mul] using S.chart_collar q t ht1
    constructor
    · change Phi0 (e (q, c + h * t)) ∈ CM.target
      rw [← hcollar, ← hCMfun]
      exact CM.map_source hv
    · change CM.symm (Phi0 (e (q, c + h * t))) =
        S.radial t • (S.boundary_map q).1
      rw [← hcollar, ← hCMfun, CM.left_inv hv]
  · rw [hIclosure]
    ext x
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hx : x ∈ closure (e.cylinderTail b m)
    · exact Or.inr (hclosure_sub hx)
    · exact Or.inl hx
  · ext x
    constructor
    · rintro ⟨hxI, hxL⟩
      have hxnot : x ∉ closure (e.cylinderTail b m) := by
        rwa [hIclosure] at hxI
      obtain ⟨hxt, hs⟩ := (e.mem_cylinderTail_iff hsource hl.1 x).mp hxL
      have hsm : (e.symm x).2 < m := by
        by_contra! hle
        rcases hle.lt_or_eq with hlt | heq
        · exact hxnot (subset_closure
            ((e.mem_cylinderTail_iff hsource hm.1 x).mpr ⟨hxt, hlt, hs.2⟩))
        · apply hxnot
          rw [hclosure]
          exact Or.inr ((hslice x hxt).mpr heq.symm)
      exact ⟨e.symm x, ⟨mem_univ _, hs.1, hsm⟩, e.right_inv hxt⟩
    · rintro ⟨z, ⟨_, hz⟩, rfl⟩
      have hzs : z ∈ e.source := by
        rw [hsource]
        exact ⟨mem_univ _, hl.1.trans hz.1, hz.2.trans hm.2⟩
      refine ⟨?_, ⟨z, ⟨mem_univ _, hz.1, hz.2.trans hm.2⟩, rfl⟩⟩
      rw [hIclosure]
      intro hx
      rw [hclosure] at hx
      rcases hx with hxM | hxS
      · have hs := ((e.mem_cylinderTail_iff hsource hm.1 (e z)).mp hxM).2.1
        rw [e.left_inv hzs] at hs
        exact lt_asymm hz.2 hs
      · have hs := (hslice (e z) (e.map_source hzs)).mp hxS
        rw [e.left_inv hzs] at hs
        exact hz.2.ne hs
  · rw [hIt]
    ext z
    simp only [mem_union, mem_ball_zero_iff, mem_ofPred_eq, mem_univ, iff_true]
    by_cases hz : ‖z‖ < rM
    · exact Or.inl hz
    · exact Or.inr (hrLM.trans_le (le_of_not_gt hz))
  · rw [hIt]
    ext z
    simp only [mem_inter_iff, mem_ball_zero_iff, mem_ofPred_eq]
    change (‖z‖ < rM ∧ rL < ‖z‖) ↔ (rL < ‖z‖ ∧ ‖z‖ < rM)
    exact and_comm

end PoincareConjecture.M25.Topology3D.SchoenfliesData
