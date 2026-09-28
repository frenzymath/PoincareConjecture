import PoincareConjecture.Proofs.M25.Topology3D.Gluing.StandardEndInnerChart
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.SchoenfliesRadialExtension
import PoincareConjecture.Proofs.M25.Topology3D.Gluing.CollarAbsorption
import PoincareConjecture.Proofs.M25.Mathlib.PositivePolar












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology EuclideanSpace

universe u

namespace PoincareConjecture.M25.Topology3D.SchoenfliesData





theorem exists_compatible_buffered_end_charts
    {W : Type u} [TopologicalSpace W] [ChartedSpace E3 W]
    [IsManifold (𝓡 3) ∞ W]
    (Phi0 : Diffeomorph (𝓡 3) (𝓡 3) W E3 ∞)
    (e : OpenPartialHomeomorph (UnitTwoSphere × ℝ) W)
    {a b c h δ tl tm tu : ℝ}
    (S : SchoenfliesData (fun p => Phi0 (e (p.1, c + h * p.2))) δ)
    (D : DiffSphereIsotopyData S.boundary_map)
    (hsource : e.source = univ ×ˢ Ioo a b)
    (he : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target)
    (hend : ∀ d ∈ Ioo a b, IsCompact (e.cylinderTail b d)ᶜ)
    (hEmbedding : IsCollarEmbedding (fun p => Phi0 (e (p.1, c + h * p.2))))
    (hh : 0 < h) (ha : a < c - h) (hb : c + h < b)
    (hδ : 0 ≤ δ) (hlo : δ < tl) (hlm : tl < tm) (hmu : tm < tu) (hhi : tu < 1) :
    let l := c + h * tl
    let m := c + h * tm
    let u := c + h * tu
    let rL := S.radial tl
    let rM := S.radial tm
    let χ := fun s => collarCutoff (-u) (-m) (-s)
    ∃ (rho : OpenPartialHomeomorph ℝ ℝ) (I O : OpenPartialHomeomorph W E3),
      rho.source = Ioo l b ∧ rho.target = Ioi rL ∧
      ContDiffOn ℝ ∞ (rho : ℝ → ℝ) (Ioo (c + h * δ) b) ∧
      ContDiffOn ℝ ∞ rho.symm rho.target ∧
      EqOn (rho : ℝ → ℝ) (fun s => S.radial ((s - c) / h)) (Icc l m) ∧
      StrictMonoOn (rho : ℝ → ℝ) (Ico l b) ∧
      (∀ s ∈ Ico l b, 0 < rho s) ∧
      (∀ s ∈ Ico l b, 0 < deriv (rho : ℝ → ℝ) s) ∧
      Tendsto (rho : ℝ → ℝ) (𝓝[<] b) atTop ∧
      I.source = interior (e.cylinderTail b m)ᶜ ∧ I.target = ball 0 rM ∧
      (I.symm : E3 → W) = (fun z => Phi0.symm (S.chart z)) ∧
      O.source = e.cylinderTail b l ∧ O.target = {z : E3 | rL < ‖z‖} ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ I I.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ O O.source ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ I.symm I.target ∧
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ O.symm O.target ∧
      I.source ∪ O.source = univ ∧ I.target ∪ O.target = univ ∧
      EqOn (I : W → E3) O (I.source ∩ O.source) ∧
      EqOn (I.symm : E3 → W) O.symm (I.target ∩ O.target) ∧
      (∀ x : W, O x = rho (e.symm x).2 •
        (D.isotopy (χ (e.symm x).2) (e.symm x).1).1) ∧
      (∀ q : UnitTwoSphere, ∀ s ∈ Ico u b,
        O (e (q, s)) = rho s • (sphereMap D.isometry q).1) := by
  let l := c + h * tl
  let m := c + h * tm
  let u := c + h * tu
  let rL := S.radial tl
  let rM := S.radial tm
  let χ : ℝ → ℝ := fun s => collarCutoff (-u) (-m) (-s)
  have hLl : c + h * δ < l := by
    dsimp only [l]
    linarith [mul_lt_mul_of_pos_left hlo hh]
  have hlm' : l < m := by
    dsimp only [l, m]
    linarith [mul_lt_mul_of_pos_left hlm hh]
  have hmu' : m < u := by
    dsimp only [m, u]
    linarith [mul_lt_mul_of_pos_left hmu hh]
  have hub : u < b := by
    dsimp only [u]
    nlinarith [mul_lt_mul_of_pos_left hhi hh]
  have hmb : m < b := hmu'.trans hub
  have hal : a < l := by
    dsimp only [l]
    nlinarith [mul_pos hh (hδ.trans_lt hlo)]
  have htm1 : tm < 1 := hmu.trans hhi
  have htl : tl ∈ Ico δ 1 := ⟨hlo.le, hlm.trans htm1⟩
  have hrL : 0 < rL := S.radial_pos tl htl
  have hside := S.side_eq_one_of_cofinal_cylinder
    Phi0.toHomeomorph e hsource hend hh ha hb hδ (hlo.trans htl.2)
  have hnormalize (t : ℝ) : (c + h * t - c) / h = t := by
    field_simp [hh.ne']
    ring
  have hrestore (s : ℝ) : c + h * ((s - c) / h) = s := by
    field_simp [hh.ne']
    ring
  have hnormalized (s : ℝ) (hs : s ∈ Ioo l m) : (s - c) / h ∈ Ico δ tm := by
    have ht : tl < (s - c) / h := by
      apply (lt_div_iff₀ hh).mpr
      dsimp only [l] at hs
      nlinarith [hs.1]
    refine ⟨(hlo.trans ht).le, (div_lt_iff₀ hh).mpr ?_⟩
    dsimp only [m] at hs
    nlinarith [hs.2]
  obtain ⟨I, hIs, hIt, hIi, hI, hIinv, _, hIcollar, hcoverS, hinterS, hcoverT, hinterT⟩ :=
    S.exists_buffered_interior_chart Phi0 e hsource hend hh ha hb hδ hlo hlm htm1
  obtain ⟨rho, hRs, hRt, hR, hRi, hReq, hRmono, hRpos, hRderiv, hRlim⟩ :=
    S.exists_radial_extension hEmbedding hδ hh hlo hlm hmu hhi hub
  have hRsource : ContDiffOn ℝ ∞ (rho : ℝ → ℝ) rho.source := by
    apply hR.mono
    rw [hRs]
    exact fun s hs => ⟨hLl.trans hs.1, hs.2⟩
  have hχ : ContDiff ℝ ∞ χ :=
    (contDiff_collarCutoff (-u) (-m)).comp contDiff_neg
  have hχone (s : ℝ) (hs : s ≤ m) : χ s = 1 :=
    collarCutoff_eq_one (neg_lt_neg hmu') (neg_le_neg hs)
  have hχzero (s : ℝ) (hs : u ≤ s) : χ s = 0 :=
    collarCutoff_eq_zero (neg_lt_neg hmu') (neg_le_neg hs)
  let B := sphereIsotopyAbsorption D.isotopy_smooth D.isotopy_diffeo χ hχ
  have hB (p : UnitTwoSphere × ℝ) : B p = (D.isotopy (χ p.2) p.1, p.2) := rfl
  have hBlo (q : UnitTwoSphere) (s : ℝ) (hs : s ≤ m) :
      B (q, s) = (S.boundary_map q, s) := by
    rw [hB, hχone s hs, D.isotopy_one]
  have hBilo (w : UnitTwoSphere) (s : ℝ) (hs : s ≤ m) :
      B.symm (w, s) = (S.boundary_map.symm w, s) := by
    have hi := congrArg B.symm (hBlo (S.boundary_map.symm w) s hs)
    rw [B.symm_apply_apply, S.boundary_map.apply_symm_apply] at hi
    exact hi.symm
  obtain ⟨q0, hq0⟩ := (NormedSpace.sphere_nonempty (E := E3) (x := 0) (r := 1)).mpr
    (by norm_num)
  obtain ⟨P, hPs, hPt, hPf, hPh, _, hP, hPi⟩ :=
    exists_smooth_positive_polar_chart (n := 2) (⟨q0, hq0⟩ : UnitTwoSphere)
      rho l b rL hRs hRt hrL hRsource hRi
  let PB := B.toHomeomorph.transOpenPartialHomeomorph P
  have hPBs : PB.source = univ ×ˢ Ioo l b := by
    change B ⁻¹' P.source = univ ×ˢ Ioo l b
    rw [hPs]
    ext p
    change B p ∈ univ ×ˢ Ioo l b ↔ p ∈ univ ×ˢ Ioo l b
    rw [hB]
    rfl
  have hPBt : PB.target = {z : E3 | rL < ‖z‖} := hPt
  have hPB : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ PB PB.source :=
    hP.comp B.contMDiff.contMDiffOn (fun _ hx => hx)
  have hPBi : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ PB.symm PB.target :=
    B.symm.contMDiff.comp_contMDiffOn hPi
  let EL := e.restrOpen (univ ×ˢ Ioo l b) (isOpen_univ.prod isOpen_Ioo)
  have hELs : EL.source = univ ×ˢ Ioo l b :=
    inter_eq_right.mpr (e.cylinderTail_domain_subset hsource hal)
  have hELt : EL.target = e.cylinderTail b l := by
    rw [← EL.image_source_eq_target, hELs]
    rfl
  have hELt_sub : EL.target ⊆ e.target := by
    rw [hELt]
    exact e.cylinderTail_subset_target hsource hal
  have hEL : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ EL EL.source :=
    he.mono inter_subset_left
  have hELi : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ EL.symm EL.target :=
    hei.mono hELt_sub
  have hmatch : EL.symm.target = PB.source := by
    change EL.source = PB.source
    rw [hELs, hPBs]
  let O := EL.symm.trans' PB hmatch
  have hOs : O.source = e.cylinderTail b l := hELt
  have hOt : O.target = {z : E3 | rL < ‖z‖} := hPBt
  have hO : ContMDiffOn (𝓡 3) (𝓡 3) ∞ O O.source :=
    hPB.comp hELi (fun x hx => hmatch ▸ EL.symm.map_source hx)
  have hOi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ O.symm O.target :=
    hEL.comp hPBi (fun z hz => by
      change PB.symm z ∈ EL.source
      rw [show EL.source = PB.source from hmatch]
      exact PB.map_target hz)
  have hOformula (x : W) : O x = rho (e.symm x).2 •
      (D.isotopy (χ (e.symm x).2) (e.symm x).1).1 := by
    change P (B (e.symm x)) = _
    rw [hPf, hB]
  have hOinverse (z : E3) : O.symm z = e (B.symm (P.symm z)) := rfl
  have hfl : S.radial ((l - c) / h) = rL := by
    dsimp only [l, rL]
    rw [hnormalize]
  have hfm : S.radial ((m - c) / h) = rM := by
    dsimp only [m, rM]
    rw [hnormalize]
  have hRopen : Ioo l m ⊆ rho.source := by
    rw [hRs]
    exact fun s hs => ⟨hs.1, hs.2.trans hmb⟩
  have hRclosed : Icc l m ⊆ Ioo (c + h * δ) b :=
    fun s hs => ⟨hLl.trans_le hs.1, hs.2.trans_lt hmb⟩
  have hRclosed' : Icc l m ⊆ Ico l b := fun s hs => ⟨hs.1, hs.2.trans_lt hmb⟩
  obtain ⟨_, hRinterval⟩ := rho.image_Ioo_and_symm_of_eqOn_Icc hlm'.le hRopen
    (hR.continuousOn.mono hRclosed) (hRmono.mono hRclosed') hReq
  rw [hfl, hfm] at hRinterval
  have hforward : EqOn (I : W → E3) O (I.source ∩ O.source) := by
    intro x hx
    rw [hOs, hinterS] at hx
    obtain ⟨⟨q, s⟩, ⟨_, hs⟩, rfl⟩ := hx
    have hzs : (q, s) ∈ e.source := by
      rw [hsource]
      exact ⟨mem_univ _, hal.trans hs.1, hs.2.trans hmb⟩
    have hval := (hIcollar q ((s - c) / h) (hnormalized s hs)).2
    rw [hrestore] at hval
    rw [hOformula, e.left_inv hzs, hχone s hs.2.le, D.isotopy_one,
      hReq ⟨hs.1.le, hs.2.le⟩]
    exact hval
  have hinverse : EqOn (I.symm : E3 → W) O.symm (I.target ∩ O.target) := by
    intro z hz
    rw [hOt, hinterT] at hz
    have hzP : z ∈ P.target := by
      rw [hPt]
      exact hz.1
    let p := P.symm z
    have hpheight : p.2 ∈ Ioo l m := by
      change (P.symm z).2 ∈ Ioo l m
      rw [hPh]
      exact (hRinterval ‖z‖ hz).1
    let q := S.boundary_map.symm p.1
    have hq : S.boundary_map q = p.1 := S.boundary_map.apply_symm_apply p.1
    have hvec : rho p.2 • p.1.1 = z := by
      have hv : P p = z := P.right_inv hzP
      rwa [hPf] at hv
    have hradial : rho p.2 = S.radial ((p.2 - c) / h) :=
      hReq ⟨hpheight.1.le, hpheight.2.le⟩
    have houter : O.symm z = e (q, p.2) := by
      rw [hOinverse]
      change e (B.symm (p.1, p.2)) = e (q, p.2)
      rw [hBilo p.1 p.2 hpheight.2.le]
    have ht := hnormalized p.2 hpheight
    have ht1 : (p.2 - c) / h ∈ Ico δ 1 := ⟨ht.1, ht.2.trans htm1⟩
    have hchart : S.chart z = Phi0 (e (q, p.2)) := by
      calc
        S.chart z = S.chart (rho p.2 • p.1.1) := congrArg S.chart hvec.symm
        _ = S.chart (S.radial ((p.2 - c) / h) • (S.boundary_map q).1) := by
          rw [hq, hradial]
        _ = Phi0 (e (q, p.2)) := by
          simpa only [hside, one_mul, hrestore] using S.chart_collar q ((p.2 - c) / h) ht1
    calc
      I.symm z = Phi0.symm (S.chart z) := congrFun hIi z
      _ = e (q, p.2) := by rw [hchart, Phi0.symm_apply_apply]
      _ = O.symm z := houter.symm
  have hupper (q : UnitTwoSphere) (s : ℝ) (hs : s ∈ Ico u b) :
      O (e (q, s)) = rho s • (sphereMap D.isometry q).1 := by
    have hzs : (q, s) ∈ e.source := by
      rw [hsource]
      exact ⟨mem_univ _, ((hal.trans hlm').trans hmu').trans_le hs.1, hs.2⟩
    rw [hOformula, e.left_inv hzs, hχzero s hs.1, D.isotopy_zero]
  refine ⟨rho, I, O, hRs, hRt, hR, hRi, hReq, hRmono, hRpos, hRderiv, hRlim,
    hIs, hIt, hIi, hOs, hOt, hI, hO, hIinv, hOi, ?_, ?_, hforward, hinverse,
    hOformula, hupper⟩
  · rw [hOs]
    exact hcoverS
  · rw [hOt]
    exact hcoverT

end PoincareConjecture.M25.Topology3D.SchoenfliesData
