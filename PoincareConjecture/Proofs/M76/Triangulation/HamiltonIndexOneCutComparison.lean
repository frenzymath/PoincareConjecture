import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneMarkedCut
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneStandardDiskProduct
import PoincareConjecture.Proofs.M76.Triangulation.HamiltonIndexOneCutRegluing

set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76.HamiltonIndexOne

local notation "V2" => (Fin 2 → ℝ)
local notation "W" => (ℝ × (ℝ × ℝ))
local notation "D2" => closedBall (0 : V2) 1
local notation "Q2" => sphere (0 : V2) 1

private theorem exists_half_strip_chart {B : Set W}
    {e : frontier squareShell ≃ₜ frontier (complementaryRegion B)}
    (P : HamiltonMarkedDiskProduct e) :
    ∃ u : (D2 ×ˢ Icc (-(P.width / 2)) (P.width / 2)) ≃ₜ P.closedStrip,
      u.IsFinitePL ∧ ∀ x : D2 ×ˢ Icc (-(P.width / 2)) (P.width / 2),
        (u x : W) = P.map x := by
  have hsmall : D2 ×ˢ Icc (-(P.width / 2)) (P.width / 2) ⊆
      D2 ×ˢ Icc (-P.width) P.width := by
    intro x hx
    refine ⟨hx.1, ?_⟩
    constructor <;> linarith [hx.2.1, hx.2.2, P.width_pos]
  have hball := (isFinitePLBallPair_unit_cube (ι := Fin 2)).prod
    (isFinitePLBallPair_Icc (show -(P.width / 2) < P.width / 2 by
      linarith [P.width_pos]))
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hball
  have hf : FinitePiecewiseAffineOn P.map
      (D2 ×ˢ Icc (-(P.width / 2)) (P.width / 2)) := by
    rw [← hKs]
    exact P.piecewiseAffine.restrict K hK (hKs.subset.trans hsmall)
  exact hf.exists_homeomorph_image (P.injective.mono hsmall)

private theorem map_mem_endDisks_iff {B : Set W}
    {e : frontier squareShell ≃ₜ frontier (complementaryRegion B)}
    (P : HamiltonMarkedDiskProduct e) (x : V2 × ℝ)
    (hx : x ∈ D2 ×ˢ Icc (-(P.width / 2)) (P.width / 2)) :
    P.map x ∈ P.endDisks ↔ x.2 = -(P.width / 2) ∨ x.2 = P.width / 2 := by
  have hxfull : x ∈ D2 ×ˢ Icc (-P.width) P.width := by
    refine ⟨hx.1, ?_⟩
    constructor <;> linarith [hx.2.1, hx.2.2, P.width_pos]
  constructor
  · rintro ⟨y, hy, heq⟩
    have hyends : y.2 = -(P.width / 2) ∨ y.2 = P.width / 2 := hy.2
    have hyfull : y ∈ D2 ×ˢ Icc (-P.width) P.width := by
      refine ⟨hy.1, ?_⟩
      rcases hyends with ht | ht <;> rw [ht] <;>
        constructor <;> linarith [P.width_pos]
    have hxy : y = x := P.injective hyfull hxfull heq
    simpa only [hxy] using hyends
  · intro hends
    exact ⟨x, ⟨hx.1, hends⟩, rfl⟩

theorem exists_marked_shell_map_of_disk_product {B : Set W}
    {e : frontier squareShell ≃ₜ frontier (complementaryRegion B)}
    (P : HamiltonMarkedDiskProduct e) (he : e.IsFinitePL)
    (hR : IsCompact (complementaryRegion B)) :
    ∃ H : squareShell ≃ₜ complementaryRegion B, H.IsFinitePL ∧
      ∀ (x : frontier squareShell) (hx : (x : W) ∈ squareShell),
        (H ⟨x, hx⟩ : W) = e x := by
  let P0 := standardDiskProduct P.width_pos P.width_le
  let delta := P.width / 2
  let beta := 14 - delta
  let R := D2 ×ˢ Icc (-delta) delta
  let F := frontier (D2 ×ˢ Icc delta beta)
  have hd : 0 < delta := half_pos P.width_pos
  have hdsmall : delta ≤ (1 / 4 : ℝ) := by
    dsimp [delta]
    linarith [P.width_le]
  have hlt : delta < beta := by dsimp [beta]; linarith
  have hfull (x : V2 × ℝ) (hx : x ∈ R) :
      x ∈ D2 ×ˢ Icc (-P.width) P.width := by
    refine ⟨hx.1, ?_⟩
    dsimp [R, delta] at hx
    constructor <;> linarith [hx.2.1, hx.2.2, P.width_pos]
  have hstandardCompact : IsCompact squareShell :=
    (isCompact_Icc.prod (isCompact_closedBall (0 : ℝ × ℝ) 2)).of_isClosed_subset
      (isClosed_Icc.prod (isClosed_Icc.preimage continuous_norm))
      (fun _ hx => ⟨hx.1, mem_closedBall_zero_iff.mpr hx.2.2⟩)
  have hR0 : IsCompact (complementaryRegion squareMiddleBlock) := by
    rw [complementaryRegion_squareMiddleBlock]
    exact hstandardCompact
  have he0 : standardShellBoundary.IsFinitePL := by
    obtain ⟨f, ⟨K, hK, hKs, _⟩, _⟩ := he
    exact ⟨id, ⟨K, hK, hKs,
      K.affineOnFaces_affine (ContinuousAffineMap.id ℝ W)⟩, fun _ => rfl⟩
  obtain ⟨cut0⟩ := P0.exists_marked_cut_frontier he0 hR0
  obtain ⟨cut1⟩ := P.exists_marked_cut_frontier he hR
  obtain ⟨u0, hu0, hu0val⟩ := exists_half_strip_chart P0
  obtain ⟨u1, hu1, hu1val⟩ := exists_half_strip_chart P
  let strip : P0.closedStrip ≃ₜ P.closedStrip := u0.symm.trans u1
  have hstrip : strip.IsFinitePL := hu0.symm.trans hu1
  have hsourceval (x : P0.closedStrip) : P0.map (u0.symm x) = (x : W) :=
    (hu0val (u0.symm x)).symm.trans (congrArg Subtype.val (u0.apply_symm_apply x))
  have hstripval (x : P0.closedStrip) : (strip x : W) = P.map (u0.symm x) :=
    hu1val (u0.symm x)
  let cut : frontier P0.cutCarrier ≃ₜ frontier P.cutCarrier :=
    cut0.parametrization.symm.trans cut1.parametrization
  have hcut : cut.IsFinitePL := cut0.piecewiseAffine.symm.trans cut1.piecewiseAffine
  have hcutval (z : F) : (cut (cut0.parametrization z) : W) = cut1.parametrization z := by
    exact congrArg (fun p : F => (cut1.parametrization p : W))
      (cut0.parametrization.symm_apply_apply z)
  obtain ⟨_, _, hfront0, hmeet0, hcover0, _⟩ := P0.cut_geometry hR0
  obtain ⟨_, _, _, hmeet1, hcover1, _⟩ := P.cut_geometry hR
  have hfront : F = (Q2 ×ˢ Icc delta beta) ∪ (D2 ×ˢ ({delta, beta} : Set ℝ)) := by
    change frontier (D2 ×ˢ Icc delta beta) = _
    rw [frontier_prod_eq, isClosed_closedBall.closure_eq, isClosed_Icc.closure_eq,
      frontier_closedBall _ one_ne_zero, frontier_Icc hlt.le, union_comm]
  have hlower (x : D2) : ((x : V2), delta) ∈ F :=
    hfront.symm.subset (Or.inr ⟨x.property, Or.inl rfl⟩)
  have hupper (x : D2) : ((x : V2), beta) ∈ F :=
    hfront.symm.subset (Or.inr ⟨x.property, Or.inr rfl⟩)
  have hoverlap (x : P0.closedStrip) :
      (x : W) ∈ P0.cutCarrier ↔ (strip x : W) ∈ P.cutCarrier := by
    have h0 : (x : W) ∈ P0.cutCarrier ↔ (x : W) ∈ P0.endDisks := by
      rw [← hmeet0]
      exact (and_iff_right x.property).symm
    have h1 : (strip x : W) ∈ P.cutCarrier ↔ (strip x : W) ∈ P.endDisks := by
      rw [← hmeet1]
      exact (and_iff_right (strip x).property).symm
    calc
      (x : W) ∈ P0.cutCarrier ↔ (x : W) ∈ P0.endDisks := h0
      _ ↔ P0.map (u0.symm x) ∈ P0.endDisks := by rw [hsourceval]
      _ ↔ ((u0.symm x : R) : V2 × ℝ).2 = -delta ∨
          ((u0.symm x : R) : V2 × ℝ).2 = delta :=
        map_mem_endDisks_iff P0 _ (u0.symm x).property
      _ ↔ P.map (u0.symm x) ∈ P.endDisks :=
        (map_mem_endDisks_iff P _ (u0.symm x).property).symm
      _ ↔ (strip x : W) ∈ P.endDisks := by rw [hstripval]
      _ ↔ (strip x : W) ∈ P.cutCarrier := h1.symm
  have hcontact : P0.closedStrip ∩ P0.cutCarrier ⊆ frontier P0.cutCarrier := by
    intro x hx
    exact hfront0.symm.subset (Or.inr (hmeet0.subset hx))
  have hagree (x : W) (hxC : x ∈ P0.closedStrip) (hxK : x ∈ P0.cutCarrier) :
      (strip ⟨x, hxC⟩ : W) = cut ⟨x, hcontact ⟨hxC, hxK⟩⟩ := by
    let p : R := u0.symm ⟨x, hxC⟩
    have hpval : P0.map p = x := hsourceval ⟨x, hxC⟩
    have hpends : (p : V2 × ℝ).2 = -delta ∨ (p : V2 × ℝ).2 = delta := by
      apply (map_mem_endDisks_iff P0 p p.property).mp
      rw [hpval]
      exact hmeet0.subset ⟨hxC, hxK⟩
    rcases hpends with hp | hp
    · let y : D2 := ⟨(p : V2 × ℝ).1, p.property.1⟩
      let z : F := ⟨((y : V2), beta), hupper y⟩
      have hp' : (p : V2 × ℝ) = ((y : V2), -delta) := Prod.ext rfl hp
      have hz0 : cut0.parametrization z = ⟨x, hcontact ⟨hxC, hxK⟩⟩ := by
        apply Subtype.ext
        exact (cut0.upper y (hupper y)).trans ((congrArg P0.map hp').symm.trans hpval)
      have hcx : (cut ⟨x, hcontact ⟨hxC, hxK⟩⟩ : W) = cut1.parametrization z :=
        (congrArg (fun w => (cut w : W)) hz0).symm.trans (hcutval z)
      exact (hstripval ⟨x, hxC⟩).trans
        ((congrArg P.map hp').trans ((cut1.upper y (hupper y)).symm.trans hcx.symm))
    · let y : D2 := ⟨(p : V2 × ℝ).1, p.property.1⟩
      let z : F := ⟨((y : V2), delta), hlower y⟩
      have hp' : (p : V2 × ℝ) = ((y : V2), delta) := Prod.ext rfl hp
      have hz0 : cut0.parametrization z = ⟨x, hcontact ⟨hxC, hxK⟩⟩ := by
        apply Subtype.ext
        exact (cut0.lower y (hlower y)).trans ((congrArg P0.map hp').symm.trans hpval)
      have hcx : (cut ⟨x, hcontact ⟨hxC, hxK⟩⟩ : W) = cut1.parametrization z :=
        (congrArg (fun w => (cut w : W)) hz0).symm.trans (hcutval z)
      exact (hstripval ⟨x, hxC⟩).trans
        ((congrArg P.map hp').trans ((cut1.lower y (hlower y)).symm.trans hcx.symm))
  have hstripBoundary (x : frontier squareShell) (hx : (x : W) ∈ P0.closedStrip) :
      (strip ⟨x, hx⟩ : W) = e x := by
    let p : R := u0.symm ⟨x, hx⟩
    have hpval : P0.map p = (x : W) := hsourceval ⟨x, hx⟩
    have hpfront : P0.map p ∈ frontier (complementaryRegion squareMiddleBlock) := by
      rw [complementaryRegion_squareMiddleBlock, hpval]
      exact x.property
    have hpQ : (p : V2 × ℝ).1 ∈ Q2 := (P0.proper p (hfull p p.property)).mp hpfront
    have hs : standardMeridianBandMap p ∈ frontier squareShell := by
      change P0.map p ∈ frontier squareShell
      rw [hpval]
      exact x.property
    have harg : (⟨standardMeridianBandMap p, hs⟩ : frontier squareShell) = x :=
      Subtype.ext hpval
    exact (hstripval ⟨x, hx⟩).trans
      ((P.lateral ⟨(p : V2 × ℝ).1, hpQ⟩ (p : V2 × ℝ).2
        (hfull p p.property).2 hs).trans (congrArg (fun y => (e y : W)) harg))
  obtain ⟨annulus, _, hannulus, _, _⟩ := exists_standard_cut_annulus hd hdsmall
  have hstd (z : Q2 ×ˢ Icc delta beta) : standardMeridianBandMap z ∈ frontier squareShell := by
    rw [← hannulus z]
    exact (annulus z).property.1
  have hcutBoundary (x : frontier squareShell) (hx : (x : W) ∈ frontier P0.cutCarrier) :
      (cut ⟨x, hx⟩ : W) = e x := by
    let z : F := cut0.parametrization.symm ⟨x, hx⟩
    have hz0 : (cut0.parametrization z : W) = x :=
      congrArg Subtype.val (cut0.parametrization.apply_symm_apply ⟨x, hx⟩)
    have hx0 : (x : W) ∈ frontier (complementaryRegion squareMiddleBlock) := by
      rw [complementaryRegion_squareMiddleBlock]
      exact x.property
    have hzside : (z : V2 × ℝ) ∈ Q2 ×ˢ Icc delta beta := by
      rcases hfront.subset z.property with hs | hc
      · exact hs
      have hends : (z : V2 × ℝ).2 = delta ∨ (z : V2 × ℝ).2 = beta := hc.2
      let y : D2 := ⟨(z : V2 × ℝ).1, hc.1⟩
      rcases hends with ht | ht
      · have hz' : z = (⟨((y : V2), delta), hlower y⟩ : F) :=
          Subtype.ext (Prod.ext rfl ht)
        have hvalue : (cut0.parametrization z : W) = P0.map ((y : V2), delta) :=
          (congrArg (fun w => (cut0.parametrization w : W)) hz').trans (cut0.lower y (hlower y))
        have hyfull : ((y : V2), delta) ∈ D2 ×ˢ Icc (-P.width) P.width :=
          hfull _ ⟨y.property, by constructor <;> linarith⟩
        have hyQ : (y : V2) ∈ Q2 := (P0.proper _ hyfull).mp (by
          rw [← hvalue, hz0]
          exact hx0)
        exact ⟨hyQ, by rw [ht]; exact ⟨le_rfl, hlt.le⟩⟩
      · have hz' : z = (⟨((y : V2), beta), hupper y⟩ : F) :=
          Subtype.ext (Prod.ext rfl ht)
        have hvalue : (cut0.parametrization z : W) = P0.map ((y : V2), -delta) :=
          (congrArg (fun w => (cut0.parametrization w : W)) hz').trans (cut0.upper y (hupper y))
        have hyfull : ((y : V2), -delta) ∈ D2 ×ˢ Icc (-P.width) P.width :=
          hfull _ ⟨y.property, by constructor <;> linarith⟩
        have hyQ : (y : V2) ∈ Q2 := (P0.proper _ hyfull).mp (by
          rw [← hvalue, hz0]
          exact hx0)
        exact ⟨hyQ, by rw [ht]; exact ⟨hlt.le, le_rfl⟩⟩
    have hs := hstd ⟨z, hzside⟩
    have hv0 : (cut0.parametrization z : W) = standardMeridianBandMap z :=
      cut0.side ⟨z, hzside⟩ z.property hs
    have harg : (⟨standardMeridianBandMap z, hs⟩ : frontier squareShell) = x :=
      Subtype.ext (hv0.symm.trans hz0)
    exact (cut1.side ⟨z, hzside⟩ z.property hs).trans
      (congrArg (fun y => (e y : W)) harg)
  have hcover : P0.closedStrip ∪ P0.cutCarrier = squareShell :=
    hcover0.trans complementaryRegion_squareMiddleBlock
  exact exists_marked_shell_regluing cut0.ball cut1.ball hcover hcover1
    strip hstrip cut hcut hoverlap hcontact hagree e hstripBoundary hcutBoundary

end PoincareConjecture.M76.HamiltonIndexOne
