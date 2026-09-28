import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Normalization.BoundaryRepairs.Interior.Contacts

set_option autoImplicit false

open Set Metric Geometry Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion

local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "A" => (ℝ × ℝ)

variable {U M ι : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [TopologicalSpace M] {e : ι → OpenPartialHomeomorph M V3}
  {S : SimplicialComplex ℝ U} {f : U → M} {r : M → ℝ} {C : Set M}
  {s t : Stage e S f r C} {step : Step s t}
  {K₀ A₀ : SimplicialComplex ℝ A} {j : A → t.Carrier} {R Fmark : Set M}
  {D : MarkedSurfacePositionData step K₀ A₀ j R Fmark}
  {a b : PLAnnularStrip.squareAnnulus 8 1} {W : Set s.Carrier} {ε : ℝ}
  (N : PlanarAnnulusBoundaryMotion step D.endpoint R Fmark a b W ε)
  (hAnn : D.K.space = PLAnnularStrip.squareAnnulus 8 1)

include hAnn

theorem exists_positive_carrier_chart
    (hW : W ∩ ((fun z : A × A => D.projected z.1) '' D.repairPairs) ⊆ {D.projected a})
    {v : V3} (hv : v ∈ N.source.space) (hvJ : v ∈ interior N.support.space)
    (hvpos : 0 < (N.coordinates v).1.1)
    (hvzero : (N.coordinates v).2 = 0) :
    ∃ H : OpenPartialHomeomorph V3 C3,
      (0 : V3) ∈ H.source ∧ H 0 = 0 ∧
      LocallyPiecewiseAffineOn H.symm H.target ∧
      (∀ z ∈ H.source, z ∈ (fun x : V3 ↦ -v + x) '' N.branchComplex.space ↔
        (H z).1.1 = 0) ∧
      ∀ z ∈ H.source, (N.coordinates z).2 = 0 ↔ (H z).2 = 0 := by
  obtain ⟨x, y, left, right, T, coord, hxl, hyr, hxleft, hyright, hxz, hyz,
    hleq, hreq, hzT, hTzero, hTPL, hleftplane, hrightplane⟩ :=
    N.exists_positive_target_crossing hAnn hW hv hvJ hvpos hvzero
  let p := step.projection ∘ step.inclusion
  let Q := N.chart
  let w := N.window
  let z₀ := Q.symm v
  have hzQ : z₀ ∈ Q.source := Q.map_target (N.support_target (interior_subset hvJ))
  have hQz : Q z₀ = v := Q.right_inv (N.support_target (interior_subset hvJ))
  let V₀ := (w.left.target ∩ w.left.symm ⁻¹' left.source) ∩
    (w.right.target ∩ w.right.symm ⁻¹' right.source)
  have hV₀ : IsOpen V₀ := (w.left.symm.isOpen_inter_preimage left.open_source).inter
    (w.right.symm.isOpen_inter_preimage right.open_source)
  have hzV : z₀ ∈ V₀ := by
    have hl : w.left (D.endpoint x) = z₀ := by rw [congrFun w.left_eq]; exact hxz
    have hr : w.right (D.endpoint y) = z₀ := by rw [congrFun w.right_eq]; exact hyz
    refine ⟨⟨hl ▸ w.left.map_source hxl, ?_⟩,
      ⟨hr ▸ w.right.map_source hyr, ?_⟩⟩
    · change w.left.symm z₀ ∈ left.source
      rw [← hl, w.left.left_inv hxl]
      exact hxleft
    · change w.right.symm z₀ ∈ right.source
      rw [← hr, w.right.left_inv hyr]
      exact hyright
  have same_image (B₀ B₁ : OpenPartialHomeomorph t.Carrier s.Carrier)
      (hB₀ : (B₀ : t.Carrier → s.Carrier) = p)
      (hB₁ : (B₁ : t.Carrier → s.Carrier) = p) (z : s.Carrier)
      (hz : z ∈ B₀.target ∩ B₀.symm ⁻¹' B₁.source) :
      (z ∈ p '' (D.endpoint '' D.K.space ∩ B₀.source) ↔
        z ∈ p '' (D.endpoint '' D.K.space ∩ B₁.source)) := by
    have hp : p (B₀.symm z) = z := by rw [← hB₀]; exact B₀.right_inv hz.1
    have hBz := B₀.map_target hz.1
    constructor
    · rintro ⟨u, ⟨hu, huB⟩, huz⟩
      have heu : u = B₀.symm z := B₀.injOn huB hBz
        (by rw [hB₀]; exact huz.trans hp.symm)
      exact ⟨u, ⟨hu, heu.symm ▸ hz.2⟩, huz⟩
    · rintro ⟨u, ⟨hu, huB⟩, huz⟩
      have heu : u = B₀.symm z := B₁.injOn huB hz.2
        (by rw [hB₁]; exact huz.trans hp.symm)
      exact ⟨u, ⟨hu, heu.symm ▸ hBz⟩, huz⟩
  obtain ⟨i, hzi⟩ := s.cover z₀
  let A₀ := (s.charts i).symm.trans Q
  let B₀ := (s.charts i).symm.trans T
  let F := A₀.symm.trans B₀
  have hF : F ∈ piecewiseAffineGroupoid V3 :=
    (piecewiseAffineGroupoid V3).trans
      ((piecewiseAffineGroupoid V3).symm (N.lower_PL i)) (hTPL i)
  have hvA : v ∈ A₀.target := ⟨N.support_target (interior_subset hvJ), hzi⟩
  have hvB : A₀.symm v ∈ B₀.source := by
    refine ⟨(s.charts i).map_source hzi, ?_⟩
    change (s.charts i).symm ((s.charts i) z₀) ∈ T.source
    rw [(s.charts i).left_inv hzi]
    exact hzT
  have hvF : v ∈ F.source := ⟨hvA, hvB⟩
  have hFvalue (z : V3) (hz : z ∈ F.source) : F z = T (Q.symm z) := by
    change T ((s.charts i).symm ((s.charts i) (Q.symm z))) = T (Q.symm z)
    rw [(s.charts i).left_inv hz.1.2]
  let shift : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-v)
  have hshift : shift v = 0 := by change -v + v = 0; exact neg_add_cancel v
  have hshiftinv : shift.symm 0 = v := by rw [← hshift, shift.symm_apply_apply]
  let Dcoord := coord.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv
  let H₀ := shift.symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (F.trans Dcoord.toHomeomorph.toOpenPartialHomeomorph)
  let O := shift '' ((interior N.support.space ∩ (Q.target ∩ Q.symm ⁻¹' V₀)) ∩
    {u | 0 < (N.coordinates u).1.1})
  have hO : IsOpen O := shift.toHomeomorph.isOpenMap _
    ((isOpen_interior.inter (Q.symm.isOpen_inter_preimage hV₀)).inter
      (isOpen_lt continuous_const (N.coordinates.continuous.fst.fst)))
  let H := H₀.restrOpen O hO
  have hzeroH : (0 : V3) ∈ H.source := by
    refine ⟨⟨mem_univ _, ?_, mem_univ _⟩, ?_⟩
    · change shift.symm 0 ∈ F.source
      rw [hshiftinv]
      exact hvF
    · exact ⟨v, ⟨⟨hvJ, N.support_target (interior_subset hvJ), hzV⟩, hvpos⟩, hshift⟩
  have hHcenter : H 0 = 0 := by
    change Dcoord (F (shift.symm 0)) = 0
    rw [hshiftinv, hFvalue v hvF, hTzero]
    exact map_zero coord
  have hHinv : LocallyPiecewiseAffineOn H.symm H.target := by
    have hfirst := hF.2.comp
      (locallyPiecewiseAffineOn_affine Dcoord.symm.toContinuousAffineMap isOpen_univ)
    have hsecond := (locallyPiecewiseAffineOn_affine
      shift.toContinuousAffineMap isOpen_univ).comp hfirst
    apply hsecond.mono H.open_target
    intro z hz
    exact ⟨⟨mem_univ _, hz.1.1.2⟩, mem_univ _⟩
  have hheight (z : V3) : (N.coordinates (shift z)).2 = (N.coordinates z).2 := by
    change (N.coordinates (-v + z)).2 = (N.coordinates z).2
    rw [map_add, map_neg]
    change -(N.coordinates v).2 + (N.coordinates z).2 = (N.coordinates z).2
    rw [hvzero, neg_zero, zero_add]
  refine ⟨H, hzeroH, hHcenter, hHinv, ?_⟩
  suffices ∀ z ∈ H.source,
      (z ∈ shift '' N.branchComplex.space ↔ (H z).1.1 = 0) ∧
        ((N.coordinates z).2 = 0 ↔ (H z).2 = 0) from
    ⟨fun z hz ↦ (this z hz).1, fun z hz ↦ (this z hz).2⟩
  intro z hz
  let u := shift.symm z
  let y' := Q.symm u
  have huF : u ∈ F.source := hz.1.2.1
  have huJ : u ∈ interior N.support.space := by
    obtain ⟨a, ha, haz⟩ := hz.2
    change shift.symm z ∈ interior N.support.space
    rw [← haz, shift.symm_apply_apply]
    exact ha.1.1
  have hyV : y' ∈ V₀ := by
    obtain ⟨a, ha, haz⟩ := hz.2
    change Q.symm (shift.symm z) ∈ V₀
    rw [← haz, shift.symm_apply_apply]
    exact ha.1.2.2
  have hupos : 0 < (N.coordinates u).1.1 := by
    obtain ⟨a, ha, haz⟩ := hz.2
    change 0 < (N.coordinates (shift.symm z)).1.1
    rw [← haz, shift.symm_apply_apply]
    exact ha.2
  have hyQ : y' ∈ Q.source := Q.map_target (N.support_target (interior_subset huJ))
  have hyT : y' ∈ T.source := by
    have h := huF.2.2
    change (s.charts i).symm ((s.charts i) y') ∈ T.source at h
    rwa [(s.charts i).left_inv huF.1.2] at h
  have hQy : Q y' = u := Q.right_inv (N.support_target (interior_subset huJ))
  have hrightimage : u ∈ N.branchComplex.space ↔
      y' ∈ p '' (D.endpoint '' D.K.space ∩ w.right.source) := by
    rw [N.branch_space, N.source_space, hAnn]
    constructor
    · rintro ⟨⟨q, ⟨hq, hqT⟩, hqu⟩, _⟩
      refine ⟨q, ⟨hq, hqT.1⟩, ?_⟩
      have hqQ : w.right q ∈ Q.source := hqT.2
      rw [congrFun w.right_eq q] at hqQ
      apply Q.injOn hqQ hyQ
      change Q (w.right q) = u at hqu
      rw [congrFun w.right_eq q] at hqu
      exact hqu.trans hQy.symm
    · rintro ⟨q, ⟨hq, hqw⟩, hqy⟩
      refine ⟨⟨q, ⟨hq, hqw, ?_⟩, ?_⟩, interior_subset huJ⟩
      · change w.right q ∈ Q.source
        rw [congrFun w.right_eq q]
        change p q ∈ Q.source
        rw [hqy]
        exact hyQ
      · change Q (w.right q) = u
        rw [congrFun w.right_eq q]
        change Q (p q) = u
        rw [hqy, hQy]
  have hzeroimage : (N.coordinates u).2 = 0 ↔
      y' ∈ p '' (D.endpoint '' D.K.space ∩ w.left.source) := by
    rw [hAnn]
    have h := (N.left_halfplane y' hyQ).symm
    change (0 ≤ (N.coordinates (Q y')).1.1 ∧ (N.coordinates (Q y')).2 = 0) ↔
      y' ∈ p '' (D.endpoint '' PLAnnularStrip.squareAnnulus 8 1 ∩ w.left.source) at h
    simpa only [hQy, hupos.le, true_and] using h
  have hback : z ∈ shift '' N.branchComplex.space ↔ u ∈ N.branchComplex.space := by
    constructor
    · rintro ⟨q, hq, hqz⟩
      change shift.symm z ∈ N.branchComplex.space
      rwa [← hqz, shift.symm_apply_apply]
    · intro h
      exact ⟨u, h, shift.apply_symm_apply z⟩
  have hheightback : (N.coordinates z).2 = (N.coordinates u).2 := by
    have hh := hheight u
    change (N.coordinates (shift (shift.symm z))).2 = (N.coordinates u).2 at hh
    simpa only [shift.apply_symm_apply] using hh
  have hHval : H z = coord (T y') := by
    change Dcoord (F u) = coord (T y')
    rw [hFvalue u huF]
    rfl
  constructor
  · rw [hback, hrightimage, same_image w.right right w.right_eq hreq y' hyV.2,
      hrightplane y' hyT, hHval]
  · rw [hheightback, hzeroimage, same_image w.left left w.left_eq hleq y' hyV.1,
      hleftplane y' hyT, hHval]

end Geometry.OriginalPLTower.PlanarAnnulusBoundaryMotion
