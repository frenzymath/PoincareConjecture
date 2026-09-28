import PoincareConjecture.Proofs.M76.Horizon.Dehn.General.OriginalGeneralPositionData
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryOldGerms
import PoincareConjecture.Proofs.M76.Dehn.OriginalDoubleArcSurgeryStep
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLInitialSegment
import PoincareConjecture.Proofs.M76.Mathlib.RadialSegmentGerms
import PoincareConjecture.Proofs.M76.Mathlib.CentralLinkSigns

set_option autoImplicit false

open Set Metric Geometry Geometry.SimplicialComplex Topology
open PoincareConjecture.M76.Dehn

namespace Geometry.OriginalPLTower

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "D" => closedBall (0 : V2) 1

variable {M ι : Type*} [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ V2}
  {f : V2 → M} {r : M → ℝ} {C : Set M}

set_option maxHeartbeats 1600000 in
theorem OriginalGeneralPositionData.boundary_interior_old_chart
    {s t : Stage e S f r C} (step : Step s t) {R Fmark : Set M}
    {base : Fmark} {Jgroup : Subgroup (FundamentalGroup Fmark base)}
    {old : StageMarkedDisk t R Fmark base Jgroup}
    (data : OriginalGeneralPositionData step old)
    (a : D) (w : TwoBranchWindow (step.projection ∘ step.inclusion))
    (c : V3 ≃L[ℝ] C3) (Q : OpenPartialHomeomorph s.Carrier V3)
    (J K : SimplicialComplex ℝ V3)
    (hJQ : J.space ⊆ Q.target)
    (hQPL : ∀ k, (s.charts k).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hQzero : Q (step.projection (step.inclusion (data.initial.map a))) = 0)
    (hKs : K.space = (w.right.trans Q) ''
      (data.initial.map '' D ∩ (w.right.trans Q).source) ∩ J.space)
    (hplane : ∀ y ∈ Q.source,
      y ∈ (step.projection ∘ step.inclusion) '' (data.initial.map '' D ∩ w.left.source) ↔
        0 ≤ (c (Q y)).1.1 ∧ (c (Q y)).2 = 0)
    (hbad : ∀ y ∈ Q.source,
      y ∈ (fun z : V2 × V2 =>
        step.projection (step.inclusion (data.initial.map z.1))) '' data.exceptional →
      y = step.projection (step.inclusion (data.initial.map a)))
    (v : V3) (hvK : v ∈ K.space) (hvJ : v ∈ interior J.space)
    (hvpositive : 0 < (c v).1.1) (hvzero : (c v).2 = 0) :
    ∃ T : OpenPartialHomeomorph V3 C3,
      (0 : V3) ∈ T.source ∧ T 0 = 0 ∧ LocallyPiecewiseAffineOn T.symm T.target ∧
      (∀ z ∈ T.source, z ∈ (fun x : V3 => -v + x) '' K.space ↔ (T z).1.1 = 0) ∧
      ∀ z ∈ T.source, (c z).2 = 0 ↔ (T z).2 = 0 := by
  classical
  let initial := data.initial
  let p := step.projection ∘ step.inclusion
  let lower := p ∘ initial.map
  let bad := (fun z : V2 × V2 => lower z.1) '' data.exceptional
  have hv0 : v ≠ 0 := by
    intro heq
    simp [heq] at hvpositive
  let y := Q.symm v
  have hyQ : y ∈ Q.source := Q.map_target (hJQ (interior_subset hvJ))
  have hQy : Q y = v := Q.right_inv (hJQ (interior_subset hvJ))
  obtain ⟨xr, ⟨⟨ur, hur, hru⟩, hxr⟩, hrv⟩ := (hKs.subset hvK).1
  have hyr : p xr = y := by
    have hxrQ : w.right xr ∈ Q.source := hxr.2
    rw [congrFun w.right_eq xr] at hxrQ
    apply Q.injOn hxrQ hyQ
    change Q (w.right xr) = v at hrv
    rw [congrFun w.right_eq xr] at hrv
    exact hrv.trans hQy.symm
  have hleft : y ∈ p '' (initial.map '' D ∩ w.left.source) :=
    (hplane y hyQ).mpr (by rw [hQy]; exact ⟨hvpositive.le, hvzero⟩)
  obtain ⟨xl, ⟨⟨ul, hul, hlu⟩, hxl⟩, hly⟩ := hleft
  let al : D := ⟨ul, hul⟩
  let ar : D := ⟨ur, hur⟩
  have hlar : al ≠ ar := by
    intro heq
    have he : xl = xr :=
      hlu.symm.trans ((congrArg initial.map (congrArg Subtype.val heq)).trans hru)
    exact w.disjoint.ne_of_mem hxl hxr.1 he
  have hlower : lower al = y := (congrArg p hlu).trans hly
  have hupper : lower ar = y := (congrArg p hru).trans hyr
  have hnotE : ((al : V2), (ar : V2)) ∉ data.exceptional := by
    intro hmem
    have hybad : y ∈ bad := ⟨((al : V2), (ar : V2)), hmem, hlower⟩
    have hycenter : y = lower a := hbad y hyQ hybad
    exact hv0 (hQy.symm.trans ((congrArg Q hycenter).trans hQzero))
  obtain ⟨a', b', w', c', T, horder, ha', hb', hyT, _hTinside, hTzero,
    hTPL, _hTbranches, _hTwhole, hTleft, hTright⟩ :=
    data.crossings al ar hlar (hlower.trans hupper.symm) hnotE Q.source Q.open_source
      (by change lower al ∈ Q.source; rw [hlower]; exact hyQ)
  have hyT' : y ∈ T.source := by
    change lower al ∈ T.source at hyT
    exact hlower ▸ hyT
  have hTy : T y = 0 := by
    change T (lower al) = 0 at hTzero
    simpa only [hlower] using hTzero
  obtain ⟨left, right, coord, hleftpoint, hrightpoint, hleq, hreq,
    hleftplane, hrightplane⟩ :
      ∃ (left right : OpenPartialHomeomorph t.Carrier s.Carrier)
        (coord : V3 ≃L[ℝ] C3),
        xl ∈ left.source ∧ xr ∈ right.source ∧
        (left : t.Carrier → s.Carrier) = p ∧
        (right : t.Carrier → s.Carrier) = p ∧
        (∀ x ∈ T.source, x ∈ p '' (initial.map '' D ∩ left.source) ↔
          (coord (T x)).2 = 0) ∧
        ∀ x ∈ T.source, x ∈ p '' (initial.map '' D ∩ right.source) ↔
          (coord (T x)).1.1 = 0 := by
    rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨w'.left, w'.right, c', hlu ▸ ha', hru ▸ hb',
        w'.left_eq, w'.right_eq, hTleft, hTright⟩
    · let perm : C3 ≃ₗ[ℝ] C3 :=
        { toFun := fun z => ((z.2, z.1.2), z.1.1)
          invFun := fun z => ((z.2, z.1.2), z.1.1)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      exact ⟨w'.right, w'.left, c'.trans perm.toContinuousLinearEquiv,
        hlu ▸ hb', hru ▸ ha', w'.right_eq, w'.left_eq, hTright, hTleft⟩
  let V₀ := (w.left.target ∩ w.left.symm ⁻¹' left.source) ∩
    (w.right.target ∩ w.right.symm ⁻¹' right.source)
  have hV₀ : IsOpen V₀ := (w.left.symm.isOpen_inter_preimage left.open_source).inter
    (w.right.symm.isOpen_inter_preimage right.open_source)
  have hyV₀ : y ∈ V₀ := by
    have hly' : w.left xl = y := by rw [congrFun w.left_eq xl]; exact hly
    have hry' : w.right xr = y := by rw [congrFun w.right_eq xr]; exact hyr
    refine ⟨⟨hly' ▸ w.left.map_source hxl, ?_⟩,
      ⟨hry' ▸ w.right.map_source hxr.1, ?_⟩⟩
    · change w.left.symm y ∈ left.source
      rw [← hly', w.left.left_inv hxl]
      exact hleftpoint
    · change w.right.symm y ∈ right.source
      rw [← hry', w.right.left_inv hxr.1]
      exact hrightpoint
  let V := V₀ ∩ (Q.source ∩ Q ⁻¹' {x | 0 < (c x).1.1})
  have hpositiveOpen : IsOpen {x : V3 | 0 < (c x).1.1} :=
    isOpen_lt continuous_const (c.continuous.fst.fst)
  have hV : IsOpen V := hV₀.inter (Q.isOpen_inter_preimage hpositiveOpen)
  have hyV : y ∈ V := ⟨hyV₀, hyQ, by
    change 0 < (c (Q y)).1.1
    rw [hQy]
    exact hvpositive⟩
  have same_image (A B : OpenPartialHomeomorph t.Carrier s.Carrier)
      (hA : (A : t.Carrier → s.Carrier) = p)
      (hB : (B : t.Carrier → s.Carrier) = p) (x : s.Carrier)
      (hx : x ∈ A.target ∩ A.symm ⁻¹' B.source) :
      (x ∈ p '' (initial.map '' D ∩ A.source) ↔
        x ∈ p '' (initial.map '' D ∩ B.source)) := by
    have hp : p (A.symm x) = x := by rw [← hA]; exact A.right_inv hx.1
    have hAx := A.map_target hx.1
    constructor
    · rintro ⟨u, ⟨hu, huA⟩, hux⟩
      have heu : u = A.symm x := A.injOn huA hAx (by rw [hA]; exact hux.trans hp.symm)
      exact ⟨u, ⟨hu, heu.symm ▸ hx.2⟩, hux⟩
    · rintro ⟨u, ⟨hu, huB⟩, hux⟩
      have heu : u = A.symm x := B.injOn huB hx.2 (by rw [hB]; exact hux.trans hp.symm)
      exact ⟨u, ⟨hu, heu.symm ▸ hAx⟩, hux⟩
  obtain ⟨i, hyi⟩ := s.cover y
  let A := (s.charts i).symm.trans Q
  let B := (s.charts i).symm.trans T
  let F := A.symm.trans B
  have hF : F ∈ piecewiseAffineGroupoid V3 :=
    (piecewiseAffineGroupoid V3).trans ((piecewiseAffineGroupoid V3).symm (hQPL i)) (hTPL i)
  have hviA : v ∈ A.target := ⟨hJQ (interior_subset hvJ), hyi⟩
  have hviB : A.symm v ∈ B.source := by
    refine ⟨(s.charts i).map_source hyi, ?_⟩
    change (s.charts i).symm ((s.charts i) y) ∈ T.source
    rw [(s.charts i).left_inv hyi]
    exact hyT'
  have hvF : v ∈ F.source := ⟨hviA, hviB⟩
  have hFvalue (z : V3) (hz : z ∈ F.source) : F z = T (Q.symm z) := by
    change T ((s.charts i).symm ((s.charts i) (Q.symm z))) = T (Q.symm z)
    rw [(s.charts i).left_inv hz.1.2]
  let shift : V3 ≃ᴬ[ℝ] V3 := ContinuousAffineEquiv.constVAdd ℝ V3 (-v)
  have hshift : shift v = 0 := by change -v + v = 0; exact neg_add_cancel v
  have hshiftinv : shift.symm 0 = v := by rw [← hshift, shift.symm_apply_apply]
  let Dcoord := coord.toLinearEquiv.toAffineEquiv.toContinuousAffineEquiv
  let H₀ := shift.symm.toHomeomorph.toOpenPartialHomeomorph.trans
    (F.trans Dcoord.toHomeomorph.toOpenPartialHomeomorph)
  let O := shift '' (interior J.space ∩ (Q.target ∩ Q.symm ⁻¹' V))
  have hO : IsOpen O := shift.toHomeomorph.isOpenMap _
    (isOpen_interior.inter (Q.symm.isOpen_inter_preimage hV))
  let H := H₀.restrOpen O hO
  have hzeroH : (0 : V3) ∈ H.source := by
    refine ⟨⟨mem_univ _, ?_, mem_univ _⟩, ?_⟩
    · change shift.symm 0 ∈ F.source
      rw [hshiftinv]
      exact hvF
    · exact ⟨v, ⟨hvJ, hJQ (interior_subset hvJ), hyV⟩, hshift⟩
  have hHcenter : H 0 = 0 := by
    change Dcoord (F (shift.symm 0)) = 0
    rw [hshiftinv, hFvalue v hvF, hTy]
    exact map_zero coord
  have hHinv : LocallyPiecewiseAffineOn H.symm H.target := by
    have hfirst := hF.2.comp
      (locallyPiecewiseAffineOn_affine Dcoord.symm.toContinuousAffineMap isOpen_univ)
    have hsecond := (locallyPiecewiseAffineOn_affine
      shift.toContinuousAffineMap isOpen_univ).comp hfirst
    apply hsecond.mono H.open_target
    intro z hz
    exact ⟨⟨mem_univ _, hz.1.1.2⟩, mem_univ _⟩
  have hshiftK := K.affineOnFaces_affine shift.toContinuousAffineMap
  let Kshift := hshiftK.embeddedImage shift.injective.injOn
  have hKshifts : Kshift.space = shift '' K.space :=
    hshiftK.embeddedImage_space shift.injective.injOn
  let height : V3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℝ).comp c.toContinuousLinearMap
  have hheight (z : V3) : height (shift z) = (c z).2 := by
    change (c (-v + z)).2 = (c z).2
    rw [map_add, map_neg]
    change -(c v).2 + (c z).2 = (c z).2
    rw [hvzero, neg_zero, zero_add]
  have hparts (z : V3) (hz : z ∈ H.source) :
      (z ∈ Kshift.space ↔ (H z).1.1 = 0) ∧
        (height z = 0 ↔ (H z).2 = 0) := by
    let x := shift.symm z
    let y' := Q.symm x
    have hxF : x ∈ F.source := hz.1.2.1
    have hxJ : x ∈ interior J.space := by
      obtain ⟨a, ha, haz⟩ := hz.2
      change shift.symm z ∈ interior J.space
      rw [← haz, shift.symm_apply_apply]
      exact ha.1
    have hy'V : y' ∈ V := by
      obtain ⟨a, ha, haz⟩ := hz.2
      change Q.symm (shift.symm z) ∈ V
      rw [← haz, shift.symm_apply_apply]
      exact ha.2.2
    have hy'Q : y' ∈ Q.source := Q.map_target (hJQ (interior_subset hxJ))
    have hy'T : y' ∈ T.source := by
      have h := hxF.2.2
      change (s.charts i).symm ((s.charts i) y') ∈ T.source at h
      rwa [(s.charts i).left_inv hxF.1.2] at h
    have hQy' : Q y' = x := Q.right_inv (hJQ (interior_subset hxJ))
    have hrightimage : x ∈ K.space ↔
        y' ∈ p '' (initial.map '' D ∩ w.right.source) := by
      rw [hKs]
      constructor
      · rintro ⟨⟨u, ⟨hu, huT⟩, hux⟩, _⟩
        refine ⟨u, ⟨hu, huT.1⟩, ?_⟩
        have huQ : w.right u ∈ Q.source := huT.2
        rw [congrFun w.right_eq u] at huQ
        apply Q.injOn huQ hy'Q
        change Q (w.right u) = x at hux
        rw [congrFun w.right_eq u] at hux
        exact hux.trans hQy'.symm
      · rintro ⟨u, ⟨hu, huw⟩, huy⟩
        refine ⟨⟨u, ⟨hu, huw, ?_⟩, ?_⟩, interior_subset hxJ⟩
        · change w.right u ∈ Q.source
          rw [congrFun w.right_eq u]
          change p u ∈ Q.source
          rw [huy]
          exact hy'Q
        · change Q (w.right u) = x
          rw [congrFun w.right_eq u]
          change Q (p u) = x
          rw [huy, hQy']
    have hxpositive : 0 < (c x).1.1 := by
      have hh := hy'V.2.2
      change 0 < (c (Q y')).1.1 at hh
      rwa [hQy'] at hh
    have hzeroimage : (c x).2 = 0 ↔
        y' ∈ p '' (initial.map '' D ∩ w.left.source) := by
      simpa only [hQy', and_iff_right hxpositive.le] using (hplane y' hy'Q).symm
    have hback : z ∈ Kshift.space ↔ x ∈ K.space := by
      rw [hKshifts]
      constructor
      · rintro ⟨u, hu, huz⟩
        change shift.symm z ∈ K.space
        rwa [← huz, shift.symm_apply_apply]
      · intro h
        exact ⟨x, h, shift.apply_symm_apply z⟩
    have hheightback : height z = (c x).2 := by
      have hh := hheight x
      change height (shift (shift.symm z)) = (c x).2 at hh
      simpa only [shift.apply_symm_apply] using hh
    have hHval : H z = coord (T y') := by
      change Dcoord (F x) = coord (T y')
      rw [hFvalue x hxF]
      rfl
    constructor
    · rw [hback, hrightimage, same_image w.right right w.right_eq hreq y' hy'V.1.2,
        hrightplane y' hy'T, hHval]
    · rw [hheightback, hzeroimage, same_image w.left left w.left_eq hleq y' hy'V.1.1,
        hleftplane y' hy'T, hHval]
  refine ⟨H, hzeroH, hHcenter, hHinv, ?_, fun z hz => (hparts z hz).2⟩
  intro z hz
  change z ∈ shift '' K.space ↔ (H z).1.1 = 0
  rw [← hKshifts]
  exact (hparts z hz).1

end Geometry.OriginalPLTower
