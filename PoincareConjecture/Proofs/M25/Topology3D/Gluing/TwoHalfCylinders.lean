import PoincareConjecture.Proofs.M25.AppA_1_Necks.FiberwiseCylinderModel
import PoincareConjecture.Proofs.M25.Mathlib.PositivePolar
import PoincareConjecture.Proofs.M25.Mathlib.ProductBoundaryTransition
import PoincareConjecture.Proofs.M25.Topology3D.Space3.OrientedCollarCorrection

set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M25.Topology3D

theorem exists_cylinder_model_of_opposite_half_charts
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M]
    (e f : OpenPartialHomeomorph RoundCylinderSpace M)
    (hehalf : univ ×ˢ Ioc (-1 : ℝ) 0 ⊆ e.source)
    (hfhalf : univ ×ˢ Ico (0 : ℝ) 1 ⊆ f.source)
    (he : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ e.symm e.target)
    (hf : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ f f.source)
    (hfi : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ f.symm f.target)
    (hzero : range (fun q : UnitTwoSphere => e (q, 0)) =
      range (fun q : UnitTwoSphere => f (q, 0)))
    (hinter : (e '' (univ ×ˢ Ioc (-1 : ℝ) 0)) ∩
        (f '' (univ ×ˢ Ico (0 : ℝ) 1)) =
      range (fun q : UnitTwoSphere => e (q, 0))) :
    Nonempty (OpenCylinderModel
      ((e '' (univ ×ˢ Ioc (-1 : ℝ) 0)) ∪
        (f '' (univ ×ˢ Ico (0 : ℝ) 1)))) := by
  classical
  let Lh := e '' (univ ×ˢ Ioc (-1 : ℝ) 0)
  let Rh := f '' (univ ×ˢ Ico (0 : ℝ) 1)
  have he0 (q : UnitTwoSphere) : (q, 0) ∈ e.source :=
    hehalf ⟨mem_univ _, by norm_num⟩
  have hf0 (q : UnitTwoSphere) : (q, 0) ∈ f.source :=
    hfhalf ⟨mem_univ _, by norm_num⟩
  have het (q : UnitTwoSphere) : e (q, 0) ∈ f.target := by
    have hq : e (q, 0) ∈ range (fun p : UnitTwoSphere => f (p, 0)) := by
      rw [← hzero]
      exact mem_range_self q
    obtain ⟨p, hp⟩ := hq
    exact hp ▸ f.map_source (hf0 p)
  have hft (q : UnitTwoSphere) : f (q, 0) ∈ e.target := by
    have hq : f (q, 0) ∈ range (fun p : UnitTwoSphere => e (p, 0)) := by
      rw [hzero]
      exact mem_range_self q
    obtain ⟨p, hp⟩ := hq
    exact hp ▸ e.map_source (he0 p)
  let a : UnitTwoSphere → UnitTwoSphere := fun q => (f.symm (e (q, 0))).1
  let b : UnitTwoSphere → UnitTwoSphere := fun q => (e.symm (f (q, 0))).1
  have ha (q : UnitTwoSphere) : f.symm (e (q, 0)) = (a q, 0) := by
    have hq : e (q, 0) ∈ range (fun p : UnitTwoSphere => f (p, 0)) := by
      rw [← hzero]
      exact mem_range_self q
    obtain ⟨p, hp⟩ := hq
    have hp' : f.symm (e (q, 0)) = (p, 0) := by
      rw [← hp]
      exact f.left_inv (hf0 p)
    dsimp only [a]
    rw [hp']
  have hb (q : UnitTwoSphere) : e.symm (f (q, 0)) = (b q, 0) := by
    have hq : f (q, 0) ∈ range (fun p : UnitTwoSphere => e (p, 0)) := by
      rw [hzero]
      exact mem_range_self q
    obtain ⟨p, hp⟩ := hq
    have hp' : e.symm (f (q, 0)) = (p, 0) := by
      rw [← hp]
      exact e.left_inv (he0 p)
    dsimp only [b]
    rw [hp']
  have hfa (q : UnitTwoSphere) : f (a q, 0) = e (q, 0) := by
    rw [← ha]
    exact f.right_inv (het q)
  have heb (q : UnitTwoSphere) : e (b q, 0) = f (q, 0) := by
    rw [← hb]
    exact e.right_inv (hft q)
  have hea : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q : UnitTwoSphere => e (q, 0)) :=
    he.comp_contMDiff (contMDiff_id.prodMk contMDiff_const) he0
  have hfb : ContMDiff (𝓡 2) (𝓡 3) ∞ (fun q : UnitTwoSphere => f (q, 0)) :=
    hf.comp_contMDiff (contMDiff_id.prodMk contMDiff_const) hf0
  let A : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞ :=
    { toFun := a
      invFun := b
      left_inv := fun q => by
        change (e.symm (f (a q, 0))).1 = q
        rw [hfa, e.left_inv (he0 q)]
      right_inv := fun q => by
        change (f.symm (e (b q, 0))).1 = q
        rw [heb, f.left_inv (hf0 q)]
      contMDiff_toFun := contMDiff_fst.comp (hfi.comp_contMDiff hea het)
      contMDiff_invFun := contMDiff_fst.comp (hei.comp_contMDiff hfb hft) }
  have hA0 (q : UnitTwoSphere) : f (A q, 0) = e (q, 0) := hfa q
  let E3 := EuclideanSpace ℝ (Fin 3)
  let : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩
  obtain ⟨q0, hq0⟩ := (NormedSpace.sphere_nonempty (E := E3)).mpr
    (show (0 : ℝ) ≤ 1 by norm_num)
  obtain ⟨Q, hQs, hQt, hQf, hQheight, _, hQ, hQi⟩ :=
    exists_smooth_unitSpherePolar (n := 2) (⟨q0, hq0⟩ : UnitTwoSphere)
  have hQnorm (p : RoundCylinderSpace) (hp : 0 < p.2) : ‖Q p‖ = p.2 := by
    rw [hQf, norm_smul, Real.norm_eq_abs, mem_sphere_zero_iff_norm.mp p.1.property,
      mul_one, abs_of_pos hp]
  have hQunit (q : UnitTwoSphere) : Q.symm q.val = (q, 1) := by
    have hq : Q (q, 1) = q.val := by rw [hQf]; simp
    rw [← hq]
    exact Q.left_inv (by rw [hQs]; exact ⟨mem_univ _, by norm_num⟩)
  have hr : ContDiffOn ℝ ∞ (fun r : ℝ => 1 - r⁻¹) (Ioi 0) :=
    contDiffOn_const.sub (contDiffOn_id.inv (fun _ hr => ne_of_gt hr))
  have hri : ContDiffOn ℝ ∞ (fun t : ℝ => (1 - t)⁻¹) (Iio 1) :=
    (contDiffOn_const.sub contDiffOn_id).inv (fun _ ht => ne_of_gt (sub_pos.mpr ht))
  let l : OpenPartialHomeomorph ℝ ℝ :=
    { toFun := fun r => r - 1
      invFun := fun t => t + 1
      source := Ioi 0
      target := Ioi (-1)
      map_source' := fun x hx => by
        change 0 < x at hx
        change -1 < x - 1
        linarith
      map_target' := fun x hx => by
        change -1 < x at hx
        change 0 < x + 1
        linarith
      left_inv' := fun _ _ => sub_add_cancel _ _
      right_inv' := fun _ _ => add_sub_cancel_right _ _
      open_source := isOpen_Ioi
      open_target := isOpen_Ioi
      continuousOn_toFun := (continuous_id.sub continuous_const).continuousOn
      continuousOn_invFun := (continuous_id.add continuous_const).continuousOn }
  let r : OpenPartialHomeomorph ℝ ℝ :=
    { toFun := fun r => 1 - r⁻¹
      invFun := fun t => (1 - t)⁻¹
      source := Ioi 0
      target := Iio 1
      map_source' := fun x hx => by
        change 0 < x at hx
        change 1 - x⁻¹ < 1
        exact sub_lt_self _ (inv_pos.mpr hx)
      map_target' := fun x hx => by
        change x < 1 at hx
        change 0 < (1 - x)⁻¹
        exact inv_pos.mpr (sub_pos.mpr hx)
      left_inv' := fun x _ => by
        rw [sub_sub_cancel, inv_inv]
      right_inv' := fun x _ => by
        rw [inv_inv, sub_sub_cancel]
      open_source := isOpen_Ioi
      open_target := isOpen_Iio
      continuousOn_toFun := hr.continuousOn
      continuousOn_invFun := hri.continuousOn }
  let PL := (OpenPartialHomeomorph.refl UnitTwoSphere).prod l
  let PR := A.toHomeomorph.toOpenPartialHomeomorph.prod r
  have hPL : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ PL PL.source :=
    (contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const)).contMDiffOn
  have hPLi : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ PL.symm PL.target :=
    (contMDiff_fst.prodMk (contMDiff_snd.add contMDiff_const)).contMDiffOn
  have hPR : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ PR PR.source :=
    (A.contMDiff.comp contMDiff_fst).contMDiffOn.prodMk
      (hr.contMDiffOn.comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2))
  have hPRi : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ PR.symm PR.target :=
    (A.symm.contMDiff.comp contMDiff_fst).contMDiffOn.prodMk
      (hri.contMDiffOn.comp contMDiff_snd.contMDiffOn (fun _ hz => hz.2))
  let EL := Q.symm.trans' PL hQs
  let HR := Q.symm.trans' PR hQs
  have hEL (x : E3) : EL x = ((Q.symm x).1, ‖x‖ - 1) := by
    change ((Q.symm x).1, (Q.symm x).2 - 1) = _
    rw [hQheight]
  have hHR (x : E3) : HR x = (A (Q.symm x).1, 1 - ‖x‖⁻¹) := by
    change (A (Q.symm x).1, 1 - (Q.symm x).2⁻¹) = _
    rw [hQheight]
  have hELsm : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ EL EL.source :=
    hPL.comp hQi (fun x hx => by
      change Q.symm x ∈ univ ×ˢ Ioi 0
      rw [← hQs]
      exact Q.map_target hx)
  have hHRsm : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ HR HR.source :=
    hPR.comp hQi (fun x hx => by
      change Q.symm x ∈ univ ×ˢ Ioi 0
      rw [← hQs]
      exact Q.map_target hx)
  have hELi : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ EL.symm EL.target :=
    hQ.comp_contMDiffOn hPLi
  have hHRi : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ HR.symm HR.target :=
    hQ.comp_contMDiffOn hPRi
  let E := EL.trans e
  let H := HR.trans f
  have hE : ContMDiffOn (𝓡 3) (𝓡 3) ∞ E E.source := he.comp' hELsm
  have hEi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ E.symm E.target := hELi.comp' hei
  have hH : ContMDiffOn (𝓡 3) (𝓡 3) ∞ H H.source := hf.comp' hHRsm
  have hHi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ H.symm H.target := hHRi.comp' hfi
  have hEs (x : E3) : x ∈ E.source ↔ x ≠ 0 ∧ EL x ∈ e.source := by
    change (x ∈ Q.target ∧ EL x ∈ e.source) ↔ _
    rw [hQt]
    rfl
  have hHs (x : E3) : x ∈ H.source ↔ x ≠ 0 ∧ HR x ∈ f.source := by
    change (x ∈ Q.target ∧ HR x ∈ f.source) ↔ _
    rw [hQt]
    rfl
  have hLheight {x : E3} (hx : 0 < ‖x‖) (hx' : ‖x‖ ≤ 1) :
      EL x ∈ univ ×ˢ Ioc (-1 : ℝ) 0 := by
    rw [hEL]
    exact ⟨mem_univ _, by constructor <;> linarith⟩
  have hRheight {x : E3} (hx : 1 ≤ ‖x‖) : HR x ∈ univ ×ˢ Ico (0 : ℝ) 1 := by
    have hpos : 0 < ‖x‖ := zero_lt_one.trans_le hx
    have hi := (inv_le_one₀ hpos).mpr hx
    rw [hHR]
    exact ⟨mem_univ _, by constructor <;> linarith [inv_pos.mpr hpos]⟩
  have hEhalf {x : E3} (hx : 0 < ‖x‖) (hx' : ‖x‖ ≤ 1) : x ∈ E.source :=
    (hEs x).mpr ⟨norm_pos_iff.mp hx, hehalf (hLheight hx hx')⟩
  have hHhalf {x : E3} (hx : 1 ≤ ‖x‖) : x ∈ H.source :=
    (hHs x).mpr ⟨norm_pos_iff.mp (zero_lt_one.trans_le hx), hfhalf (hRheight hx)⟩
  have hEimage : E '' {x : E3 | 0 < ‖x‖ ∧ ‖x‖ ≤ 1} = Lh := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨EL x, hLheight hx.1 hx.2, rfl⟩
    · rintro ⟨⟨q, t⟩, ht, rfl⟩
      have hpos : 0 < t + 1 := by linarith [ht.2.1]
      refine ⟨Q (q, t + 1), ?_, ?_⟩
      · change 0 < ‖Q (q, t + 1)‖ ∧ ‖Q (q, t + 1)‖ ≤ 1
        rw [hQnorm (q, t + 1) hpos]
        exact ⟨hpos, by linarith [ht.2.2]⟩
      · change e (PL (Q.symm (Q (q, t + 1)))) = e (q, t)
        rw [Q.left_inv (by rw [hQs]; exact ⟨mem_univ _, hpos⟩)]
        congr 1
        exact Prod.ext rfl (add_sub_cancel_right t 1)
  have hHimage : H '' {x : E3 | 1 ≤ ‖x‖} = Rh := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨HR x, hRheight hx, rfl⟩
    · rintro ⟨⟨q, t⟩, ht, rfl⟩
      have hpos : 0 < 1 - t := sub_pos.mpr ht.2.2
      refine ⟨Q (A.symm q, (1 - t)⁻¹), ?_, ?_⟩
      · change 1 ≤ ‖Q (A.symm q, (1 - t)⁻¹)‖
        rw [hQnorm (A.symm q, (1 - t)⁻¹) (inv_pos.mpr hpos)]
        exact (one_le_inv₀ hpos).mpr (by linarith [ht.2.1])
      · change f (PR (Q.symm (Q (A.symm q, (1 - t)⁻¹)))) = f (q, t)
        rw [Q.left_inv (by rw [hQs]; exact ⟨mem_univ _, inv_pos.mpr hpos⟩)]
        congr 1
        apply Prod.ext
        · exact A.apply_symm_apply q
        · change 1 - ((1 - t)⁻¹)⁻¹ = t
          rw [inv_inv, sub_sub_cancel]
  have hEunit (q : UnitTwoSphere) : E q.val = e (q, 0) := by
    change e (PL (Q.symm q.val)) = _
    rw [hQunit]
    change e (q, 1 - 1) = _
    rw [sub_self]
  have hHunit (q : UnitTwoSphere) : H q.val = e (q, 0) := by
    change f (PR (Q.symm q.val)) = _
    rw [hQunit]
    change f (A q, 1 - (1 : ℝ)⁻¹) = _
    simpa only [inv_one, sub_self] using hA0 q
  have hEsphere : sphere (0 : E3) 1 ⊆ E.source := by
    intro x hx
    have hn := mem_sphere_zero_iff_norm.mp hx
    exact hEhalf (by rw [hn]; norm_num) (by rw [hn])
  have hHsphere : sphere (0 : E3) 1 ⊆ H.source := by
    intro x hx
    exact hHhalf (by rw [mem_sphere_zero_iff_norm.mp hx])
  let J := H.trans E.symm
  have hJ : ContMDiffOn (𝓡 3) (𝓡 3) ∞ J J.source := hEi.comp' hH
  have hJi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ J.symm J.target := hHi.comp' hE
  have hJsphere : sphere (0 : E3) 1 ⊆ J.source := by
    intro x hx
    refine ⟨hHsphere hx, ?_⟩
    have heq : H x = E x := (hHunit ⟨x, hx⟩).trans (hEunit ⟨x, hx⟩).symm
    change H x ∈ E.target
    rw [heq]
    exact E.map_source (hEsphere hx)
  have hJfixed (x : E3) (hx : x ∈ sphere (0 : E3) 1) : J x = x := by
    change E.symm (H x) = x
    rw [hHunit ⟨x, hx⟩, ← hEunit ⟨x, hx⟩]
    exact E.left_inv (hEsphere hx)
  have hJout (x : E3) (hx : x ∈ J.source) (hn : 1 ≤ ‖x‖) : 1 ≤ ‖J x‖ := by
    by_contra hnot
    have hlt : ‖J x‖ < 1 := lt_of_not_ge hnot
    have hj : J x ∈ E.source := E.map_target hx.2
    have hpos : 0 < ‖J x‖ := norm_pos_iff.mpr ((hEs _).mp hj).1
    have heq : E (J x) = H x := E.right_inv hx.2
    have hl : H x ∈ Lh := by
      rw [← heq, ← hEimage]
      exact ⟨J x, ⟨hpos, hlt.le⟩, rfl⟩
    have hr' : H x ∈ Rh := by rw [← hHimage]; exact ⟨x, hn, rfl⟩
    have hz : H x ∈ range (fun q : UnitTwoSphere => e (q, 0)) := by
      rw [← hinter]
      exact ⟨hl, hr'⟩
    obtain ⟨q, hq⟩ := hz
    have heq' : J x = q.val := E.injOn hj (hEsphere q.property) (by
      rw [heq, hEunit]
      exact hq.symm)
    rw [heq', mem_sphere_zero_iff_norm.mp q.property] at hlt
    exact (lt_irrefl (1 : ℝ)) hlt
  obtain ⟨F, hFfixed, hFnear, hFball, hFclosed, _⟩ :=
    exists_oriented_collar_extension J hJ.contDiffOn hJi.contDiffOn hJsphere hJfixed
      (fun x hx => by
        filter_upwards [J.open_source.mem_nhds (hJsphere hx)] with y hy
        exact hJout y hy)
  obtain ⟨N0, hN0open, hN0sphere, hN0eq⟩ := eventually_nhdsSet_iff_exists.mp hFnear
  let N := N0 ∩ J.source
  let W := F '' N
  have hNopen : IsOpen N := hN0open.inter J.open_source
  have hWopen : IsOpen W := F.toHomeomorph.isOpen_image.mpr hNopen
  have hWsphere : sphere (0 : E3) 1 ⊆ W := by
    intro x hx
    exact ⟨x, ⟨hN0sphere hx, hJsphere hx⟩, hFfixed x hx⟩
  let K0 := F.symm.toHomeomorph.toOpenPartialHomeomorph.trans H
  have hK0 : ContMDiffOn (𝓡 3) (𝓡 3) ∞ K0 K0.source :=
    hH.comp' F.symm.contMDiff.contMDiffOn
  have hK0i : ContMDiffOn (𝓡 3) (𝓡 3) ∞ K0.symm K0.target :=
    F.contMDiff.comp_contMDiffOn (hHi.mono inter_subset_left)
  have hWdata {x : E3} (hx : x ∈ W) :
      x ∈ E.source ∧ x ∈ K0.source ∧ E x = K0 x := by
    obtain ⟨y, hy, rfl⟩ := hx
    have hFJ : F y = J y := hN0eq y hy.1
    have hj : J y ∈ E.source := E.map_target hy.2.2
    refine ⟨by rwa [← hFJ] at hj, ?_, ?_⟩
    · change F y ∈ univ ∧ F.symm (F y) ∈ H.source
      exact ⟨mem_univ _, by rw [F.symm_apply_apply]; exact hy.2.1⟩
    · change E (F y) = H (F.symm (F y))
      rw [F.symm_apply_apply, hFJ]
      exact E.right_inv hy.2.2
  have hFset (s : Set E3) (hs : F '' s = s) (x : E3) : F x ∈ s ↔ x ∈ s := by
    constructor
    · intro hx
      rw [← hs] at hx
      obtain ⟨y, hy, heq⟩ := hx
      exact F.injective heq ▸ hy
    · intro hx
      rw [← hs]
      exact ⟨x, hx, rfl⟩
  have hFiLt (x : E3) : ‖F.symm x‖ < 1 ↔ ‖x‖ < 1 := by
    simpa only [F.apply_symm_apply, mem_ball_zero_iff] using
      (hFset (ball 0 1) hFball (F.symm x)).symm
  have hFiLe (x : E3) : ‖F.symm x‖ ≤ 1 ↔ ‖x‖ ≤ 1 := by
    simpa only [F.apply_symm_apply, mem_closedBall_zero_iff] using
      (hFset (closedBall 0 1) hFclosed (F.symm x)).symm
  have hFiGe (x : E3) : 1 ≤ ‖F.symm x‖ ↔ 1 ≤ ‖x‖ := by
    simpa only [not_lt] using not_congr (hFiLt x)
  have hFiGt (x : E3) : 1 < ‖F.symm x‖ ↔ 1 < ‖x‖ := by
    simpa only [not_le] using not_congr (hFiLe x)
  let V := {x : E3 | 1 < ‖x‖} ∪ W
  have hVopen : IsOpen V := (isOpen_lt continuous_const continuous_norm).union hWopen
  let K := K0.restrOpen V hVopen
  have hK : ContMDiffOn (𝓡 3) (𝓡 3) ∞ K K.source := hK0.mono inter_subset_left
  have hKi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ K.symm K.target :=
    hK0i.mono inter_subset_left
  have hKhalf {x : E3} (hx : 1 ≤ ‖x‖) : x ∈ K.source := by
    refine ⟨⟨mem_univ _, hHhalf ((hFiGe x).mpr hx)⟩, ?_⟩
    by_cases hgt : 1 < ‖x‖
    · exact Or.inl hgt
    · exact Or.inr (hWsphere (mem_sphere_zero_iff_norm.mpr
        (le_antisymm (le_of_not_gt hgt) hx)))
  have hKW {x : E3} (hx : x ∈ W) : x ∈ K.source :=
    ⟨(hWdata hx).2.1, Or.inr hx⟩
  have hKimage : K '' {x : E3 | 1 ≤ ‖x‖} = Rh := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [← hHimage]
      exact ⟨F.symm x, (hFiGe x).mpr hx, rfl⟩
    · intro hp
      rw [← hHimage] at hp
      obtain ⟨y, hy, rfl⟩ := hp
      refine ⟨F y, (hFiGe (F y)).mp (by rwa [F.symm_apply_apply]), ?_⟩
      change H (F.symm (F y)) = H y
      rw [F.symm_apply_apply]
  have hKstrict {x : E3} (hx : 1 < ‖x‖) : K x ∉ Lh := by
    intro hl
    have hr' : K x ∈ Rh := by rw [← hKimage]; exact ⟨x, hx.le, rfl⟩
    have hz : K x ∈ range (fun q : UnitTwoSphere => e (q, 0)) := by
      rw [← hinter]
      exact ⟨hl, hr'⟩
    obtain ⟨q, hq⟩ := hz
    have hgt := (hFiGt x).mpr hx
    have heq : F.symm x = q.val :=
      H.injOn (hHhalf hgt.le) (hHsphere q.property) (by
        rw [hHunit]
        exact hq.symm)
    rw [heq, mem_sphere_zero_iff_norm.mp q.property] at hgt
    exact (lt_irrefl (1 : ℝ)) hgt
  have hEcore : E.IsImage (closedBall 0 1) Lh := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    constructor
    · intro hp
      rw [← hEimage] at hp
      obtain ⟨y, hy, heq⟩ := hp
      exact E.injOn (hEhalf hy.1 hy.2) hx heq ▸ hy.2
    · intro hn
      rw [← hEimage]
      exact ⟨x, ⟨norm_pos_iff.mpr ((hEs x).mp hx).1, hn⟩, rfl⟩
  have hKcore : K.IsImage (closedBall 0 1) Lh := by
    intro x hx
    rw [mem_closedBall_zero_iff]
    constructor
    · intro hp
      by_contra hn
      exact hKstrict (lt_of_not_ge hn) hp
    · intro hn
      have hw : x ∈ W := hx.2.resolve_left (not_lt_of_ge hn)
      change K0 x ∈ Lh
      rw [← (hWdata hw).2.2]
      exact (hEcore (hWdata hw).1).mpr (mem_closedBall_zero_iff.mpr hn)
  have hKsphere : sphere (0 : E3) 1 ⊆ K.source := by
    intro x hx
    exact hKhalf (by rw [mem_sphere_zero_iff_norm.mp hx])
  have hfront : E.source ∩ frontier (closedBall 0 1) =
      K.source ∩ frontier (closedBall 0 1) := by
    rw [frontier_closedBall (0 : E3) one_ne_zero]
    rw [inter_eq_right.mpr hEsphere, inter_eq_right.mpr hKsphere]
  have hfrontEq : EqOn E K (E.source ∩ frontier (closedBall 0 1)) := by
    intro x hx
    have hs : x ∈ sphere (0 : E3) 1 := by
      simpa only [frontier_closedBall (0 : E3) one_ne_zero] using hx.2
    exact (hWdata (hWsphere hs)).2.2
  let Phi := E.piecewise K (closedBall 0 1) Lh hEcore hKcore hfront hfrontEq
  have hPhiL {x : E3} (hx : ‖x‖ ≤ 1) : Phi x = E x :=
    if_pos (mem_closedBall_zero_iff.mpr hx)
  have hPhiR {x : E3} (hx : 1 < ‖x‖) : Phi x = K x :=
    if_neg (fun h => not_le_of_gt hx (mem_closedBall_zero_iff.mp h))
  have hPhiW : EqOn Phi E W := by
    intro x hx
    by_cases hn : ‖x‖ ≤ 1
    · exact hPhiL hn
    · exact (hPhiR (lt_of_not_ge hn)).trans (hWdata hx).2.2.symm
  have hPhiRight {x : E3} (hx : 1 ≤ ‖x‖) : Phi x = K x := by
    by_cases hn : 1 < ‖x‖
    · exact hPhiR hn
    · have hs : x ∈ sphere (0 : E3) 1 :=
        mem_sphere_zero_iff_norm.mpr (le_antisymm (le_of_not_gt hn) hx)
      exact (hPhiW (hWsphere hs)).trans (hWdata (hWsphere hs)).2.2
  have hPhis : Phi.source = ({0} : Set E3)ᶜ := by
    ext x
    change ((x ∈ E.source ∧ x ∈ closedBall 0 1) ∨
      (x ∈ K.source ∧ x ∉ closedBall 0 1)) ↔ x ≠ 0
    constructor
    · rintro (hx | hx)
      · exact ((hEs x).mp hx.1).1
      · have hn : 1 < ‖x‖ := lt_of_not_ge (fun h => hx.2 (mem_closedBall_zero_iff.mpr h))
        exact norm_pos_iff.mp (zero_lt_one.trans hn)
    · intro hx
      by_cases hn : ‖x‖ ≤ 1
      · exact Or.inl ⟨hEhalf (norm_pos_iff.mpr hx) hn, mem_closedBall_zero_iff.mpr hn⟩
      · exact Or.inr ⟨hKhalf (lt_of_not_ge hn).le,
          fun h => hn (mem_closedBall_zero_iff.mp h)⟩
  have hPhit : Phi.target = Lh ∪ Rh := by
    rw [← Phi.image_source_eq_target, hPhis]
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      by_cases hn : ‖x‖ ≤ 1
      · rw [hPhiL hn]
        left
        rw [← hEimage]
        exact ⟨x, ⟨norm_pos_iff.mpr hx, hn⟩, rfl⟩
      · rw [hPhiR (lt_of_not_ge hn)]
        right
        rw [← hKimage]
        exact ⟨x, (lt_of_not_ge hn).le, rfl⟩
    · rintro (hp | hp)
      · rw [← hEimage] at hp
        obtain ⟨x, hx, rfl⟩ := hp
        exact ⟨x, norm_pos_iff.mp hx.1, hPhiL hx.2⟩
      · rw [← hKimage] at hp
        obtain ⟨x, hx, rfl⟩ := hp
        exact ⟨x, norm_pos_iff.mp (zero_lt_one.trans_le hx), hPhiRight hx⟩

  have hlocal (x : E3) (hx : x ∈ Phi.source) :
      ∃ g : OpenPartialHomeomorph E3 M, ∃ O : Set E3,
        IsOpen O ∧ x ∈ O ∧ O ⊆ Phi.source ∧ O ⊆ g.source ∧ EqOn Phi g O ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ g g.source ∧
        ContMDiffOn (𝓡 3) (𝓡 3) ∞ g.symm g.target := by
    by_cases hw : x ∈ W
    · refine ⟨E, W, hWopen, hw, ?_, fun _ hy => (hWdata hy).1, hPhiW, hE, hEi⟩
      intro y hy
      rw [hPhis]
      exact ((hEs y).mp (hWdata hy).1).1
    · by_cases hn : ‖x‖ < 1
      · have hne : x ≠ 0 := by simpa only [hPhis, mem_compl_iff, mem_singleton_iff] using hx
        refine ⟨E, E.source ∩ ball 0 1, E.open_source.inter isOpen_ball,
          ⟨hEhalf (norm_pos_iff.mpr hne) hn.le, mem_ball_zero_iff.mpr hn⟩,
          ?_, inter_subset_left, ?_, hE, hEi⟩
        · intro y hy
          exact Or.inl ⟨hy.1, ball_subset_closedBall hy.2⟩
        · intro y hy
          exact hPhiL (mem_ball_zero_iff.mp hy.2).le
      · have hgt : 1 < ‖x‖ := by
          by_contra hnot
          exact hw (hWsphere (mem_sphere_zero_iff_norm.mpr
            (le_antisymm (le_of_not_gt hnot) (le_of_not_gt hn))))
        refine ⟨K, K.source ∩ (closedBall 0 1)ᶜ,
          K.open_source.inter isClosed_closedBall.isOpen_compl,
          ⟨hKhalf hgt.le, fun h => not_le_of_gt hgt (mem_closedBall_zero_iff.mp h)⟩,
          ?_, inter_subset_left, ?_, hK, hKi⟩
        · intro y hy
          exact Or.inr hy
        · intro y hy
          exact hPhiR (lt_of_not_ge (fun h => hy.2 (mem_closedBall_zero_iff.mpr h)))
  have hPhi : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi Phi.source := by
    intro x hx
    obtain ⟨g, O, hO, hxO, _, hOg, heq, hg, _⟩ := hlocal x hx
    apply ContMDiffAt.contMDiffWithinAt
    apply (hg.contMDiffAt (g.open_source.mem_nhds (hOg hxO))).congr_of_eventuallyEq
    filter_upwards [hO.mem_nhds hxO] with y hy
    exact heq hy
  have hPhii : ContMDiffOn (𝓡 3) (𝓡 3) ∞ Phi.symm Phi.target := by
    intro p hp
    obtain ⟨g, O, hO, hxO, hOP, hOg, heq, _, hgi⟩ :=
      hlocal (Phi.symm p) (Phi.map_target hp)
    have hpO : p ∈ g '' O :=
      ⟨Phi.symm p, hxO, (heq hxO).symm.trans (Phi.right_inv hp)⟩
    have hpt : p ∈ g.target := by
      obtain ⟨x, hx, rfl⟩ := hpO
      exact g.map_source (hOg hx)
    have hOgopen := g.isOpen_image_of_subset_source hO hOg
    apply ContMDiffAt.contMDiffWithinAt
    apply (hgi.contMDiffAt (g.open_target.mem_nhds hpt)).congr_of_eventuallyEq
    filter_upwards [hOgopen.mem_nhds hpO] with y hy
    obtain ⟨z, hz, rfl⟩ := hy
    calc
      Phi.symm (g z) = Phi.symm (Phi z) := congrArg Phi.symm (heq hz).symm
      _ = z := Phi.left_inv (hOP hz)
      _ = g.symm (g z) := (g.left_inv (hOg hz)).symm
  have hmatch : Phi.source = Q.target := hPhis.trans hQt.symm
  let P := Phi.symm.trans' Q.symm hmatch
  have hPs : P.source = Lh ∪ Rh := hPhit
  have hPt : P.target = {z : RoundCylinderSpace | 0 < z.2} := by
    change Q.source = _
    rw [hQs]
    ext z
    simp
  have hP : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ P P.source :=
    hQi.comp hPhii (fun p hp => by rw [← hmatch]; exact Phi.map_target hp)
  have hPi : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ P.symm P.target :=
    hPhi.comp hQ.contMDiffOn (fun z hz => by rw [hmatch]; exact Q.map_source hz)
  obtain ⟨T, _⟩ := OpenCylinderModel.exists_of_fiberwise_partial_chart
    (.forward 0) (fun _ => 0) (fun _ => 1) contMDiff_const contMDiff_const
    (fun _ => by norm_num) P hPs hPt hP hPi
  exact ⟨T⟩

end PoincareConjecture.M25.Topology3D
