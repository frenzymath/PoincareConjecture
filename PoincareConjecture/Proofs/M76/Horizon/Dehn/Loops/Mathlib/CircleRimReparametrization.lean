import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Isotopy.Circle.Reparametrization.Lift
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.RotatedResolutionWords








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

open PoincareConjecture Poincare.Manifold.Schoenflies


theorem exists_real_homeomorph_lift_circle (q : UnitCircle ≃ₜ UnitCircle) :
    ∃ L : ℝ ≃ₜ ℝ, ∀ t, unitCircleExp (L t) = q (unitCircleExp t) := by
  obtain ⟨b, hb⟩ := unitCircleExp_surjective (q (unitCircleExp 0))
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := isCoveringMap_unitCircleExp.existsUnique_continuousMap_lifts
    ⟨fun t => q (unitCircleExp t), q.continuous.comp contMDiff_unitCircleExp.continuous⟩
    0 b hb
  have hLt (t : ℝ) : unitCircleExp (L t) = q (unitCircleExp t) := congrFun hL t
  have hb' : unitCircleExp 0 = q.symm (unitCircleExp (L 0)) := by rw [hLt]; simp
  obtain ⟨K, ⟨hK0, hK⟩, _⟩ := isCoveringMap_unitCircleExp.existsUnique_continuousMap_lifts
    ⟨fun t => q.symm (unitCircleExp t),
      q.symm.continuous.comp contMDiff_unitCircleExp.continuous⟩ (L 0) 0 hb'
  have hKt (t : ℝ) : unitCircleExp (K t) = q.symm (unitCircleExp t) := congrFun hK t
  have hKL : (fun t => K (L t)) = id :=
    isCoveringMap_unitCircleExp.eq_of_comp_eq (K.continuous.comp L.continuous)
      continuous_id (by ext t; simp [hKt, hLt]) 0 hK0
  have hLK : (fun t => L (K t)) = id :=
    isCoveringMap_unitCircleExp.eq_of_comp_eq (L.continuous.comp K.continuous)
      continuous_id (by ext t; simp [hKt, hLt]) (L 0) (by simp [hK0])
  let H : ℝ ≃ₜ ℝ := {
    toFun := L
    invFun := K
    left_inv := congrFun hKL
    right_inv := congrFun hLK
    continuous_toFun := L.continuous
    continuous_invFun := K.continuous }
  exact ⟨H, hLt⟩



theorem real_circle_lift_orientation (q : UnitCircle ≃ₜ UnitCircle)
    (L : ℝ ≃ₜ ℝ) (hL : ∀ t, unitCircleExp (L t) = q (unitCircleExp t)) :
    (∀ t, L (t + 1) = L t + 1) ∨ (∀ t, L (t + 1) = L t - 1) := by
  have hsame (s t : ℝ) (h : unitCircleExp s = unitCircleExp t) :
      unitCircleExp (L s) = unitCircleExp (L t) := by rw [hL, hL, h]
  have hinj (s t : ℝ) (h : unitCircleExp (L s) = unitCircleExp (L t)) :
      unitCircleExp s = unitCircleExp t := by
    rw [hL, hL] at h
    exact q.injective h
  rcases L.continuous.strictMono_of_inj L.injective with hm | hm
  · exact Or.inl (add_one_of_strictMono_circle_lift L.continuous hm
      (fun t => hsame (t + 1) t (unitCircleExp_periodic t)) hinj)
  · have hm' : StrictMono (fun t : ℝ => L (-t)) := fun a b hab => hm (neg_lt_neg hab)
    have hperiod' : ∀ t, unitCircleExp (L (-(t + 1))) = unitCircleExp (L (-t)) := by
      intro t
      apply hsame
      exact unitCircleExp_eq_iff.mpr ⟨-1, by simp; ring⟩
    have hinj' (s t : ℝ) (h : unitCircleExp (L (-s)) = unitCircleExp (L (-t))) :
        unitCircleExp s = unitCircleExp t := by
      obtain ⟨n, hn⟩ := unitCircleExp_eq_iff.mp (hinj (-s) (-t) h)
      exact unitCircleExp_eq_iff.mpr ⟨-n, by push_cast; linarith⟩
    have hp := add_one_of_strictMono_circle_lift (L.continuous.comp continuous_neg)
      hm' hperiod' hinj'
    right
    intro t
    have hh := hp (-(t + 1))
    dsimp only [Function.comp_apply] at hh
    have he : - (-(t + 1) + 1) = t := by ring
    rw [he, neg_neg] at hh
    linarith

variable {X : Type*} [TopologicalSpace X]


theorem whiskeredLoopClass_change_path_mem_iff {b x : X}
    (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p q : Path b x) (a : Path x x) :
    q.whiskeredLoopClass a ∈ J ↔ p.whiskeredLoopClass a ∈ J := by
  have h := Path.whiskeredLoopClass_cycle_mem_iff J p q (Path.refl x) a
  rw [Path.whiskeredLoopClass_congr q (Path.Homotopic.trans_refl a),
    Path.whiskeredLoopClass_congr p (Path.Homotopic.refl_trans a)] at h
  exact h



def realPathCircleLoop {x : ℝ} {n : ℤ} (a : Path x (x + n)) :
    Path (unitCircleExp x) (unitCircleExp x) :=
  (a.map contMDiff_unitCircleExp.continuous).cast rfl (unitCircleExp_add_int x n).symm



theorem realPathCircleLoop_homotopic {x y : ℝ} {n : ℤ}
    (a : Path x (x + n)) (c : Path y (y + n)) :
    (realPathCircleLoop a).Homotopic
      ((((Path.segment x y).map contMDiff_unitCircleExp.continuous).trans
        (realPathCircleLoop c)).trans
          ((Path.segment x y).map contMDiff_unitCircleExp.continuous).symm) := by
  let d := Path.segment x y
  let e := Path.segment (y + (n : ℝ)) (x + n)
  have h := (SimplyConnectedSpace.paths_homotopic a ((d.trans c).trans e)).map
    ⟨unitCircleExp, contMDiff_unitCircleExp.continuous⟩
  have h' := h.pathCast rfl (unitCircleExp_add_int x n).symm
  have he : (e.map contMDiff_unitCircleExp.continuous).cast
      (unitCircleExp_add_int y n).symm (unitCircleExp_add_int x n).symm =
      (d.map contMDiff_unitCircleExp.continuous).symm := by
    apply Path.ext
    funext t
    change unitCircleExp (AffineMap.lineMap (y + (n : ℝ)) (x + n) (t : ℝ)) =
      unitCircleExp (AffineMap.lineMap x y (1 - (t : ℝ)))
    have heq : AffineMap.lineMap (y + (n : ℝ)) (x + n) (t : ℝ) =
        AffineMap.lineMap x y (1 - (t : ℝ)) + n := by
      simp only [AffineMap.lineMap_apply, smul_eq_mul, vsub_eq_sub, vadd_eq_add]
      ring
    rw [heq, unitCircleExp_add_int]
  simpa only [Path.map_trans, Path.cast_trans _ _ rfl
    (unitCircleExp_add_int y n).symm (unitCircleExp_add_int x n).symm,
    Path.cast_trans _ _ rfl rfl (unitCircleExp_add_int y n).symm,
    Path.cast_rfl_rfl, he, realPathCircleLoop] using h'



theorem realPathCircleLoop_mem_iff {x y : ℝ} {n : ℤ}
    (a : Path x (x + n)) (c : Path y (y + n)) (f : C(UnitCircle, X))
    {b : X} (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b (f (unitCircleExp x))) (q : Path b (f (unitCircleExp y))) :
    q.whiskeredLoopClass ((realPathCircleLoop c).map f.continuous) ∈ J ↔
      p.whiskeredLoopClass ((realPathCircleLoop a).map f.continuous) ∈ J := by
  let d := ((Path.segment x y).map contMDiff_unitCircleExp.continuous).map f.continuous
  have h := (realPathCircleLoop_homotopic a c).map f
  simp only [Path.map_trans, ← Path.map_symm] at h
  rw [Path.whiskeredLoopClass_congr p h]
  have he : p.whiskeredLoopClass
      ((d.trans ((realPathCircleLoop c).map f.continuous)).trans d.symm) =
      (p.trans d).whiskeredLoopClass ((realPathCircleLoop c).map f.continuous) := by
    exact inv_injective (basedPathWord_radial p p d d _).symm
  rw [he]
  exact whiskeredLoopClass_change_path_mem_iff J (p.trans d) q _


theorem real_lift_add_int {L : ℝ → ℝ} {e : ℝ}
    (hp : ∀ t, L (t + 1) = L t + e) (t : ℝ) (n : ℤ) :
    L (t + n) = L t + n * e := by
  have hper : Function.Periodic (fun s => L s - s * e) 1 := by
    intro s
    dsimp only
    rw [hp]
    ring
  have h := hper.int_mul n t
  simp only [mul_one] at h
  linarith



theorem exists_realPathCircleLoop {z : UnitCircle} (rho : Path z z) :
    ∃ (x : ℝ) (n : ℤ) (a : Path x (x + n)) (hx : z = unitCircleExp x),
      rho = (realPathCircleLoop a).cast hx hx := by
  obtain ⟨x, hx⟩ := unitCircleExp_surjective z
  obtain ⟨A, hA, hA0⟩ := isCoveringMap_unitCircleExp.exists_path_lifts
    rho.toContinuousMap x (by simpa using hx.symm)
  have hA1 : unitCircleExp (A 1) = unitCircleExp x := by
    have h := congrFun hA 1
    change unitCircleExp (A 1) = rho 1 at h
    simpa only [Path.target, hx] using h
  obtain ⟨n, hn⟩ := unitCircleExp_eq_iff.mp hA1
  let a : Path x (x + n) := {
    toContinuousMap := A
    source' := hA0
    target' := hn }
  refine ⟨x, n, a, hx.symm, ?_⟩
  apply Path.ext
  funext t
  exact (congrFun hA t).symm



theorem circleLoop_homeomorph_mem_iff {z : UnitCircle} (rho : Path z z)
    (h : UnitCircle ≃ₜ UnitCircle) (f : C(UnitCircle, X))
    {b : X} (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b (f z)) (q : Path b (f (h z))) :
    q.whiskeredLoopClass ((rho.map h.continuous).map f.continuous) ∈ J ↔
      p.whiskeredLoopClass (rho.map f.continuous) ∈ J := by
  obtain ⟨L, hL⟩ := exists_real_homeomorph_lift_circle h
  obtain ⟨x, n, a, hx, rfl⟩ := exists_realPathCircleLoop rho
  subst z
  let p' := p
  let q' : Path b (f (unitCircleExp (L x))) := q.cast rfl (congrArg f (hL x))
  rcases real_circle_lift_orientation h L hL with hp | hp
  · have hn : L (x + n) = L x + n := by
      simpa using real_lift_add_int hp x n
    let c : Path (L x) (L x + n) := (a.map L.continuous).cast rfl hn.symm
    have hc : (realPathCircleLoop c).map f.continuous =
        (((realPathCircleLoop a).map h.continuous).map f.continuous).cast
          (congrArg f (hL x)) (congrArg f (hL x)) := by
      apply Path.ext
      funext t
      exact congrArg f (hL (a t))
    have H := realPathCircleLoop_mem_iff a c f J p' q'
    rw [hc] at H
    exact H
  · have hn : L (x + n) = L x + (-n : ℤ) := by
      have hp' : ∀ t, L (t + 1) = L t + (-1 : ℝ) := by intro t; simpa [sub_eq_add_neg] using hp t
      have hh := real_lift_add_int hp' x n
      simpa using hh
    let c : Path (L x) (L x + (-n : ℤ)) := (a.map L.continuous).cast rfl hn.symm
    let ar : Path (x + n) ((x + n) + (-n : ℤ)) := a.symm.cast rfl (by push_cast; ring)
    let pr : Path b (f (unitCircleExp (x + n))) :=
      p.cast rfl (congrArg f (unitCircleExp_add_int x n))
    have hc : (realPathCircleLoop c).map f.continuous =
        (((realPathCircleLoop a).map h.continuous).map f.continuous).cast
          (congrArg f (hL x)) (congrArg f (hL x)) := by
      apply Path.ext
      funext t
      exact congrArg f (hL (a t))
    have ha : (realPathCircleLoop ar).map f.continuous =
        ((realPathCircleLoop a).map f.continuous).symm.cast
          (congrArg f (unitCircleExp_add_int x n))
          (congrArg f (unitCircleExp_add_int x n)) := rfl
    have H := realPathCircleLoop_mem_iff ar c f J pr q'
    rw [hc, ha] at H
    change q.whiskeredLoopClass (((realPathCircleLoop a).map h.continuous).map f.continuous) ∈ J ↔
      p.whiskeredLoopClass ((realPathCircleLoop a).map f.continuous) ∈ J
    have H' : q.whiskeredLoopClass (((realPathCircleLoop a).map h.continuous).map f.continuous) ∈ J ↔
        p.whiskeredLoopClass ((realPathCircleLoop a).map f.continuous).symm ∈ J := H
    have hs : p.whiskeredLoopClass ((realPathCircleLoop a).map f.continuous).symm =
        (p.whiskeredLoopClass ((realPathCircleLoop a).map f.continuous))⁻¹ := by
      have hh := congrArg Inv.inv (basedPathWord_symm p p
        ((realPathCircleLoop a).map f.continuous))
      simpa only [basedPathWord_loop, inv_inv] using hh
    simpa only [hs, J.inv_mem_iff] using H'



theorem circleLikeLoop_homeomorph_mem_iff
    {C : Type*} [TopologicalSpace C] (e : C ≃ₜ UnitCircle)
    {z : C} (rho : Path z z) (h : C ≃ₜ C) (f : C(C, X))
    {b : X} (J : Subgroup (FundamentalGroup X b)) [J.Normal]
    (p : Path b (f z)) (q : Path b (f (h z))) :
    q.whiskeredLoopClass ((rho.map h.continuous).map f.continuous) ∈ J ↔
      p.whiskeredLoopClass (rho.map f.continuous) ∈ J := by
  let k := e.symm.trans (h.trans e)
  let g : C(UnitCircle, X) := f.comp ⟨e.symm, e.symm.continuous⟩
  have hp : g (e z) = f z := by simp [g]
  have hq : g (k (e z)) = f (h z) := by simp [g, k]
  have H := circleLoop_homeomorph_mem_iff (rho.map e.continuous) k g J
    (p.cast rfl hp) (q.cast rfl hq)
  have h0 : (rho.map e.continuous).map g.continuous =
      (rho.map f.continuous).cast hp hp := by
    apply Path.ext
    funext t
    change f (e.symm (e (rho t))) = f (rho t)
    rw [e.symm_apply_apply]
  have h1 : (((rho.map e.continuous).map k.continuous).map g.continuous) =
      ((rho.map h.continuous).map f.continuous).cast hq hq := by
    apply Path.ext
    funext t
    change f (e.symm (e (h (e.symm (e (rho t)))))) = f (h (rho t))
    simp only [e.symm_apply_apply]
  rw [h0, h1] at H
  exact H

end PoincareConjecture.M76.Dehn
