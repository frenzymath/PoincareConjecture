import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.ResolutionEndHomotopies

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "C3" => ((ℝ × ℝ) × ℝ)

structure MarkedResolutionOldEndData {X : Type*} [TopologicalSpace X]
    {Fmark : Set X} {τ : C3 → X} {b : ℝ} {t : unitInterval}
    (d : MarkedResolutionEndData Fmark τ b t) where
  AR : Path d.a d.r
  CL : Path d.c d.l
  AR_val : ∀ s : unitInterval, (AR s : X) =
    τ ((-1 + 2 * (s : ℝ), 1 - 2 * (s : ℝ)), (t : ℝ))
  CL_val : ∀ s : unitInterval, (CL s : X) =
    τ ((1 - 2 * (s : ℝ), 1 - 2 * (s : ℝ)), (t : ℝ))
  AR_homotopic : AR.Homotopic (d.ra.symm.trans d.rr)
  CL_homotopic : CL.Homotopic (d.rc.symm.trans d.rl)

theorem nonempty_marked_resolution_old_end_data
    {X : Type*} [TopologicalSpace X] {Fmark : Set X} (τ : C3 → X)
    (hτ : ContinuousOn τ tube)
    (hτmark : ∀ z ∈ tube, z.2 = 0 ∨ z.2 = 1 → τ z ∈ Fmark)
    {b : ℝ} (t : unitInterval) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1)
    (d : MarkedResolutionEndData Fmark τ b t) :
    Nonempty (MarkedResolutionOldEndData d) := by
  have hconv : Convex ℝ (endSquare (t : ℝ)) :=
    ((convex_Icc (-1 : ℝ) 1).prod (convex_Icc (-1 : ℝ) 1)).prod
      (convex_singleton (t : ℝ))
  have htube (x : endSquare (t : ℝ)) : (x : C3) ∈ tube := by
    refine ⟨x.property.1, ?_⟩
    have hx : (x : C3).2 = (t : ℝ) := x.property.2
    rw [hx]
    exact t.property
  let f : C(endSquare (t : ℝ), Fmark) :=
    { toFun := fun x ↦ ⟨τ x, hτmark x (htube x) (by
        have hx : (x : C3).2 = (t : ℝ) := x.property.2
        rwa [hx])⟩
      continuous_toFun :=
        (hτ.comp_continuous continuous_subtype_val htube).subtype_mk _ }
  let a : endSquare (t : ℝ) := ⟨((-1, 1), (t : ℝ)), by norm_num [endSquare]⟩
  let c : endSquare (t : ℝ) := ⟨((1, 1), (t : ℝ)), by norm_num [endSquare]⟩
  let l : endSquare (t : ℝ) := ⟨((-1, -1), (t : ℝ)), by norm_num [endSquare]⟩
  let r : endSquare (t : ℝ) := ⟨((1, -1), (t : ℝ)), by norm_num [endSquare]⟩
  let seg (x y : endSquare (t : ℝ)) : Path x y :=
    Path.segmentIn (endSquare (t : ℝ)) x y
      (hconv.segment_subset x.property y.property)
  have hz : d.z = f (endCenter t) := Subtype.ext d.z_val
  have ha : d.a = f a := Subtype.ext d.a_val
  have hc : d.c = f c := Subtype.ext d.c_val
  have hl : d.l = f l := Subtype.ext d.l_val
  have hr : d.r = f r := Subtype.ext d.r_val
  have hdiag (x y : endSquare (t : ℝ)) {u v : Fmark}
      (hu : u = f x) (hv : v = f y)
      (rx : Path d.z u) (ry : Path d.z v)
      (hrx : ∀ s : unitInterval, (rx s : X) =
        τ (AffineMap.lineMap ((0, 0), (t : ℝ)) (x : C3) (s : ℝ)))
      (hry : ∀ s : unitInterval, (ry s : X) =
        τ (AffineMap.lineMap ((0, 0), (t : ℝ)) (y : C3) (s : ℝ))) :
      (((seg x y).map f.continuous).cast hu hv).Homotopic (rx.symm.trans ry) := by
    have h := (Path.homotopic_of_convex_range hconv Subset.rfl (seg x y)
      ((seg (endCenter t) x).symm.trans (seg (endCenter t) y))
      (fun s ↦ ((seg x y) s).property)
      (fun s ↦ (((seg (endCenter t) x).symm.trans (seg (endCenter t) y)) s).property)).map f
    have hx : ((seg (endCenter t) x).map f.continuous).cast hz hu = rx := by
      apply Path.ext
      funext s
      exact Subtype.ext (hrx s).symm
    have hy : ((seg (endCenter t) y).map f.continuous).cast hz hv = ry := by
      apply Path.ext
      funext s
      exact Subtype.ext (hry s).symm
    have H := h.pathCast hu hv
    simpa only [Path.map_trans, ← Path.map_symm, Path.cast_trans _ _ hu hz hv,
      Path.cast_symm, hx, hy] using H
  let AR := ((seg a r).map f.continuous).cast ha hr
  let CL := ((seg c l).map f.continuous).cast hc hl
  refine ⟨{
    AR := AR
    CL := CL
    AR_val := ?_
    CL_val := ?_
    AR_homotopic := hdiag a r ha hr d.ra d.rr d.ra_val d.rr_val
    CL_homotopic := hdiag c l hc hl d.rc d.rl d.rc_val d.rl_val }⟩
  · intro s
    change τ (AffineMap.lineMap ((-1, 1), (t : ℝ)) ((1, -1), (t : ℝ)) (s : ℝ)) = _
    congr 1
    ext <;> simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul] <;> ring
  · intro s
    change τ (AffineMap.lineMap ((1, 1), (t : ℝ)) ((-1, -1), (t : ℝ)) (s : ℝ)) = _
    congr 1
    ext <;> simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul] <;> ring

theorem old_resolution_end_word_case_a
    {X : Type*} [TopologicalSpace X] {Fmark : Set X} {τ : C3 → X} {b : ℝ}
    (E0 : MarkedResolutionEndData Fmark τ b 0)
    (E1 : MarkedResolutionEndData Fmark τ b 1)
    (D0 : MarkedResolutionOldEndData E0) (D1 : MarkedResolutionOldEndData E1)
    (base : Fmark) (p : Path base E0.z) (q : Path base E1.z)
    (a : Path E0.a E1.a) (β : Path E1.r E1.l)
    (c : Path E1.c E0.c) (d : Path E0.l E0.r) :
    let A := basedPathWord (p.trans E0.ra) (q.trans E1.ra) a
    let B := basedPathWord (q.trans E1.rr) (q.trans E1.rl) β
    let C := basedPathWord (q.trans E1.rc) (p.trans E0.rc) c
    let D := basedPathWord (p.trans E0.rl) (p.trans E0.rr) d
    basedPathWord (p.trans E0.ra) (p.trans E0.ra)
      (((((((a.trans D1.AR).trans β).trans D1.CL.symm).trans c).trans D0.CL).trans d).trans
        D0.AR.symm) = A * B * C * D := by
  dsimp only
  have har0 := basedPathWord_end_path p E0.ra E0.rr D0.AR D0.AR_homotopic
  have hcl0 := basedPathWord_end_path p E0.rc E0.rl D0.CL D0.CL_homotopic
  have har1 := basedPathWord_end_path q E1.ra E1.rr D1.AR D1.AR_homotopic
  have hcl1 := basedPathWord_end_path q E1.rc E1.rl D1.CL D1.CL_homotopic
  rw [basedPathWord_trans (p.trans E0.ra) (p.trans E0.rr) (p.trans E0.ra),
    basedPathWord_trans (p.trans E0.ra) (p.trans E0.rl) (p.trans E0.rr),
    basedPathWord_trans (p.trans E0.ra) (p.trans E0.rc) (p.trans E0.rl),
    basedPathWord_trans (p.trans E0.ra) (q.trans E1.rc) (p.trans E0.rc),
    basedPathWord_trans (p.trans E0.ra) (q.trans E1.rl) (q.trans E1.rc),
    basedPathWord_trans (p.trans E0.ra) (q.trans E1.rr) (q.trans E1.rl),
    basedPathWord_trans (p.trans E0.ra) (q.trans E1.ra) (q.trans E1.rr)]
  simp only [basedPathWord_symm, har0, hcl0, har1, hcl1, inv_one, mul_one]

theorem old_resolution_end_word_case_b
    {X : Type*} [TopologicalSpace X] {Fmark : Set X} {τ : C3 → X} {b : ℝ}
    (E0 : MarkedResolutionEndData Fmark τ b 0)
    (E1 : MarkedResolutionEndData Fmark τ b 1)
    (D0 : MarkedResolutionOldEndData E0) (D1 : MarkedResolutionOldEndData E1)
    (base : Fmark) (p : Path base E0.z) (q : Path base E1.z)
    (a : Path E1.a E0.a) (β : Path E0.r E1.l)
    (c : Path E1.c E0.c) (d : Path E0.l E1.r) :
    let A := basedPathWord (q.trans E1.ra) (p.trans E0.ra) a
    let B := basedPathWord (p.trans E0.rr) (q.trans E1.rl) β
    let C := basedPathWord (q.trans E1.rc) (p.trans E0.rc) c
    let D := basedPathWord (p.trans E0.rl) (q.trans E1.rr) d
    basedPathWord (q.trans E1.ra) (q.trans E1.ra)
      (((((((a.trans D0.AR).trans β).trans D1.CL.symm).trans c).trans D0.CL).trans d).trans
        D1.AR.symm) = A * B * C * D := by
  dsimp only
  have har0 := basedPathWord_end_path p E0.ra E0.rr D0.AR D0.AR_homotopic
  have hcl0 := basedPathWord_end_path p E0.rc E0.rl D0.CL D0.CL_homotopic
  have har1 := basedPathWord_end_path q E1.ra E1.rr D1.AR D1.AR_homotopic
  have hcl1 := basedPathWord_end_path q E1.rc E1.rl D1.CL D1.CL_homotopic
  rw [basedPathWord_trans (q.trans E1.ra) (q.trans E1.rr) (q.trans E1.ra),
    basedPathWord_trans (q.trans E1.ra) (p.trans E0.rl) (q.trans E1.rr),
    basedPathWord_trans (q.trans E1.ra) (p.trans E0.rc) (p.trans E0.rl),
    basedPathWord_trans (q.trans E1.ra) (q.trans E1.rc) (p.trans E0.rc),
    basedPathWord_trans (q.trans E1.ra) (q.trans E1.rl) (q.trans E1.rc),
    basedPathWord_trans (q.trans E1.ra) (p.trans E0.rr) (q.trans E1.rl),
    basedPathWord_trans (q.trans E1.ra) (p.trans E0.ra) (p.trans E0.rr)]
  simp only [basedPathWord_symm, har0, hcl0, har1, hcl1, inv_one, mul_one]

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
