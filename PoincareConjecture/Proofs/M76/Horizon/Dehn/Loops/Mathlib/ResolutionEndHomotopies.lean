import PoincareConjecture.Proofs.M76.Dehn.Mathlib.PolygonalResolutionEndPaths
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.ResolutionEndWordCalculation

set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76.Dehn.PolygonalCrossingResolution

local notation "C3" => ((ℝ × ℝ) × ℝ)

structure MarkedResolutionEndData {X : Type*} [TopologicalSpace X]
    (Fmark : Set X) (τ : C3 → X) (b : ℝ) (t : unitInterval) where
  z : Fmark
  a : Fmark
  c : Fmark
  l : Fmark
  r : Fmark
  z_val : (z : X) = τ ((0, 0), (t : ℝ))
  a_val : (a : X) = τ ((-1, 1), (t : ℝ))
  c_val : (c : X) = τ ((1, 1), (t : ℝ))
  l_val : (l : X) = τ ((-1, -1), (t : ℝ))
  r_val : (r : X) = τ ((1, -1), (t : ℝ))
  ra : Path z a
  rc : Path z c
  rl : Path z l
  rr : Path z r
  U : Path a c
  L : Path l a
  R : Path r c
  ra_val : ∀ s : unitInterval, (ra s : X) =
    τ (AffineMap.lineMap ((0, 0), (t : ℝ)) ((-1, 1), (t : ℝ)) (s : ℝ))
  rc_val : ∀ s : unitInterval, (rc s : X) =
    τ (AffineMap.lineMap ((0, 0), (t : ℝ)) ((1, 1), (t : ℝ)) (s : ℝ))
  rl_val : ∀ s : unitInterval, (rl s : X) =
    τ (AffineMap.lineMap ((0, 0), (t : ℝ)) ((-1, -1), (t : ℝ)) (s : ℝ))
  rr_val : ∀ s : unitInterval, (rr s : X) =
    τ (AffineMap.lineMap ((0, 0), (t : ℝ)) ((1, -1), (t : ℝ)) (s : ℝ))
  U_val : ∀ s : unitInterval, (U s : X) = τ (strip b true ((t : ℝ), 2 * (s : ℝ) - 1))
  L_val : ∀ s : unitInterval, (L s : X) = τ (alternate b false ((t : ℝ), 2 * (s : ℝ) - 1))
  R_val : ∀ s : unitInterval, (R s : X) = τ (alternate b true ((t : ℝ), 2 * (s : ℝ) - 1))
  U_homotopic : U.Homotopic (ra.symm.trans rc)
  L_homotopic : L.Homotopic (rl.symm.trans ra)
  R_homotopic : R.Homotopic (rr.symm.trans rc)

theorem nonempty_marked_resolution_end_data
    {X : Type*} [TopologicalSpace X] {Fmark : Set X} (τ : C3 → X)
    (hτ : ContinuousOn τ tube)
    (hτmark : ∀ z ∈ tube, z.2 = 0 ∨ z.2 = 1 → τ z ∈ Fmark)
    {b : ℝ} (hb : b < 1) (t : unitInterval) (ht : (t : ℝ) = 0 ∨ (t : ℝ) = 1) :
    Nonempty (MarkedResolutionEndData Fmark τ b t) := by
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
  let radial (x : endSquare (t : ℝ)) : Path (endCenter t) x :=
    Path.segmentIn (endSquare (t : ℝ)) (endCenter t) x
      (hconv.segment_subset (endCenter t).property x.property)
  have hpath (alternatePair positive : Bool) (x y : endSquare (t : ℝ))
      (hx : (x : C3) = resolutionMap 0 alternatePair positive ((t : ℝ), -1))
      (hy : (y : C3) = resolutionMap 0 alternatePair positive ((t : ℝ), 1)) :
      ∃ P : Path x y,
        (∀ s : unitInterval, (P s : C3) =
          resolutionMap b alternatePair positive ((t : ℝ), 2 * (s : ℝ) - 1)) ∧
        (P.map f.continuous).Homotopic
          (((radial x).map f.continuous).symm.trans ((radial y).map f.continuous)) := by
    obtain ⟨x', y', P, _, _, hx', hy', hP, _, _, _, _⟩ :=
      exists_resolution_end_path (X := Fmark) hb t alternatePair positive
    have hxx : x = x' := Subtype.ext (hx.trans hx'.symm)
    have hyy : y = y' := Subtype.ext (hy.trans hy'.symm)
    let P' := P.cast hxx hyy
    have hhom : P'.Homotopic ((radial x).symm.trans (radial y)) :=
      Path.homotopic_of_convex_range hconv Subset.rfl P'
        ((radial x).symm.trans (radial y)) (fun s ↦ (P' s).property)
        (fun s ↦ (((radial x).symm.trans (radial y)) s).property)
    refine ⟨P', hP, ?_⟩
    have h := hhom.map f
    rw [Path.map_trans, ← Path.map_symm] at h
    exact h
  obtain ⟨U, hU, hUhom⟩ := hpath false true a c
    (by norm_num [a, resolutionMap, strip, signedHeight, height])
    (by norm_num [c, resolutionMap, strip, signedHeight, height])
  obtain ⟨L, hL, hLhom⟩ := hpath true false l a
    (by norm_num [l, resolutionMap, alternate, signedHeight, height])
    (by norm_num [a, resolutionMap, alternate, signedHeight, height])
  obtain ⟨R, hR, hRhom⟩ := hpath true true r c
    (by norm_num [r, resolutionMap, alternate, signedHeight, height])
    (by norm_num [c, resolutionMap, alternate, signedHeight, height])
  refine ⟨{
    z := f (endCenter t), a := f a, c := f c, l := f l, r := f r
    z_val := rfl, a_val := rfl, c_val := rfl, l_val := rfl, r_val := rfl
    ra := (radial a).map f.continuous, rc := (radial c).map f.continuous
    rl := (radial l).map f.continuous, rr := (radial r).map f.continuous
    U := U.map f.continuous, L := L.map f.continuous, R := R.map f.continuous
    ra_val := fun _ ↦ rfl, rc_val := fun _ ↦ rfl
    rl_val := fun _ ↦ rfl, rr_val := fun _ ↦ rfl
    U_val := ?_, L_val := ?_, R_val := ?_
    U_homotopic := hUhom, L_homotopic := hLhom, R_homotopic := hRhom }⟩
  · intro s
    exact congrArg τ (hU s)
  · intro s
    exact congrArg τ (hL s)
  · intro s
    exact congrArg τ (hR s)

theorem exists_marked_resolution_end_word_calculations
    {X : Type*} [TopologicalSpace X] {Fmark : Set X} (τ : C3 → X)
    (hτ : ContinuousOn τ tube)
    (hτmark : ∀ z ∈ tube, z.2 = 0 ∨ z.2 = 1 → τ z ∈ Fmark)
    {b : ℝ} (hb : b < 1) :
    ∃ (E0 : MarkedResolutionEndData Fmark τ b 0)
      (E1 : MarkedResolutionEndData Fmark τ b 1),
      (∀ (base : Fmark) (p : Path base E0.z) (q : Path base E1.z)
        (a : Path E0.a E1.a) (β : Path E1.r E1.l)
        (c : Path E1.c E0.c) (d : Path E0.l E0.r),
        let A := basedPathWord (p.trans E0.ra) (q.trans E1.ra) a
        let B := basedPathWord (q.trans E1.rr) (q.trans E1.rl) β
        let C := basedPathWord (q.trans E1.rc) (p.trans E0.rc) c
        let D := basedPathWord (p.trans E0.rl) (p.trans E0.rr) d
        basedPathWord (p.trans E0.ra) (p.trans E0.ra)
            (((a.trans E1.U).trans c).trans E0.U.symm) = A * C ∧
          basedPathWord (p.trans E0.ra) (p.trans E0.ra)
            (((((((a.trans E1.L.symm).trans β.symm).trans E1.R).trans c).trans
              E0.R.symm).trans d.symm).trans E0.L) = A * B⁻¹ * C * D⁻¹) ∧
      (∀ (base : Fmark) (p : Path base E0.z) (q : Path base E1.z)
        (a : Path E1.a E0.a) (β : Path E0.r E1.l)
        (c : Path E1.c E0.c) (d : Path E0.l E1.r),
        let A := basedPathWord (q.trans E1.ra) (p.trans E0.ra) a
        let B := basedPathWord (p.trans E0.rr) (q.trans E1.rl) β
        let C := basedPathWord (q.trans E1.rc) (p.trans E0.rc) c
        let D := basedPathWord (p.trans E0.rl) (q.trans E1.rr) d
        basedPathWord (q.trans E1.ra) (q.trans E1.ra)
            (((a.trans E0.U).trans c.symm).trans E1.U.symm) = A * C⁻¹ ∧
          basedPathWord (q.trans E1.ra) (q.trans E1.ra)
            (((((((a.trans E0.L.symm).trans d).trans E1.R).trans c).trans
              E0.R.symm).trans β).trans E1.L) = A * D * C * B) := by
  obtain ⟨E0⟩ := nonempty_marked_resolution_end_data τ hτ hτmark hb 0 (Or.inl rfl)
  obtain ⟨E1⟩ := nonempty_marked_resolution_end_data τ hτ hτmark hb 1 (Or.inr rfl)
  refine ⟨E0, E1, ?_, ?_⟩
  · intro base p q a β c d
    exact resolution_end_words_case_a p q E0.ra E0.rc E0.rl E0.rr
      E1.ra E1.rc E1.rl E1.rr E0.U E0.L E0.R E1.U E1.L E1.R
      E0.U_homotopic E0.L_homotopic E0.R_homotopic
      E1.U_homotopic E1.L_homotopic E1.R_homotopic a β c d
  · intro base p q a β c d
    exact resolution_end_words_case_b p q E0.ra E0.rc E0.rl E0.rr
      E1.ra E1.rc E1.rl E1.rr E0.U E0.L E0.R E1.U E1.L E1.R
      E0.U_homotopic E0.L_homotopic E0.R_homotopic
      E1.U_homotopic E1.L_homotopic E1.R_homotopic a β c d

end PoincareConjecture.M76.Dehn.PolygonalCrossingResolution
