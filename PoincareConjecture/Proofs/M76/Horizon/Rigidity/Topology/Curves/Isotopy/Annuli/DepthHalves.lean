import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.FinitePLEssentialCircle
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusFinitePL

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

def annularDepthHalf (side : Bool) : Set P2 :=
  {x | x ∈ Ann ∧ if side then 0 ≤ depth 8 x else depth 8 x ≤ 0}

theorem exists_finitePL_annularDepthHalf (side : Bool) :
    ∃ A : Ann ≃ₜ annularDepthHalf side, A.IsFinitePL ∧
      (∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * 8)) (u : Icc (-1 : ℝ) 1),
        (A ⟨annulusMap 8 (by norm_num) ((s : Circle), u),
          _root_.Dehn.annulus_period_point_mem (by norm_num) (by norm_num) _ u⟩ : P2) =
          annulusMap 8 (by norm_num) ((s : Circle), ((u : ℝ) + if side then 1 else -1) / 2)) ∧
      ∀ x : Ann, depth 8 (A x : P2) = (depth 8 (x : P2) + if side then 1 else -1) / 2 := by
  classical
  let a : P2 →ᴬ[ℝ] P2 := (ContinuousLinearMap.fst ℝ ℝ ℝ).toContinuousAffineMap.prod
    ((2 : ℝ)⁻¹ • ((ContinuousLinearMap.snd ℝ ℝ ℝ).toContinuousAffineMap +
      ContinuousAffineMap.const ℝ P2 (if side then 1 else -1)))
  have ha (x : P2) : a x = (x.1, (x.2 + if side then 1 else -1) / 2) := by
    apply Prod.ext
    · rfl
    · change (2 : ℝ)⁻¹ * (x.2 + if side then 1 else -1) = _
      ring
  have hau {u : ℝ} (hu : u ∈ Icc (-1 : ℝ) 1) :
      (u + if side then 1 else -1) / 2 ∈ Icc (-1 : ℝ) 1 := by
    cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      constructor <;> linarith [hu.1, hu.2]
  have hw := finitePiecewiseAffineOn_wrappedStripMap
    (L := (8 : ℝ)) (d := 1) (by norm_num) (by norm_num)
  have hwcopy := hw
  obtain ⟨K, hK, hKs, _⟩ := hwcopy
  have haPL : FinitePiecewiseAffineOn a (rectangle (4 * 8) 1) :=
    ⟨K, hK, hKs, K.affineOnFaces_affine a⟩
  let f : P2 → P2 := wrappedStripMap 8 ∘ a
  have hf : FinitePiecewiseAffineOn f (rectangle (4 * 8) 1) :=
    hw.comp haPL (by intro x hx; rw [ha]; exact ⟨hx.1, hau hx.2⟩)
  have hval (x : P2) (hx : x ∈ rectangle (4 * 8) 1) :
      f x = annulusMap 8 (by norm_num)
        ((x.1 : Circle), (x.2 + if side then 1 else -1) / 2) := by
    change wrappedStripMap 8 (a x) = _
    rw [ha]
    exact (annulusMap_coe (by norm_num)
      (by have hh := abs_le.mpr (hau hx.2); linarith) hx.1).symm
  have hfib (x : P2) (hx : x ∈ rectangle (4 * 8) 1)
      (y : P2) (hy : y ∈ rectangle (4 * 8) 1) :
      f x = f y ↔ x.2 = y.2 ∧ (x.1 : Circle) = (y.1 : Circle) := by
    rw [hval x hx, hval y hy]
    constructor
    · intro h
      have hh := injective_annulusMap (L := (8 : ℝ)) (d := 1)
        (by norm_num) (by norm_num)
        (a₁ := ((x.1 : Circle), ⟨_, hau hx.2⟩))
        (a₂ := ((y.1 : Circle), ⟨_, hau hy.2⟩)) h
      refine ⟨?_, congrArg Prod.fst hh⟩
      have hv := congrArg (fun z : Circle × Icc (-1 : ℝ) 1 => (z.2 : ℝ)) hh
      dsimp only at hv
      linarith
    · rintro ⟨hu, hs⟩
      rw [hu, hs]
  obtain ⟨A, hA, _, hAv, hAp⟩ :=
    _root_.Dehn.exists_finitePL_annulus_of_periodic_strip
      (L := 8) (d := 1) (by norm_num) (by norm_num) f hf hfib
  have hdep (x : P2) (hx : x ∈ rectangle (4 * 8) 1) :
      depth 8 (f x) = (x.2 + if side then 1 else -1) / 2 := by
    rw [hval x hx]
    exact depth_annulusMap (by norm_num)
      (by have hh := abs_le.mpr (hau hx.2); linarith) _
  have himage : f '' rectangle (4 * 8) 1 = annularDepthHalf side := by
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      refine ⟨mem_squareAnnulus_iff_depth.mpr ?_, ?_⟩
      · rw [hdep x hx]
        exact hau hx.2
      · rw [hdep x hx]
        cases side <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
          linarith [hx.2.1, hx.2.2]
    · intro x hx
      obtain ⟨s, hs, hxs⟩ := exists_period_parameter_of_depth
        (L := (8 : ℝ)) (d := 1) (by norm_num) (by norm_num) ⟨x, hx.1⟩
      let u := 2 * depth 8 x - if side then 1 else -1
      have hu : u ∈ Icc (-1 : ℝ) 1 := by
        have hd := mem_squareAnnulus_iff_depth.mp hx.1
        cases side <;> simp only [annularDepthHalf, mem_ofPred_eq,
          Bool.false_eq_true, ↓reduceIte] at hx <;>
          dsimp [u] <;> constructor <;> linarith [hd.1, hd.2, hx.2]
      refine ⟨(s, u), ⟨hs, hu⟩, ?_⟩
      rw [hval _ ⟨hs, hu⟩, show (u + if side then 1 else -1) / 2 = depth 8 x by dsimp [u]; ring]
      exact hxs.symm
  refine ⟨A.trans (Homeomorph.setCongr himage), hA.setCongr rfl himage, ?_, ?_⟩
  · intro s hs u
    exact (hAv s hs u).trans (hval _ ⟨hs, u.property⟩)
  · intro x
    obtain ⟨s, hs, hxs⟩ := exists_period_parameter_of_depth
      (L := (8 : ℝ)) (d := 1) (by norm_num) (by norm_num) x
    change depth 8 (A x : P2) = _
    rw [hAp x s hs hxs]
    exact hdep _ ⟨hs, mem_squareAnnulus_iff_depth.mp x.property⟩

theorem annularDepthHalf_union : annularDepthHalf false ∪ annularDepthHalf true = Ann := by
  ext x
  simp only [annularDepthHalf, mem_union, mem_ofPred_eq, Bool.false_eq_true, ↓reduceIte]
  constructor
  · exact fun h => h.elim And.left And.left
  · intro hx
    exact (le_total (depth 8 x) 0).elim (fun h => Or.inl ⟨hx, h⟩)
      (fun h => Or.inr ⟨hx, h⟩)

theorem exists_finitePL_annularDepthHalf_rims (side : Bool) :
    ∃ A : Ann ≃ₜ annularDepthHalf side, A.IsFinitePL ∧
      (∀ x : Ann, depth 8 (A x : P2) =
        (depth 8 (x : P2) + if side then 1 else -1) / 2) ∧
      (∀ z : Circle, (A (annulusRimPoint false z) : P2) =
        if side then annulusCoreCircle z else annulusRimPoint false z) ∧
      ∀ z : Circle, (A (annulusRimPoint true z) : P2) =
        if side then annulusRimPoint true z else annulusCoreCircle z := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨A, hA, hval, hdepth⟩ := exists_finitePL_annularDepthHalf side
  refine ⟨A, hA, hdepth, ?_, ?_⟩
  all_goals
    intro z
    let s := AddCircle.equivIco (4 * (8 : ℝ)) 0 z
    have hs : (s : ℝ) ∈ Icc 0 (4 * (8 : ℝ)) :=
      ⟨s.property.1, by simpa only [zero_add] using s.property.2.le⟩
    have hsz : ((s : ℝ) : Circle) = z := AddCircle.coe_equivIco
  · have h := hval s hs ⟨-1, by norm_num⟩
    rw [hsz] at h
    cases side <;> simpa [annulusRimPoint, annulusCoreCircle_apply] using h
  · have h := hval s hs ⟨1, by norm_num⟩
    rw [hsz] at h
    cases side <;> simpa [annulusRimPoint, annulusCoreCircle_apply] using h

end PoincareConjecture.M76.Dehn
