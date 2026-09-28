import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Polygons.FinitePLReturningBigon
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Regions.ProperArcPairConfinement
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusOpenChart
import PoincareConjecture.Proofs.M76.Mathlib.CompactLocallyPLComposition









set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Circle" => AddCircle (4 * (8 : ℝ))


noncomputable def annularLiftProjection (x : P2) : P2 :=
  annulusMap 8 (by norm_num) ((x.2 : Circle), x.1)

theorem exists_annular_returning_bigon_support
    {W : Set P2} {a b : P2} {d : ℝ}
    (hW : IsFinitePLBallPair ℝ W {a, b}) (hab : a.1 < b.1)
    (haxis : W ∩ {x : P2 | x.2 = 0} = {a, b})
    (hd : d < 4 * (8 : ℝ))
    (hstrip : W ⊆ Ioo (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) d) :
    ∃ B D : Set P2,
      IsFinitePLBallPair P2 B (W ∪ segment ℝ a b) ∧
      IsFinitePLBallPair P2 D (frontier D) ∧ IsCompact D ∧ B ⊆ D ∧
      a ∈ frontier D ∧ b ∈ frontier D ∧
      W ⊆ D ∧ segment ℝ a b ⊆ D ∧
      W \ {a, b} ⊆ interior D ∧ segment ℝ a b \ {a, b} ⊆ interior D ∧
      FinitePiecewiseAffineOn annularLiftProjection D ∧ InjOn annularLiftProjection D ∧
      IsFinitePLBallPair P2 (annularLiftProjection '' D)
        (frontier (annularLiftProjection '' D)) ∧
      annularLiftProjection '' D ⊆ depth 8 ⁻¹' Ioo (-1 : ℝ) 1 ∧
      (∃ Q : D ≃ₜ (annularLiftProjection '' D), Q.IsFinitePL ∧ Q.symm.IsFinitePL ∧
        ∀ x : D, (Q x : P2) = annularLiftProjection x) ∧
      annularLiftProjection '' (W \ {a, b}) ⊆ interior (annularLiftProjection '' D) ∧
      annularLiftProjection '' (segment ℝ a b \ {a, b}) ⊆
        interior (annularLiftProjection '' D) := by
  classical
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  have haW : a ∈ W := hW.1 (by simp)
  have hbW : b ∈ W := hW.1 (by simp)
  have ha : a.2 = 0 := (haxis.symm.subset (by simp)).2
  have hb : b.2 = 0 := (haxis.symm.subset (by simp)).2
  have hd0 : 0 ≤ d := (hstrip haW).2.1.trans (hstrip haW).2.2
  have hab' : a ≠ b := fun h => hab.ne (congrArg Prod.fst h)
  obtain ⟨n, P, hP, hi, _, hboundary, hB, _, _, hconvex⟩ :=
    exists_finite_pl_returning_bigon hW hab' (fun x hx => (hstrip hx).2.1) haxis
  let B := closure P.inside
  let eps := (4 * (8 : ℝ) - d) / 4
  have heps : 0 < eps := by dsimp [eps]; linarith
  have hwidth : d + eps < -eps + 4 * (8 : ℝ) := by dsimp [eps]; linarith
  let U : Set P2 := Ioo (-1 : ℝ) 1 ×ˢ Ioo (-eps) (d + eps)
  have hBU : B ⊆ U := by
    have hBC := hconvex (Ioo (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) d)
      ((convex_Ioo _ _).prod (convex_Icc _ _)) hstrip
    intro x hx
    have hh := hBC hx
    exact ⟨hh.1, by constructor <;> linarith [hh.2.1, hh.2.2]⟩
  have hB' : IsFinitePLBallPair P2 B (segment ℝ a b ∪ W) := by
    simpa only [union_comm] using hB
  obtain ⟨D, hcompact, hD, hDU, hBD, haD, hbD, hWD, hsD, hWi, hsi, _⟩ :=
    exists_confined_proper_arc_pair_disk hW hab ha hb
      (fun x hx => (hstrip hx).2.1) haxis hB'
      (isOpen_Ioo.prod isOpen_Ioo) hBU
  have hDcopy := hD
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ := hDcopy
  have hswap : FinitePiecewiseAffineOn (Prod.swap : P2 → P2) D := by
    rw [← hKs]
    exact (K.affineOnFaces_affine
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ).toContinuousAffineEquiv.toContinuousAffineMap).finitePiecewiseAffineOn hK
  have hproj : FinitePiecewiseAffineOn annularLiftProjection D :=
    (locallyPiecewiseAffineOn_annulusMap_lift (L := 8) (d := 1)
      (by norm_num) (by norm_num) (by norm_num)).comp_finitePiecewiseAffineOn hswap
        (fun x hx => ⟨mem_univ _, (hDU hx).1⟩)
  have hinj : InjOn annularLiftProjection D := by
    intro x hx y hy heq
    have hxu := hDU hx
    have hyu := hDU hy
    have h := injective_annulusMap (L := 8) (d := 1) (by norm_num) (by norm_num)
      (a₁ := ((x.2 : Circle), ⟨x.1, hxu.1.1.le, hxu.1.2.le⟩))
      (a₂ := ((y.2 : Circle), ⟨y.1, hyu.1.1.le, hyu.1.2.le⟩)) heq
    have hh : x.1 = y.1 := congrArg (fun z : Circle × Icc (-1 : ℝ) 1 => (z.2 : ℝ)) h
    have hc : (x.2 : Circle) = (y.2 : Circle) := congrArg Prod.fst h
    have hxperiod : x.2 ∈ Ico (-eps) (-eps + 4 * (8 : ℝ)) :=
      ⟨hxu.2.1.le, hxu.2.2.trans hwidth⟩
    have hyperiod : y.2 ∈ Ico (-eps) (-eps + 4 * (8 : ℝ)) :=
      ⟨hyu.2.1.le, hyu.2.2.trans hwidth⟩
    exact Prod.ext hh ((AddCircle.coe_eq_coe_iff_of_mem_Ico hxperiod hyperiod).mp hc)
  have himage := hD.image hproj hinj
  have hfront := himage.frontier_eq_of_finrank_eq rfl
  obtain ⟨Q, hQ, hQval⟩ := hproj.exists_homeomorph_image hinj
  refine ⟨B, D, hB, hD, hcompact, hBD, haD, hbD, hWD, hsD, hWi, hsi,
    hproj, hinj, hfront.symm ▸ himage, ?_, ⟨Q, hQ, hQ.symm, hQval⟩, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    change depth 8 (annulusMap 8 _ ((x.2 : Circle), x.1)) ∈ Ioo (-1 : ℝ) 1
    rw [depth_annulusMap (by norm_num) (by
      have hh := abs_le.mpr ⟨(hDU hx).1.1.le, (hDU hx).1.2.le⟩
      linarith)]
    exact (hDU hx).1
  · rintro _ ⟨x, hx, rfl⟩
    exact hproj.mem_interior_image rfl hinj (hWi hx)
  · rintro _ ⟨x, hx, rfl⟩
    exact hproj.mem_interior_image rfl hinj (hsi hx)

end PoincareConjecture.M76.Dehn
