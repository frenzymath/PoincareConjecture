import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.SignedAnnularDegree
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.PolyhedralSource
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.PeriodCircleLoop
import Mathlib.Analysis.Convex.PathConnected









set_option autoImplicit false
open Set Metric Geometry
open scoped unitInterval

namespace PoincareConjecture.M76

theorem exists_real_lift_boundaryLoopIterate_periodLoop
    (p : ℝ) [Fact (0 < p)] (n : ℕ) :
    ∃ L : C(unitInterval, ℝ), L 0 = 0 ∧ L 1 = (n : ℝ) * p ∧
      ∀ t, (L t : AddCircle p) = boundaryLoopIterate (AddCircle.periodLoop p) n t := by
  induction n with
  | zero =>
    exact ⟨ContinuousMap.const _ 0, rfl, by simp, fun _ => rfl⟩
  | succ n ih =>
    obtain ⟨L, hzero, hone, hL⟩ := ih
    let a : Path (0 : ℝ) p := Path.segment 0 p
    let b : Path p (p + (n : ℝ) * p) :=
      { toFun := fun t => p + L t
        continuous_toFun := continuous_const.add L.continuous
        source' := by rw [hzero, add_zero]
        target' := by rw [hone] }
    refine ⟨(a.trans b).toContinuousMap, (a.trans b).source, ?_, ?_⟩
    · change (a.trans b) 1 = _
      rw [Path.target, Nat.cast_add, Nat.cast_one]
      ring
    · intro t
      change ((a.trans b) t : AddCircle p) = _
      rw [boundaryLoopIterate, Path.trans_apply, Path.trans_apply]
      split_ifs
      · change (((AffineMap.lineMap 0 p _) : ℝ) : AddCircle p) = _
        simp only [AffineMap.lineMap_apply_module, smul_eq_mul, mul_zero, zero_add]
        rfl
      · change ((p + L _) : AddCircle p) = _
        simpa only [AddCircle.coe_add, AddCircle.coe_period, zero_add] using hL _

namespace Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))

theorem annulusSquareRimParameter_periodLoop (t : unitInterval) :
    annulusSquareRimParameter (AddCircle.periodLoop (4 * (8 : ℝ)) t) =
      squareRimLoop t := by
  change HamiltonIndexOne.squareCircle
    (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (2 : ℝ))
      (by norm_num) (by norm_num) (((t : ℝ) * (4 * 8) : ℝ) : Circle)) = _
  rw [AddCircle.homeomorphAddCircle_apply_mk]
  have hscale : (t : ℝ) * (4 * 8) * ((4 * 8)⁻¹ * (4 * 2)) = 8 * t := by ring
  rw [hscale]
  apply Subtype.ext
  rw [HamiltonIndexOne.squareCircle_apply]
  have hs : (8 * (t : ℝ)) ∈ Icc (0 : ℝ) (4 * 2) := by
    constructor <;> linarith [t.property.1, t.property.2]
  have hmap := PLAnnularStrip.annulusMap_coe (L := (2 : ℝ))
    (by norm_num : (0 : ℝ) < 2) (by norm_num : 4 * |(0 : ℝ)| < 2) hs
  change ![-1 + (PLAnnularStrip.annulusMap 2 (by norm_num)
    ((((8 * (t : ℝ)) : ℝ) : AddCircle (4 * (2 : ℝ))), 0)).1,
    -1 + (PLAnnularStrip.annulusMap 2 (by norm_num)
    ((((8 * (t : ℝ)) : ℝ) : AddCircle (4 * (2 : ℝ))), 0)).2] = _
  rw [hmap, Wall.squareRimLoop_coordinates]
  simp only [PLAnnularStrip.wrappedStripMap, PLAnnularStrip.coordinate,
    PLAnnularStrip.cornerCorrection]
  split_ifs <;> ext i <;> fin_cases i <;> norm_num <;> first | linarith

theorem homotopic_nsmul_of_squareRimLoop_iterate
    (gamma : C(Q2, Circle)) (n : ℕ)
    (hgamma : ∀ t, gamma (squareRimLoop t) =
      boundaryLoopIterate (AddCircle.periodLoop (4 * (8 : ℝ))) n t) :
    Nonempty ((gamma.comp ⟨annulusSquareRimParameter, annulusSquareRimParameter.continuous⟩).Homotopy
      ⟨fun z => n • z, by fun_prop⟩) := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨L, hzero, hone, hL⟩ :=
    exists_real_lift_boundaryLoopIterate_periodLoop (4 * (8 : ℝ)) n
  let H : C(unitInterval × unitInterval, Circle) :=
    ⟨fun z => (((1 - (z.1 : ℝ)) * L z.2 +
      (z.1 : ℝ) * ((n : ℝ) * (z.2 : ℝ) * (4 * 8)) : ℝ) : Circle), by fun_prop⟩
  have hclosed (t : unitInterval) : H (t, 0) = H (t, 1) := by
    change (((1 - (t : ℝ)) * L 0 + (t : ℝ) * ((n : ℝ) * 0 * (4 * 8)) : ℝ) : Circle) =
      (((1 - (t : ℝ)) * L 1 + (t : ℝ) * ((n : ℝ) * 1 * (4 * 8)) : ℝ) : Circle)
    rw [hzero, hone]
    have heq : (1 - (t : ℝ)) * ((n : ℝ) * (4 * 8)) +
        (t : ℝ) * ((n : ℝ) * 1 * (4 * 8)) = n • (4 * (8 : ℝ)) := by
      rw [nsmul_eq_mul]
      ring
    rw [heq, AddCircle.coe_nsmul, AddCircle.coe_period]
    simp
  obtain ⟨G, hG⟩ := exists_square_cylinder_of_closed_curves H hclosed
  refine ⟨{
    toFun := fun z => G (z.1, annulusSquareRimParameter z.2)
    continuous_toFun := G.continuous.comp
      (continuous_fst.prodMk (annulusSquareRimParameter.continuous.comp continuous_snd))
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro z
    obtain ⟨s, hs⟩ := surjective_squareRimLoop (annulusSquareRimParameter z)
    change G (0, annulusSquareRimParameter z) = gamma (annulusSquareRimParameter z)
    rw [← hs, hG, hgamma]
    simpa [H] using hL s
  · intro z
    obtain ⟨s, hs⟩ := surjective_squareRimLoop (annulusSquareRimParameter z)
    have hz : AddCircle.periodLoop (4 * (8 : ℝ)) s = z :=
      annulusSquareRimParameter.injective ((annulusSquareRimParameter_periodLoop s).trans hs)
    change G (1, annulusSquareRimParameter z) = n • z
    rw [← hs, hG, ← hz]
    change (((1 - (1 : ℝ)) * L s + (1 : ℝ) * ((n : ℝ) * (s : ℝ) * (4 * 8)) : ℝ) : Circle) = _
    simp only [sub_self, zero_mul, one_mul, zero_add]
    change (((n : ℝ) * (s : ℝ) * (4 * 8) : ℝ) : Circle) =
      n • (((s : ℝ) * (4 * 8) : ℝ) : Circle)
    rw [mul_assoc, ← nsmul_eq_mul, AddCircle.coe_nsmul]

theorem homotopic_nsmul_of_periodLoop_iterate
    (f : C(Circle, Circle)) (n : ℕ)
    (hf : ∀ t, f (AddCircle.periodLoop (4 * (8 : ℝ)) t) =
      boundaryLoopIterate (AddCircle.periodLoop (4 * (8 : ℝ))) n t) :
    Nonempty (f.Homotopy ⟨fun z => n • z, by fun_prop⟩) := by
  let gamma : C(Q2, Circle) := f.comp
    ⟨annulusSquareRimParameter.symm, annulusSquareRimParameter.symm.continuous⟩
  have hgamma (t : unitInterval) : gamma (squareRimLoop t) =
      boundaryLoopIterate (AddCircle.periodLoop (4 * (8 : ℝ))) n t := by
    change f (annulusSquareRimParameter.symm (squareRimLoop t)) = _
    rw [← annulusSquareRimParameter_periodLoop t,
      annulusSquareRimParameter.symm_apply_apply]
    exact hf t
  have heq : gamma.comp
      ⟨annulusSquareRimParameter, annulusSquareRimParameter.continuous⟩ = f := by
    ext z
    change f (annulusSquareRimParameter.symm (annulusSquareRimParameter z)) = f z
    rw [annulusSquareRimParameter.symm_apply_apply]
  simpa only [heq] using homotopic_nsmul_of_squareRimLoop_iterate gamma n hgamma

end Dehn
end PoincareConjecture.M76
