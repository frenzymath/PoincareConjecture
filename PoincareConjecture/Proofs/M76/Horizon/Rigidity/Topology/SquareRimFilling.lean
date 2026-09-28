import PoincareConjecture.Proofs.M76.Wall.SquareRimCoordinates
import PoincareConjecture.Proofs.M76.Mathlib.ContractibleBallExtension
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup

set_option autoImplicit false
open Set Metric
open scoped unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "Q" => sphere (0 : V2) 1

theorem squareRimLoop_fibers (s t : unitInterval)
    (h : squareRimLoop s = squareRimLoop t) :
    s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
  have hxy := congrArg Subtype.val h
  rw [Wall.squareRimLoop_coordinates, Wall.squareRimLoop_coordinates] at hxy
  have hs0 := s.property.1
  have hs1 := s.property.2
  have ht0 := t.property.1
  have ht1 := t.property.2
  split_ifs at hxy <;>
    have hx := congrFun hxy 0 <;>
    have hy := congrFun hxy 1 <;>
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hx hy
  all_goals
    first
    | exact Or.inl (Subtype.ext (by linarith))
    | exact Or.inr (Or.inl ⟨Subtype.ext (by change (s : ℝ) = 0; linarith),
        Subtype.ext (by change (t : ℝ) = 1; linarith)⟩)
    | exact Or.inr (Or.inr ⟨Subtype.ext (by change (s : ℝ) = 1; linarith),
        Subtype.ext (by change (t : ℝ) = 0; linarith)⟩)

theorem surjective_squareRimLoop : Function.Surjective squareRimLoop := by
  intro x
  have hn : ‖(x : V2)‖ = 1 := mem_sphere_zero_iff_norm.mp x.property
  have hx0 : -1 ≤ x.val 0 ∧ x.val 0 ≤ 1 := by
    exact abs_le.mp (by simpa only [Real.norm_eq_abs, hn] using norm_le_pi_norm x.val 0)
  have hx1 : -1 ≤ x.val 1 ∧ x.val 1 ≤ 1 := by
    exact abs_le.mp (by simpa only [Real.norm_eq_abs, hn] using norm_le_pi_norm x.val 1)
  have hside : x.val 1 = -1 ∨ x.val 0 = 1 ∨ x.val 1 = 1 ∨ x.val 0 = -1 := by
    by_contra! hside
    have hlt : ‖x.val‖ < 1 := (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr (by
      intro i
      fin_cases i
      · exact abs_lt.mpr ⟨lt_of_le_of_ne hx0.1 hside.2.2.2.symm,
          lt_of_le_of_ne hx0.2 hside.2.1⟩
      · exact abs_lt.mpr ⟨lt_of_le_of_ne hx1.1 hside.1.symm,
          lt_of_le_of_ne hx1.2 hside.2.2.1⟩)
    linarith
  rcases hside with h | h | h | h
  · let t : unitInterval := ⟨(x.val 0 + 1) / 8, ⟨by linarith, by linarith⟩⟩
    refine ⟨t, Subtype.ext ?_⟩
    rw [Wall.squareRimLoop_coordinates, if_pos (show (t : ℝ) ≤ 1 / 4 by dsimp [t]; linarith)]
    ext i
    fin_cases i <;> simp [t, h]
    all_goals ring
  · by_cases hbottom : x.val 1 = -1
    · let t : unitInterval := ⟨1 / 4, by norm_num⟩
      refine ⟨t, Subtype.ext ?_⟩
      rw [Wall.squareRimLoop_coordinates]
      ext i
      fin_cases i <;> norm_num [t, h, hbottom]
    · let t : unitInterval := ⟨(x.val 1 + 3) / 8, ⟨by linarith, by linarith⟩⟩
      refine ⟨t, Subtype.ext ?_⟩
      rw [Wall.squareRimLoop_coordinates,
        if_neg (show ¬(t : ℝ) ≤ 1 / 4 by dsimp [t]; intro ht; apply hbottom; linarith),
        if_pos (show (t : ℝ) ≤ 1 / 2 by dsimp [t]; linarith)]
      ext i
      fin_cases i <;> simp [t, h]
      all_goals ring
  · by_cases hright : x.val 0 = 1
    · let t : unitInterval := ⟨1 / 2, by norm_num⟩
      refine ⟨t, Subtype.ext ?_⟩
      rw [Wall.squareRimLoop_coordinates]
      ext i
      fin_cases i <;> norm_num [t, h, hright]
    · let t : unitInterval := ⟨(5 - x.val 0) / 8, ⟨by linarith, by linarith⟩⟩
      refine ⟨t, Subtype.ext ?_⟩
      rw [Wall.squareRimLoop_coordinates,
        if_neg (show ¬(t : ℝ) ≤ 1 / 4 by dsimp [t]; linarith),
        if_neg (show ¬(t : ℝ) ≤ 1 / 2 by dsimp [t]; intro ht; apply hright; linarith),
        if_pos (show (t : ℝ) ≤ 3 / 4 by dsimp [t]; linarith)]
      ext i
      fin_cases i <;> simp [t, h]
      all_goals ring
  · by_cases htop : x.val 1 = 1
    · let t : unitInterval := ⟨3 / 4, by norm_num⟩
      refine ⟨t, Subtype.ext ?_⟩
      rw [Wall.squareRimLoop_coordinates]
      ext i
      fin_cases i <;> norm_num [t, h, htop]
    · let t : unitInterval := ⟨(7 - x.val 1) / 8, ⟨by linarith, by linarith⟩⟩
      refine ⟨t, Subtype.ext ?_⟩
      rw [Wall.squareRimLoop_coordinates,
        if_neg (show ¬(t : ℝ) ≤ 1 / 4 by dsimp [t]; linarith),
        if_neg (show ¬(t : ℝ) ≤ 1 / 2 by dsimp [t]; linarith),
        if_neg (show ¬(t : ℝ) ≤ 3 / 4 by dsimp [t]; intro ht; apply htop; linarith)]
      ext i
      fin_cases i <;> simp [t, h]
      all_goals ring

theorem isQuotientMap_squareRimLoop : Topology.IsQuotientMap squareRimLoop :=
  .of_surjective_continuous surjective_squareRimLoop squareRimLoop.continuous

variable {Y : Type*} [TopologicalSpace Y]

theorem exists_squareRimMap {y : Y} (p : Path y y) :
    ∃ gamma : C(Q, Y), ∀ t : unitInterval, gamma (squareRimLoop t) = p t := by
  have hfactor : Function.FactorsThrough p.toContinuousMap squareRimLoop := by
    intro s t h
    rcases squareRimLoop_fibers s t h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact p.source.trans p.target.symm
    · exact p.target.trans p.source.symm
  refine ⟨isQuotientMap_squareRimLoop.lift p.toContinuousMap hfactor, ?_⟩
  intro t
  exact congrArg (fun f : C(unitInterval, Y) => f t)
    (isQuotientMap_squareRimLoop.lift_comp p.toContinuousMap hfactor)

theorem nullhomotopic_of_squareRimLoop (gamma : C(Q, Y))
    (h : (squareRimLoop.map gamma.continuous).Homotopic
      (Path.refl (gamma squareRimBase))) : gamma.Nullhomotopic := by
  obtain ⟨H⟩ := h
  let P : C(unitInterval, C(unitInterval, Y)) :=
    (H.toHomotopy.toContinuousMap.comp ⟨Prod.swap, continuous_swap⟩).curry
  have hfactor : Function.FactorsThrough P squareRimLoop := by
    intro s t h
    rcases squareRimLoop_fibers s t h with rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · ext v
      exact (H.source v).trans (H.target v).symm
    · ext v
      exact (H.target v).trans (H.source v).symm
  let L := isQuotientMap_squareRimLoop.lift P hfactor
  have hL (s t : unitInterval) : L (squareRimLoop s) t = H (t, s) :=
    congrArg (fun f : C(unitInterval, C(unitInterval, Y)) => f s t)
      (isQuotientMap_squareRimLoop.lift_comp P hfactor)
  refine ⟨gamma squareRimBase, ⟨{
    toContinuousMap := L.uncurry.comp ⟨Prod.swap, continuous_swap⟩
    map_zero_left := ?_
    map_one_left := ?_ }⟩⟩
  · intro x
    obtain ⟨s, rfl⟩ := surjective_squareRimLoop x
    exact (hL s 0).trans (H.toHomotopy.apply_zero s)
  · intro x
    obtain ⟨s, rfl⟩ := surjective_squareRimLoop x
    exact (hL s 1).trans (H.toHomotopy.apply_one s)

theorem injective_or_exists_squareRim_filling
    {Z : Type*} [TopologicalSpace Z] (i : C(Y, Z)) (y : Y) :
    Function.Injective (FundamentalGroup.map i y) ∨
      ∃ (gamma : C(Q, Y)) (f : C(closedBall (0 : V2) 1, Z)),
        gamma squareRimBase = y ∧
        (∀ x : Q, f ⟨x, sphere_subset_closedBall x.property⟩ = i (gamma x)) ∧
        FundamentalGroup.fromPath
          (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1 := by
  classical
  by_cases hinj : Function.Injective (FundamentalGroup.map i y)
  · exact Or.inl hinj
  right
  have hex : ∃ c : FundamentalGroup Y y, c ≠ 1 ∧ FundamentalGroup.map i y c = 1 := by
    by_contra! h
    apply hinj
    intro v w hvw
    have hc : FundamentalGroup.map i y (v * w⁻¹) = 1 := by
      rw [map_mul, map_inv, hvw, mul_inv_cancel]
    have hunit : v * w⁻¹ = 1 := by
      by_contra hne
      exact h _ hne hc
    exact mul_inv_eq_one.mp hunit
  obtain ⟨c, hc, hci⟩ := hex
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective c
  obtain ⟨gamma, hgamma⟩ := exists_squareRimMap p
  have hbase : gamma squareRimBase = y := by
    simpa only [Path.source] using hgamma 0
  have hpi : (p.map i.continuous).Homotopic (Path.refl (i y)) :=
    Path.Homotopic.Quotient.exact hci
  have hloop : (squareRimLoop.map (i.comp gamma).continuous) =
      (p.map i.continuous).cast (congrArg i hbase) (congrArg i hbase) := by
    ext t
    exact congrArg i (hgamma t)
  have hnull : (i.comp gamma).Nullhomotopic := by
    apply nullhomotopic_of_squareRimLoop
    rw [hloop]
    have href : (Path.refl (i y)).cast (congrArg i hbase) (congrArg i hbase) =
        Path.refl ((i.comp gamma) squareRimBase) := by
      ext t
      exact (congrArg i hbase).symm
    simpa only [href] using hpi.pathCast (congrArg i hbase) (congrArg i hbase)
  obtain ⟨f, hf⟩ := hnull.exists_closedBall_extension (i.comp gamma)
  refine ⟨gamma, f, hbase, hf, ?_⟩
  intro htrivial
  have hgp : (squareRimLoop.map gamma.continuous).Homotopic
      (Path.refl (gamma squareRimBase)) := Path.Homotopic.Quotient.exact htrivial
  have heq : (squareRimLoop.map gamma.continuous).cast hbase.symm hbase.symm = p := by
    ext t
    exact hgamma t
  have hprefl : p.Homotopic (Path.refl y) := by
    have hh := hgp.pathCast hbase.symm hbase.symm
    have href : (Path.refl (gamma squareRimBase)).cast hbase.symm hbase.symm =
        Path.refl y := by
      ext t
      exact hbase
    simpa only [heq, href] using hh
  exact hc (Path.Homotopic.Quotient.eq.mpr hprefl)

end PoincareConjecture.M76.Dehn
