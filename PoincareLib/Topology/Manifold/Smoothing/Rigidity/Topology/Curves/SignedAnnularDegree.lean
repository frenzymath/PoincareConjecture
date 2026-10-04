import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Curves.FinitePLEssentialCircle

/-!
# Signed degree of an essential embedded annular circle

The actual finite PL embedded circle is homotopic to a homeomorphic traversal
of the core. Its radial lift has one signed period; consequently a positive
integer multiplicity for that same radial map must be one.
-/

set_option autoImplicit false

open Set Metric Geometry PLAnnularStrip

namespace AddCircle

/-- A circle map homotopic both to a homeomorphism and to positive integer
multiplication has multiplicity one. Both actual homotopies are retained. -/
theorem nat_eq_one_of_homotopic_homeomorph
    {p : ℝ} [Fact (0 < p)] (f : C(AddCircle p, AddCircle p))
    (q : AddCircle p ≃ₜ AddCircle p)
    (Hq : f.Homotopy ⟨q, q.continuous⟩)
    (n : ℕ) (hn : 0 < n)
    (Hn : f.Homotopy ⟨fun z => n • z, by fun_prop⟩) : n = 1 := by
  obtain ⟨L, hL, hperiod⟩ := exists_signed_period_lift_of_homotopic_homeomorph f q Hq
  let N : C(ℝ, ℝ) := ⟨fun t => (n : ℝ) * t, by fun_prop⟩
  have hN (t : ℝ) : (N t : AddCircle p) = n • (t : AddCircle p) := by
    change (((n : ℝ) * t : ℝ) : AddCircle p) = _
    rw [← nsmul_eq_mul, coe_nsmul]
  have hdis := lift_period_displacement_eq_of_homotopy f
    ⟨fun z => n • z, by fun_prop⟩ Hn L N hL hN
  change L p - L 0 = (n : ℝ) * p - (n : ℝ) * 0 at hdis
  have hp : 0 < p := Fact.out
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rcases hperiod with hpos | hneg
  · have h := hpos 0
    simp only [zero_add] at h
    have heq : (n : ℝ) = 1 := by nlinarith
    exact_mod_cast heq
  · have h := hneg 0
    simp only [zero_add] at h
    nlinarith

end AddCircle

namespace PoincareMT.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "P2" => (ℝ × ℝ)
local notation "Q2" => sphere (0 : V2) 1
local notation "Circle" => AddCircle (4 * (8 : ℝ))
local notation "Ann" => squareAnnulus 8 1

/-- The fixed square-rim parameter, with one period of length thirty-two. -/
noncomputable def annulusSquareRimParameter : Circle ≃ₜ Q2 :=
  (AddCircle.homeomorphAddCircle (4 * (8 : ℝ)) (4 * (2 : ℝ))
    (by norm_num) (by norm_num)).trans HamiltonIndexOne.squareCircle

/-- The actual radial coordinate of the given circle, in the fixed complete
square-rim parameter. -/
noncomputable def annulusRadialSquareRimMap (gamma : C(Q2, Ann)) : C(Circle, Circle) :=
  ⟨fun z => (annulusCylinderHomeomorph.symm (gamma (annulusSquareRimParameter z))).2,
    (annulusCylinderHomeomorph.symm.continuous.comp
      (gamma.continuous.comp annulusSquareRimParameter.continuous)).snd⟩

/-- The finite PL embedded circle itself constructs the radial homotopy to
an actual circle homeomorphism. No polygon or sign is supplied. -/
theorem exists_finitePL_essential_annulus_radial_homeomorph_homotopy
    (gamma : C(Q2, Ann)) (hinj : Function.Injective gamma)
    (f : V2 → P2) (hf : FinitePiecewiseAffineOn f Q2)
    (hvalue : ∀ x : Q2, f x = (gamma x : P2))
    (hdepth : ∀ x : Q2, -1 < depth 8 (gamma x : P2) ∧ depth 8 (gamma x : P2) < 1)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1) :
    ∃ q : Circle ≃ₜ Circle,
      Nonempty ((annulusRadialSquareRimMap gamma).Homotopy ⟨q, q.continuous⟩) := by
  obtain ⟨q, ⟨H⟩⟩ := exists_finitePL_essential_annulus_core_homotopy
    gamma hinj f hf hvalue hdepth hessential
  refine ⟨annulusSquareRimParameter.trans q, ⟨{
    toFun := fun z => (annulusCylinderHomeomorph.symm
      (H (z.1, annulusSquareRimParameter z.2))).2
    continuous_toFun := (annulusCylinderHomeomorph.symm.continuous.comp
      (H.continuous.comp (continuous_fst.prodMk
        (annulusSquareRimParameter.continuous.comp continuous_snd)))).snd
    map_zero_left := ?_
    map_one_left := ?_
  }⟩⟩
  · intro z
    exact congrArg (fun x => (annulusCylinderHomeomorph.symm x).2)
      (H.apply_zero (annulusSquareRimParameter z))
  · intro z
    rw [H.apply_one]
    change (annulusCylinderHomeomorph.symm
      (annulusCylinderHomeomorph (⟨1 / 2, by norm_num⟩,
        q (annulusSquareRimParameter z)))).2 = _
    rw [annulusCylinderHomeomorph.symm_apply_apply]
    rfl

/-- Every actual finite PL essential embedded annular circle has a real
radial lift with exactly one positive or negative period. -/
theorem exists_finitePL_essential_annulus_signed_radial_lift
    (gamma : C(Q2, Ann)) (hinj : Function.Injective gamma)
    (f : V2 → P2) (hf : FinitePiecewiseAffineOn f Q2)
    (hvalue : ∀ x : Q2, f x = (gamma x : P2))
    (hdepth : ∀ x : Q2, -1 < depth 8 (gamma x : P2) ∧ depth 8 (gamma x : P2) < 1)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1) :
    ∃ L : C(ℝ, ℝ),
      (∀ t, (L t : Circle) = annulusRadialSquareRimMap gamma (t : Circle)) ∧
      ((∀ t, L (t + 32) = L t + 32) ∨ (∀ t, L (t + 32) = L t - 32)) := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨q, ⟨H⟩⟩ := exists_finitePL_essential_annulus_radial_homeomorph_homotopy
    gamma hinj f hf hvalue hdepth hessential
  obtain ⟨L, hL, hperiod⟩ := AddCircle.exists_signed_period_lift_of_homotopic_homeomorph
    (annulusRadialSquareRimMap gamma) q H
  refine ⟨L, hL, ?_⟩
  simpa only [show (4 : ℝ) * 8 = 32 by norm_num] using hperiod

/-- A positive multiple traversal cannot be the radial class of the actual
embedded essential circle unless that multiplicity is one. -/
theorem finitePL_essential_annulus_positive_degree_eq_one
    (gamma : C(Q2, Ann)) (hinj : Function.Injective gamma)
    (f : V2 → P2) (hf : FinitePiecewiseAffineOn f Q2)
    (hvalue : ∀ x : Q2, f x = (gamma x : P2))
    (hdepth : ∀ x : Q2, -1 < depth 8 (gamma x : P2) ∧ depth 8 (gamma x : P2) < 1)
    (hessential : FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk (squareRimLoop.map gamma.continuous)) ≠ 1)
    (n : ℕ) (hn : 0 < n)
    (Hn : (annulusRadialSquareRimMap gamma).Homotopy
      ⟨fun z => n • z, by fun_prop⟩) : n = 1 := by
  let : Fact (0 < 4 * (8 : ℝ)) := ⟨by norm_num⟩
  obtain ⟨q, ⟨Hq⟩⟩ := exists_finitePL_essential_annulus_radial_homeomorph_homotopy
    gamma hinj f hf hvalue hdepth hessential
  exact AddCircle.nat_eq_one_of_homotopic_homeomorph
    (annulusRadialSquareRimMap gamma) q Hq n hn Hn

end PoincareMT.M76.Dehn
