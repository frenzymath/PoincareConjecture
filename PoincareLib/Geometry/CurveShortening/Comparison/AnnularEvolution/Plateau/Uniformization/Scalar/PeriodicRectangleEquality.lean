import PoincareLib.Geometry.CurveShortening.Comparison.Annulus
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.Periodic

/-!
# Periodic rectangle equality on the entire horizontal strip

Equality on one closed angular fundamental rectangle and the actual
period identities imply equality on the full strip, including all seams.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M64Uniformization

/-- Equality on the closed fundamental rectangle and the actual period identities imply
equality throughout the entire closed radial strip. Source: Morgan--Tian (2007), Lemma
19.15, pp. 447-449; the explicit project construction is recorded in
`proof-work/tasks/M64/derivations/2026-09-25-actual-free-modulus-approximation.md`. -/
theorem scalar_periodic_eqOn_closedStrip {Y : Type*} {f g : LoopPlane → Y}
    (hf : ∀ x s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hg : ∀ x s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      g (annulusPoint (x + curvePeriod) s) = g (annulusPoint x s))
    (heq : EqOn f g m64AnnulusDomain) :
    EqOn f g {p | p 1 ∈ Icc (0 : ℝ) 1} := by
  intro p hp
  have hP : 0 < curvePeriod := by unfold curvePeriod; positivity
  let k : ℤ := ⌊p 0 / curvePeriod⌋
  let q := annulusPoint (p 0 - (k : ℝ) * curvePeriod) (p 1)
  have hlo : (k : ℝ) * curvePeriod ≤ p 0 :=
    (le_div_iff₀ hP).mp (Int.floor_le (p 0 / curvePeriod))
  have hhi : p 0 < ((k : ℝ) + 1) * curvePeriod :=
    (div_lt_iff₀ hP).mp (Int.lt_floor_add_one (p 0 / curvePeriod))
  have hq : q ∈ m64AnnulusDomain := by
    change 0 ≤ p 0 - (k : ℝ) * curvePeriod ∧
      p 0 - (k : ℝ) * curvePeriod ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1
    exact ⟨by linarith, by nlinarith, hp⟩
  have hfp : Function.Periodic (fun x : ℝ => f (annulusPoint x (p 1))) curvePeriod :=
    fun x => hf x (p 1) hp
  have hgp : Function.Periodic (fun x : ℝ => g (annulusPoint x (p 1))) curvePeriod :=
    fun x => hg x (p 1) hp
  have hpeta : annulusPoint (p 0) (p 1) = p := by
    ext i
    fin_cases i <;> rfl
  have hfq : f q = f p := by
    simpa only [q, hpeta] using hfp.sub_int_mul_eq (x := p 0) k
  have hgq : g q = g p := by
    simpa only [q, hpeta] using hgp.sub_int_mul_eq (x := p 0) k
  exact hfq.symm.trans ((heq hq).trans hgq)

end PoincareMT.M64Uniformization
