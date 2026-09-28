import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.PeriodicCircleShift
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.LocalConeWeakFilling
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.CurveTraceFundamental

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "circleMu" => volume.restrict (Icc (0 : ℝ) curvePeriod)

theorem m64Periodic_H1_shift
    (w : ℕ → ℝ → E) (hw : ∀ j, ContDiff ℝ 1 (w j))
    (hwp : ∀ j, Function.Periodic (w j) curvePeriod)
    (U v : ℝ → E) (hUp : Function.Periodic U curvePeriod)
    (hvp : Function.Periodic v curvePeriod) (hv : MemLp v 2 circleMu)
    (huni : TendstoUniformlyOn w U atTop (Icc (0 : ℝ) curvePeriod))
    (hder : Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
      ‖deriv (w j) x - v x‖ ^ 2) atTop (𝓝 0)) (a : ℝ) :
    MemLp (fun x => v (x + a)) 2 circleMu ∧
      TendstoUniformlyOn (fun j x => w j (x + a)) (fun x => U (x + a))
        atTop (Icc (0 : ℝ) curvePeriod) ∧
      Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
        ‖deriv (fun t => w j (t + a)) x - v (x + a)‖ ^ 2) atTop (𝓝 0) ∧
      (∀ x ∈ Icc (0 : ℝ) curvePeriod,
        U (x + a) - U a = ∫ t in (0 : ℝ)..x, v (t + a)) ∧
      (∫ x in Icc (0 : ℝ) curvePeriod, ‖v (x + a)‖ ^ 2) =
        ∫ x in Icc (0 : ℝ) curvePeriod, ‖v x‖ ^ 2 := by
  have hT : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hva := m64Periodic_memLp_two_shift hT hvp hv a
  have hglobal := m64Periodic_tendstoUniformly hwp hUp huni
  have hunia : TendstoUniformlyOn (fun j x => w j (x + a)) (fun x => U (x + a))
      atTop (Icc (0 : ℝ) curvePeriod) :=
    (hglobal.comp (fun x => x + a)).tendstoUniformlyOn
  have hperiod (j : ℕ) : Function.Periodic (fun x => ‖deriv (w j) x - v x‖ ^ 2)
      curvePeriod := by
    intro x
    dsimp only
    rw [m64Periodic_deriv (hwp j) x, hvp x]
  have herror (j : ℕ) : (∫ x in Icc (0 : ℝ) curvePeriod,
      ‖deriv (fun t => w j (t + a)) x - v (x + a)‖ ^ 2) =
        ∫ x in Icc (0 : ℝ) curvePeriod, ‖deriv (w j) x - v x‖ ^ 2 := by
    simp_rw [deriv_comp_add_const]
    exact m64Periodic_integral_shift hT (hperiod j) a
  have hdera : Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
      ‖deriv (fun t => w j (t + a)) x - v (x + a)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [herror] using hder
  have hwa (j : ℕ) : ContDiff ℝ 1 (fun t => w j (t + a)) :=
    (hw j).comp (contDiff_id.add contDiff_const)
  refine ⟨hva, hunia, hdera, ?_, ?_⟩
  · have hh := m64Curve_trace_fundamental_of_strong_approximation
      (fun j t => w j (t + a)) (fun j => deriv (fun t => w j (t + a)))
      (fun j => (hwa j).continuous_deriv (by simp))
      (fun j t => ((hwa j).differentiable (by simp) t).hasDerivAt) hT
      (fun t => v (t + a)) (fun t => U (t + a)) hva hdera hunia
    simpa only [zero_add] using hh
  · exact m64Periodic_integral_shift (f := fun x => ‖v x‖ ^ 2) hT
      (fun x => congrArg (fun z : E => ‖z‖ ^ 2) (hvp x)) a

end PoincareConjecture
