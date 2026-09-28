import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Calculus.Deriv.MeanValue










set_option autoImplicit false

namespace AddCircle



theorem exists_continuous_real_lift {p : ℝ} {f : ℝ → AddCircle p} (hf : Continuous f) :
    ∃ L : ℝ → ℝ, Continuous L ∧ ∀ x, (L x : AddCircle p) = f x := by
  obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (f 0)
  obtain ⟨L, hL, _⟩ := (isCoveringMap_coe p).existsUnique_continuousMap_lifts ⟨f, hf⟩ 0 r hr
  exact ⟨L, L.continuous, congrFun hL.2⟩




theorem real_lift_period_shift {p tau : ℝ} {L : ℝ → ℝ} (hL : Continuous L)
    (hper : Function.Periodic (fun x => (L x : AddCircle p)) tau) :
    ∀ x, L (x + tau) = L x + (L tau - L 0) := by
  have hd : ((L tau - L 0 : ℝ) : AddCircle p) = 0 := by
    rw [coe_sub, show (L tau : AddCircle p) = (L 0 : AddCircle p) by
      simpa only [zero_add] using hper 0, sub_self]
  have heq := (isCoveringMap_coe p).eq_of_comp_eq
    (hL.comp (continuous_id.add continuous_const)) (hL.add continuous_const)
    (show (fun x => (L (x + tau) : AddCircle p)) =
      (fun x => ((L x + (L tau - L 0) : ℝ) : AddCircle p)) from by
        funext x
        rw [coe_add, hd, add_zero]
        exact hper x) 0 (by simp)
  exact congrFun heq




theorem real_lift_positive_degree {p tau : ℝ} (hp : 0 < p) (htau : 0 < tau)
    {L : ℝ → ℝ} (hL : Continuous L) (hderiv : ∀ x, 0 < deriv L x)
    (hper : Function.Periodic (fun x => (L x : AddCircle p)) tau) :
    ∃ N : ℕ, 0 < N ∧ ∀ x, L (x + tau) = L x + (N : ℝ) * p := by
  have hdpos : 0 < L tau - L 0 := sub_pos.mpr (strictMono_of_deriv_pos hderiv htau)
  have hd : ((L tau - L 0 : ℝ) : AddCircle p) = 0 := by
    rw [coe_sub, show (L tau : AddCircle p) = (L 0 : AddCircle p) by
      simpa only [zero_add] using hper 0, sub_self]
  obtain ⟨N, hN⟩ := (coe_eq_zero_of_pos_iff p hp hdpos).mp hd
  have hNpos : 0 < N := by
    by_contra! h
    have hzero : N = 0 := Nat.eq_zero_of_le_zero h
    subst N
    simp only [zero_smul] at hN
    linarith
  refine ⟨N, hNpos, fun x => ?_⟩
  rw [real_lift_period_shift hL hper x, ← hN, nsmul_eq_mul]




theorem exists_homotopy_lift_periodShift {p tau d : ℝ}
    (H : C(unitInterval × ℝ, AddCircle p)) (L0 : C(ℝ, ℝ))
    (hzero : ∀ x, H (0, x) = (L0 x : AddCircle p))
    (hper : ∀ s, Function.Periodic (fun x => H (s, x)) tau)
    (hshift : ∀ x, L0 (x + tau) = L0 x + d) :
    ∃ L : C(unitInterval × ℝ, ℝ),
      (∀ x, L (0, x) = L0 x) ∧ (∀ z, (L z : AddCircle p) = H z) ∧
        ∀ s x, L (s, x + tau) = L (s, x) + d := by
  let cov := isCoveringMap_coe p
  let L := cov.liftHomotopy H L0 hzero
  have hproj (z : unitInterval × ℝ) : (L z : AddCircle p) = H z :=
    congrFun (cov.liftHomotopy_lifts H L0 hzero) z
  have hstart (x : ℝ) : L (0, x) = L0 x := cov.liftHomotopy_zero H L0 hzero x
  have hd : (d : AddCircle p) = 0 := by
    have h := hper 0 0
    change H (0, 0 + tau) = H (0, 0) at h
    rw [hzero, hzero, hshift, coe_add] at h
    exact add_left_cancel (h.trans (add_zero _).symm)
  refine ⟨L, hstart, hproj, fun s x => ?_⟩
  have heq := cov.eq_of_comp_eq
    (L.continuous.comp (continuous_id.prodMk continuous_const))
    ((L.continuous.comp (continuous_id.prodMk continuous_const)).add continuous_const)
    (show (fun r : unitInterval => (L (r, x + tau) : AddCircle p)) =
      (fun r : unitInterval => ((L (r, x) + d : ℝ) : AddCircle p)) from by
        funext r
        rw [coe_add, hd, add_zero, hproj, hproj]
        exact hper r x) 0 (by
          change L (0, x + tau) = L (0, x) + d
          rw [hstart, hstart, hshift])
  exact congrFun heq s

end AddCircle
