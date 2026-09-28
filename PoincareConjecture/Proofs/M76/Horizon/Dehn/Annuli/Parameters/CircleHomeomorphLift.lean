import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Isotopy.Mathlib.RelativeCircleLift
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Algebra.Module.LocallyConvex

set_option autoImplicit false
open Set

namespace AddCircle

variable {p : ℝ} [Fact (0 < p)]

omit [Fact (0 < p)] in
theorem exists_real_homeomorph_lift (q : AddCircle p ≃ₜ AddCircle p)
    (b : ℝ) (hb : (b : AddCircle p) = q 0) :
    ∃ L : ℝ ≃ₜ ℝ, L 0 = b ∧ ∀ t, (L t : AddCircle p) = q (t : AddCircle p) := by
  let cov := isCoveringMap_coe p
  obtain ⟨L, ⟨hL0, hL⟩, _⟩ := cov.existsUnique_continuousMap_lifts
    ⟨fun t : ℝ ↦ q (t : AddCircle p), q.continuous.comp (AddCircle.continuous_mk' p)⟩
    0 b (by exact hb)
  have hLt (t : ℝ) : (L t : AddCircle p) = q (t : AddCircle p) := congrFun hL t
  obtain ⟨K, ⟨hK0, hK⟩, _⟩ := cov.existsUnique_continuousMap_lifts
    ⟨fun t : ℝ ↦ q.symm (t : AddCircle p), q.symm.continuous.comp (AddCircle.continuous_mk' p)⟩
    b 0 (by change (0 : AddCircle p) = q.symm (b : AddCircle p); rw [hb, q.symm_apply_apply])
  have hKt (t : ℝ) : (K t : AddCircle p) = q.symm (t : AddCircle p) := congrFun hK t
  have hKL : (fun t ↦ K (L t)) = id := cov.eq_of_comp_eq
    (K.continuous.comp L.continuous) continuous_id (by ext t; simp [hKt, hLt])
    0 (by rw [hL0, hK0]; rfl)
  have hLK : (fun t ↦ L (K t)) = id := cov.eq_of_comp_eq
    (L.continuous.comp K.continuous) continuous_id (by ext t; simp [hKt, hLt])
    b (by rw [hK0, hL0]; rfl)
  exact ⟨{
    toFun := L
    invFun := K
    left_inv := congrFun hKL
    right_inv := congrFun hLK
    continuous_toFun := L.continuous
    continuous_invFun := K.continuous }, hL0, hLt⟩

theorem add_period_of_strictMono_lift {L : ℝ → ℝ}
    (hL : Continuous L) (hm : StrictMono L)
    (hperiod : ∀ t, (L (t + p) : AddCircle p) = (L t : AddCircle p))
    (hinj : ∀ s t, (L s : AddCircle p) = (L t : AddCircle p) →
      (s : AddCircle p) = (t : AddCircle p)) :
    ∀ t, L (t + p) = L t + p := by
  have hp := Fact.out (p := 0 < p)
  intro t
  have hz : ((L (t + p) - L t : ℝ) : AddCircle p) = 0 := by
    rw [coe_sub, hperiod, sub_self]
  obtain ⟨n, hn⟩ := (coe_eq_zero_iff p).mp hz
  rw [zsmul_eq_mul] at hn
  have hnpos : (0 : ℝ) < n := by
    have hlt := hm (show t < t + p by linarith)
    nlinarith
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (show (1 : ℤ) ≤ n by
      exact Int.add_one_le_iff.mpr (by exact_mod_cast hnpos))
  have hlow : L t + p ≤ L (t + p) := by nlinarith
  apply le_antisymm _ hlow
  by_contra h
  have hhigh : L t + p < L (t + p) := lt_of_not_ge h
  obtain ⟨u, hu, hLu⟩ := intermediate_value_Ioo
    (show t ≤ t + p by linarith) hL.continuousOn
    (show L t + p ∈ Ioo (L t) (L (t + p)) from ⟨by linarith, hhigh⟩)
  have hueq : (u : AddCircle p) = (t : AddCircle p) := hinj u t (by
    rw [hLu, coe_add, coe_period, add_zero])
  have huz : ((u - t : ℝ) : AddCircle p) = 0 := by rw [coe_sub, hueq, sub_self]
  obtain ⟨k, hk⟩ := (coe_eq_zero_iff p).mp huz
  rw [zsmul_eq_mul] at hk
  have hk0 : (0 : ℝ) < k := by nlinarith [hu.1]
  have hk1 : (k : ℝ) < 1 := by nlinarith [hu.2]
  have : (0 : ℤ) < k := by exact_mod_cast hk0
  have : (k : ℤ) < 1 := by exact_mod_cast hk1
  omega

theorem real_homeomorph_lift_orientation (q : AddCircle p ≃ₜ AddCircle p)
    (L : ℝ ≃ₜ ℝ) (hL : ∀ t, (L t : AddCircle p) = q (t : AddCircle p)) :
    (StrictMono L ∧ ∀ t, L (t + p) = L t + p) ∨
      (StrictAnti L ∧ ∀ t, L (t + p) = L t - p) := by
  have hperiod (t : ℝ) : (L (t + p) : AddCircle p) = (L t : AddCircle p) := by
    rw [hL, hL, coe_add, coe_period, add_zero]
  have hinj (s t : ℝ) (h : (L s : AddCircle p) = (L t : AddCircle p)) :
      (s : AddCircle p) = (t : AddCircle p) := by
    rw [hL, hL] at h
    exact q.injective h
  rcases L.continuous.strictMono_of_inj L.injective with hm | hm
  · exact Or.inl ⟨hm, add_period_of_strictMono_lift L.continuous hm hperiod hinj⟩
  · right
    refine ⟨hm, ?_⟩
    have hper (t : ℝ) : (L (-(t + p)) : AddCircle p) = (L (-t) : AddCircle p) := by
      simp only [hL, neg_add, coe_add, coe_neg, coe_period, neg_zero, add_zero]
    have hinv (s t : ℝ) (h : (L (-s) : AddCircle p) = (L (-t) : AddCircle p)) :
        (s : AddCircle p) = (t : AddCircle p) := by
      have hh := hinj (-s) (-t) h
      simpa only [coe_neg, neg_inj] using hh
    have hpos := add_period_of_strictMono_lift (L.continuous.comp continuous_neg)
      (show StrictMono (fun t : ℝ ↦ L (-t)) from fun _ _ hab ↦ hm (neg_lt_neg hab)) hper hinv
    intro t
    have hh := hpos (-(t + p))
    have heq : - (-(t + p) + p) = t := by ring
    simp only [Function.comp_apply] at hh
    rw [heq, neg_neg] at hh
    linarith

end AddCircle
