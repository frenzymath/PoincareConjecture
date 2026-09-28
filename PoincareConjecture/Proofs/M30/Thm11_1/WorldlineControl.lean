import PoincareConjecture.Proofs.M30.Generalized.ScalarAlong
import PoincareConjecture.Proofs.M30.Mathlib.GuardedScalarComparison
import PoincareConjecture.Proofs.M30.Thm11_1.BoundedDistance














set_option autoImplicit false

open Filter Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

variable {S : GeneralizedBlowupSequence.{u}}
  {epsilon canonicalConstant kappa r₀ mu : ℝ}



theorem Cylinder.scalar_le_double_on_backward_interval
    (hC : RicciFlowCurvatureTheory.{u})
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    {k : ℕ} {C : GeneralizedSliceCarrier.{u}} {U : Set C.carrier}
    {tau D : ℝ} (htau : 0 ≤ tau) (hD : 4 ≤ D)
    (e : GeneralizedFlowCylinder (S.flow k) C (S.base k).1 (S.scale k)
      (Icc (-tau) 0) U)
    (x : C.carrier) (hx : x ∈ U)
    (hterminal : (S.flow k).scalar (e.pointMap 0 ⟨neg_nonpos.mpr htau, le_rfl⟩ x) ≤
      D * S.scale k)
    (htime : 8 * H.analytic_constant * D * tau ≤ 1) :
    ∀ s (hs : s ∈ Icc (-tau) 0),
      (S.flow k).scalar (e.pointMap s hs x) ≤ 2 * D * S.scale k := by
  classical
  let f : ℝ → ℝ := scalarAlong e x
  have hchoice (s : ℝ) : ∃ d : ℝ, s ∈ Icc (-tau) 0 →
      HasDerivWithinAt f d (Icc (-tau) 0) s ∧
        (4 * S.scale k ≤ f s →
          |d| ≤ H.analytic_constant / S.scale k * f s ^ 2) := by
    by_cases hs : s ∈ Icc (-tau) 0
    · obtain ⟨d, hd, hrate⟩ := exists_scalarAlong_deriv_bound hC H e hs hs.2 x hx
      exact ⟨d, fun _ => ⟨hd, hrate⟩⟩
    · exact ⟨0, fun hs' => (hs hs').elim⟩
  choose d hd using hchoice
  have hQ : 0 < S.scale k := S.base_scalar_pos k
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have htime' : 8 * (H.analytic_constant / S.scale k) * (D * S.scale k) *
      (0 - -tau) ≤ 1 := by
    calc
      8 * (H.analytic_constant / S.scale k) * (D * S.scale k) * (0 - -tau) =
          8 * H.analytic_constant * D * tau := by
        rw [zero_sub, neg_neg]
        field_simp
      _ ≤ 1 := htime
  have hzero : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨neg_nonpos.mpr htau, le_rfl⟩
  have hterminal' : f 0 ≤ D * S.scale k := by
    simpa only [f, scalarAlong_of_mem e x hzero] using hterminal
  have hbound := le_two_mul_of_abs_deriv_le_sq_above_backward
    (f := f) (f' := d) (div_pos H.analytic_constant_pos hQ) (mul_pos hDpos hQ)
    (mul_le_mul_of_nonneg_right hD hQ.le)
    (fun s hs => (hd s hs).1) hterminal' (fun s hs => (hd s hs).2) htime'
  intro s hs
  simpa only [f, scalarAlong_of_mem e x hs, mul_assoc] using hbound s hs




theorem exists_uniform_scalar_controlled_worldlines
    (hC : RicciFlowCurvatureTheory.{u})
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    (hbound : GeneralizedBlowupBoundedDistance S) (A : ℝ) (hA : 0 < A) :
    ∃ D : ℝ, 4 ≤ D ∧ ∃ tau : ℝ, 0 < tau ∧ ∀ᶠ k : ℕ in atTop,
      ∀ x ∈ S.baseBall k A,
        ∃ e : GeneralizedFlowCylinder (S.flow k) ((S.flow k).slice (S.base k).1)
          (S.base k).1 (S.scale k) (Icc (-tau) 0) ({x} : Set _),
          (∀ h₀, e.pointMap 0 h₀ x = (⟨(S.base k).1, x⟩ : (S.flow k).point)) ∧
            ∀ s (hs : s ∈ Icc (-tau) 0),
              (S.flow k).scalar (e.pointMap s hs x) ≤ 2 * D * S.scale k := by
  obtain ⟨D₀, _, hD₀⟩ := hbound A hA
  let D : ℝ := max 4 D₀
  have hD : 4 ≤ D := le_max_left _ _
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  obtain ⟨tau₀, htau₀, hworldlines⟩ := exists_uniform_backward_worldlines
    hbound H.mu_pos H.maximal_worldlines A hA
  have hden : 0 < 8 * H.analytic_constant * D := by
    exact mul_pos (mul_pos (by norm_num) H.analytic_constant_pos) hDpos
  let tau : ℝ := min tau₀ (1 / (8 * H.analytic_constant * D))
  have htau : 0 < tau := lt_min htau₀ (one_div_pos.mpr hden)
  have htime : 8 * H.analytic_constant * D * tau ≤ 1 := by
    have hle : tau ≤ 1 / (8 * H.analytic_constant * D) := min_le_right _ _
    simpa only [mul_comm] using (le_div_iff₀ hden).mp hle
  refine ⟨D, hD, tau, htau, ?_⟩
  filter_upwards [hD₀, hworldlines] with k hk hworld
  intro x hx
  obtain ⟨e₀, he₀⟩ := hworld x hx
  have htime_subset : Icc (-tau) 0 ⊆ Icc (-tau₀) 0 :=
    Icc_subset_Icc (neg_le_neg (min_le_left _ _)) le_rfl
  let e := Cylinder.restrict e₀ htime_subset Subset.rfl
  have hzero : ∀ h₀, e.pointMap 0 h₀ x = (⟨(S.base k).1, x⟩ : (S.flow k).point) :=
    fun h₀ => he₀ (htime_subset h₀)
  have hterminal : (S.flow k).scalar
      (e.pointMap 0 ⟨neg_nonpos.mpr htau.le, le_rfl⟩ x) ≤ D * S.scale k := by
    exact (congrArg (S.flow k).scalar (hzero _)).le.trans ((hk x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_right 4 D₀) (S.base_scalar_pos k).le))
  refine ⟨e, hzero, ?_⟩
  exact Cylinder.scalar_le_double_on_backward_interval hC H htau.le hD e x
    (mem_singleton x) hterminal htime




theorem exists_common_scalar_controlled_worldlines
    (hC : RicciFlowCurvatureTheory.{u})
    (H : M30CommonBlowupControls S epsilon canonicalConstant kappa r₀ mu)
    {D : ℝ} (hD : 4 ≤ D)
    (hterminal : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      ∀ x ∈ S.baseBall k A,
        (S.flow k).scalar ⟨(S.base k).1, x⟩ ≤ D * S.scale k) :
    ∃ tau : ℝ, 0 < tau ∧ ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      ∀ x ∈ S.baseBall k A,
        ∃ e : GeneralizedFlowCylinder (S.flow k) ((S.flow k).slice (S.base k).1)
          (S.base k).1 (S.scale k) (Icc (-tau) 0) ({x} : Set _),
          (∀ h₀, e.pointMap 0 h₀ x = (⟨(S.base k).1, x⟩ : (S.flow k).point)) ∧
            ∀ s (hs : s ∈ Icc (-tau) 0),
              (S.flow k).scalar (e.pointMap s hs x) ≤ 2 * D * S.scale k := by
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hden : 0 < 8 * H.analytic_constant * D :=
    mul_pos (mul_pos (by norm_num) H.analytic_constant_pos) hDpos
  let tau : ℝ := min (mu / D) (1 / (8 * H.analytic_constant * D))
  have htau : 0 < tau :=
    lt_min (div_pos H.mu_pos hDpos) (one_div_pos.mpr hden)
  have htime : 8 * H.analytic_constant * D * tau ≤ 1 := by
    have hle : tau ≤ 1 / (8 * H.analytic_constant * D) := min_le_right _ _
    simpa only [mul_comm] using (le_div_iff₀ hden).mp hle
  refine ⟨tau, htau, ?_⟩
  intro A hA
  filter_upwards [hterminal A hA, H.maximal_worldlines A hA] with k hbound hlines
  intro x hx
  obtain ⟨line⟩ := hlines x hx
  have htime_subset : Icc (-tau) 0 ⊆ line.maximal_interval := by
    apply Subset.trans _ line.requested_interval_subset
    have hle : tau ≤ m30BackwardDuration S k x mu :=
      (min_le_left _ _).trans
        (le_backwardDuration H.mu_pos.le (by linarith) (hbound x hx))
    exact Icc_subset_Icc (neg_le_neg hle) le_rfl
  let e := Cylinder.restrict line.embedding htime_subset Subset.rfl
  have hzero : ∀ h₀, e.pointMap 0 h₀ x = (⟨(S.base k).1, x⟩ : (S.flow k).point) :=
    fun _ => line.zero_identity
  refine ⟨e, hzero, ?_⟩
  apply Cylinder.scalar_le_double_on_backward_interval hC H htau.le hD e x
    (mem_singleton x) _ htime
  exact (congrArg (S.flow k).scalar (hzero _)).le.trans (hbound x hx)

end PoincareConjecture.M30
