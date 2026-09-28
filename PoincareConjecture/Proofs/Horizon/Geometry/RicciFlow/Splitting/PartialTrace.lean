import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.QuadraticDiscriminant









set_option autoImplicit false

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace Poincare.RicciFlow.Splitting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]


def frameTrace {k : ℕ} (A : E →L[ℝ] E) (v : Fin k → E) : ℝ :=
  ∑ i, inner ℝ (A (v i)) (v i)



def partialTrace (k : ℕ) (A : E →L[ℝ] E) : ℝ :=
  sInf (frameTrace A '' {v : Fin k → E | Orthonormal ℝ v})

theorem isCompact_orthonormal_frames (k : ℕ) :
    IsCompact {v : Fin k → E | Orthonormal ℝ v} := by
  have hclosed : IsClosed {v : Fin k → E | Orthonormal ℝ v} := by
    simp_rw [orthonormal_iff_ite, Set.ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_eq ((continuous_apply i).inner (continuous_apply j)) continuous_const
  apply (isCompact_univ_pi fun _ : Fin k => isCompact_closedBall (0 : E) 1).of_isClosed_subset
    hclosed
  intro v hv i _
  simp [Metric.mem_closedBall, dist_zero_right, hv.norm_eq_one i]

theorem exists_orthonormal_frame {k : ℕ} (hk : k ≤ Module.finrank ℝ E) :
    ∃ v : Fin k → E, Orthonormal ℝ v := by
  exact ⟨(stdOrthonormalBasis ℝ E) ∘ Fin.castLE hk,
    (stdOrthonormalBasis ℝ E).orthonormal.comp _ (Fin.castLE_injective hk)⟩

omit [FiniteDimensional ℝ E] in
theorem continuous_frameTrace {k : ℕ} (A : E →L[ℝ] E) :
    Continuous (frameTrace (k := k) A) := by
  unfold frameTrace
  exact continuous_finsetSum _ fun i _ =>
    (A.continuous.comp (continuous_apply i)).inner (continuous_apply i)

theorem exists_minimizing_frame {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    (A : E →L[ℝ] E) :
    ∃ v : Fin k → E, Orthonormal ℝ v ∧
      frameTrace A v = partialTrace k A := by
  obtain ⟨v, hv, hmin⟩ := (isCompact_orthonormal_frames (E := E) k).exists_isMinOn
    (exists_orthonormal_frame hk) (continuous_frameTrace A).continuousOn
  refine ⟨v, hv, ?_⟩
  apply le_antisymm
  · exact le_csInf ⟨_, mem_image_of_mem _ hv⟩ (by
      rintro _ ⟨w, hw, rfl⟩
      exact hmin hw)
  · exact csInf_le
      ((isCompact_orthonormal_frames (E := E) k).image (continuous_frameTrace A)).bddBelow
      (mem_image_of_mem _ hv)

theorem partialTrace_le_frameTrace {k : ℕ} (A : E →L[ℝ] E)
    {v : Fin k → E} (hv : Orthonormal ℝ v) :
    partialTrace k A ≤ frameTrace A v := by
  exact csInf_le
    ((isCompact_orthonormal_frames (E := E) k).image (continuous_frameTrace A)).bddBelow
    (mem_image_of_mem _ hv)

omit [FiniteDimensional ℝ E] in
theorem frameTrace_sub_bound {k : ℕ} (A B : E →L[ℝ] E)
    {v : Fin k → E} (hv : Orthonormal ℝ v) :
    |frameTrace A v - frameTrace B v| ≤ k * ‖A - B‖ := by
  have hterm (i : Fin k) : |inner ℝ ((A - B) (v i)) (v i)| ≤ ‖A - B‖ := by
    calc
      _ ≤ ‖(A - B) (v i)‖ * ‖v i‖ := abs_real_inner_le_norm _ _
      _ = ‖(A - B) (v i)‖ := by rw [hv.norm_eq_one, mul_one]
      _ ≤ ‖A - B‖ := by simpa [hv.norm_eq_one] using (A - B).le_opNorm (v i)
  calc
    _ = |∑ i, inner ℝ ((A - B) (v i)) (v i)| := by
      simp only [frameTrace, sub_apply, inner_sub_left,
        Finset.sum_sub_distrib]
    _ ≤ ∑ i, |inner ℝ ((A - B) (v i)) (v i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin k, ‖A - B‖ := Finset.sum_le_sum fun i _ => hterm i
    _ = k * ‖A - B‖ := by simp

theorem partialTrace_sub_bound {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    (A B : E →L[ℝ] E) :
    |partialTrace k A - partialTrace k B| ≤ k * ‖A - B‖ := by
  obtain ⟨v, hv, hvmin⟩ := exists_minimizing_frame hk A
  obtain ⟨w, hw, hwmin⟩ := exists_minimizing_frame hk B
  have hAw := partialTrace_le_frameTrace A hw
  have hBv := partialTrace_le_frameTrace B hv
  have hvbound := frameTrace_sub_bound A B hv
  have hwbound := frameTrace_sub_bound A B hw
  rw [hvmin] at hvbound
  rw [hwmin] at hwbound
  rw [abs_le] at hvbound hwbound ⊢
  constructor <;> linarith

theorem lipschitzWith_partialTrace {k : ℕ} (hk : k ≤ Module.finrank ℝ E) :
    LipschitzWith k (partialTrace (E := E) k) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  simpa only [dist_eq_norm, Real.norm_eq_abs, NNReal.coe_natCast] using
    partialTrace_sub_bound hk A B

theorem continuous_partialTrace {k : ℕ} (hk : k ≤ Module.finrank ℝ E) :
    Continuous (partialTrace (E := E) k) :=
  (lipschitzWith_partialTrace hk).continuous

omit [FiniteDimensional ℝ E] in
theorem positive_inner_self_eq_zero_iff {A : E →L[ℝ] E} (hA : A.IsPositive)
    (x : E) : inner ℝ (A x) x = 0 ↔ A x = 0 := by
  constructor
  · intro hx
    have hpoly (t : ℝ) :
        0 ≤ inner ℝ (A (A x)) (A x) * (t * t) +
          (2 * inner ℝ (A x) (A x)) * t + 0 := by
      have hpos := hA.inner_nonneg_left (t • A x + x)
      simp only [map_add, map_smul, inner_add_left, inner_add_right,
        real_inner_smul_left, real_inner_smul_right, hx,
        hA.inner_left_eq_inner_right (A x) x] at hpos
      nlinarith
    have hd := discrim_le_zero hpoly
    simp only [discrim, mul_zero, sub_zero] at hd
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    nlinarith [sq_nonneg (inner ℝ (A x) (A x))]
  · intro hx
    simp [hx]

theorem partialTrace_nonneg {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {A : E →L[ℝ] E} (hA : A.IsPositive) : 0 ≤ partialTrace k A := by
  obtain ⟨v, _, hmin⟩ := exists_minimizing_frame hk A
  rw [← hmin]
  exact Finset.sum_nonneg fun i _ => hA.inner_nonneg_left (v i)



theorem partialTrace_eq_zero_iff_kernel_frame {k : ℕ}
    (hk : k ≤ Module.finrank ℝ E) {A : E →L[ℝ] E} (hA : A.IsPositive) :
    partialTrace k A = 0 ↔
      ∃ v : Fin k → E, Orthonormal ℝ v ∧ ∀ i, A (v i) = 0 := by
  constructor
  · intro hzero
    obtain ⟨v, hv, hmin⟩ := exists_minimizing_frame hk A
    refine ⟨v, hv, fun i => (positive_inner_self_eq_zero_iff hA (v i)).mp ?_⟩
    have hsum : ∑ j, inner ℝ (A (v j)) (v j) = 0 := hmin.trans hzero
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => hA.inner_nonneg_left (v j))).mp hsum i (Finset.mem_univ i)
  · rintro ⟨v, hv, hker⟩
    apply le_antisymm _ (partialTrace_nonneg hk hA)
    have hframe : frameTrace A v = 0 := by simp [frameTrace, hker]
    simpa only [hframe] using partialTrace_le_frameTrace A hv


theorem partialTrace_eq_zero_iff {k : ℕ} (hk : k ≤ Module.finrank ℝ E)
    {A : E →L[ℝ] E} (hA : A.IsPositive) :
    partialTrace k A = 0 ↔ k ≤ Module.finrank ℝ A.ker := by
  rw [partialTrace_eq_zero_iff_kernel_frame hk hA]
  constructor
  · rintro ⟨v, hv, hker⟩
    let w : Fin k → A.ker := fun i => ⟨v i, hker i⟩
    have hw : Orthonormal ℝ w :=
      A.ker.subtypeₗᵢ.orthonormal_comp_iff.mp hv
    simpa using hw.linearIndependent.fintype_card_le_finrank
  · intro hdim
    obtain ⟨w, hw⟩ := exists_orthonormal_frame hdim
    exact ⟨fun i => (w i : E), A.ker.subtypeₗᵢ.orthonormal_comp_iff.mpr hw,
      fun i => (w i).property⟩

end Poincare.RicciFlow.Splitting
