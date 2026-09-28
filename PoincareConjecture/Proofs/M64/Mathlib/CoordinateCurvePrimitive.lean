import PoincareConjecture.Proofs.M64.Mathlib.VectorIntegralAbsoluteContinuity
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations













noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter MeasureTheory
open scoped Topology

namespace PoincareConjecture






theorem m64Curve_vector_primitive {m : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (u d : ℝ → EuclideanSpace ℝ (Fin m)) (b0 b1 : EuclideanSpace ℝ (Fin m))
    (hd : MemLp d 2 (volume.restrict (Icc (0 : ℝ) T)))
    (hv : ∀ a : Fin m, ∃ v : ℝ → ℝ,
      (v =ᵐ[volume.restrict (Icc (0 : ℝ) T)] fun s => u s a) ∧
      v 0 = b0 a ∧ v T = b1 a ∧
      ∀ s ∈ Icc (0 : ℝ) T, v s - v 0 = ∫ t in (0 : ℝ)..s, d t a) :
    ∃ W : ℝ → EuclideanSpace ℝ (Fin m),
      AbsolutelyContinuousOnInterval W 0 T ∧
      (W =ᵐ[volume.restrict (Icc (0 : ℝ) T)] u) ∧
      W 0 = b0 ∧ W T = b1 ∧
      ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
        W t - W s = ∫ y in s..t, d y := by
  classical
  choose v hva hv0 hvT hvinc using hv
  have hi : IntervalIntegrable d volume 0 T :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr (hd.integrable (by norm_num))
  let W := fun s => b0 + ∫ t in (0 : ℝ)..s, d t
  have hconst : AbsolutelyContinuousOnInterval
      (fun _ : ℝ => b0) 0 T :=
    (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => b0)).contDiffOn.absolutelyContinuousOnInterval
  have hW : AbsolutelyContinuousOnInterval W 0 T :=
    hconst.add (intervalIntegral_vector_absolutelyContinuous hi left_mem_uIcc)
  have hcoord (s : ℝ) (hs : s ∈ Icc (0 : ℝ) T) (a : Fin m) : W s a = v a s := by
    let P := EuclideanSpace.proj (𝕜 := ℝ) a
    have his : IntervalIntegrable d volume 0 s :=
      hi.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hs))
    have hpi := P.intervalIntegral_comp_comm his
    change (∫ t in (0 : ℝ)..s, d t a) = (∫ t in (0 : ℝ)..s, d t) a at hpi
    have h := hvinc a s hs
    rw [hv0 a, hpi] at h
    change b0 a + (∫ t in (0 : ℝ)..s, d t) a = v a s
    linarith
  refine ⟨W, hW, ?_, by simp [W], ?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr hva, ae_restrict_mem measurableSet_Icc] with s hs hsI
    exact PiLp.ext (fun a => (hcoord s hsI a).trans (hs a))
  · exact PiLp.ext (fun a => (hcoord T ⟨hT, le_rfl⟩ a).trans (hvT a))
  · intro s hs t ht
    have his := hi.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc hs))
    have hit := hi.mono_set (uIcc_subset_uIcc left_mem_uIcc (Icc_subset_uIcc ht))
    dsimp only [W]
    rw [add_sub_add_left_eq_sub,
      intervalIntegral.integral_interval_sub_left hit his]

end PoincareConjecture
