import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold

namespace PoincareConjecture

theorem m64_exists_metric_eq_nhds_of_isClosed
    {n : ℕ} {S U : Set (EuclideanSpace ℝ (Fin n))}
    (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (B : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U)
    (hsymm : ∀ x ∈ U, ∀ v w, B x v w = B x w v)
    (hpos : ∀ x ∈ U, ∀ v, v ≠ 0 → 0 < B x v v) :
    ∃ (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) (_D : LeviCivitaData g),
      ∀ x ∈ S, g.euclideanCoefficients =ᶠ[𝓝 x] B := by
  obtain ⟨chi, hzero, hone, hchi⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓡 n) hU.isClosed_compl hS
      (show Disjoint Uᶜ S from disjoint_left.mpr (fun _ hx hs => hx (hSU hs)))
      (n := ⊤)
  let delta : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ := innerSL ℝ
  let C : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    fun x => chi x • B x + (1 - chi x) • delta
  have hCa (x v w : EuclideanSpace ℝ (Fin n)) :
      C x v w = chi x * B x v w + (1 - chi x) * inner ℝ v w := rfl
  have hchiSmooth : ContDiff ℝ ∞ (fun x => chi x) := chi.contMDiff.contDiff
  have hC : ContDiff ℝ ∞ C := by
    rw [contDiff_iff_contDiffAt]
    intro x
    have hfirst : ContDiffAt ℝ ∞ (fun y => chi y • B y) x := by
      by_cases hx : x ∈ U
      · exact hchiSmooth.contDiffAt.smul (hB.contDiffAt (hU.mem_nhds hx))
      · have hz : ∀ᶠ y in 𝓝 x, chi y = 0 := hzero.filter_mono (nhds_le_nhdsSet hx)
        apply (contDiffAt_const (c := (0 : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ))).congr_of_eventuallyEq
        filter_upwards [hz] with y hy
        simp only [hy, zero_smul]
    exact hfirst.add ((contDiffAt_const.sub hchiSmooth.contDiffAt).smul contDiffAt_const)
  have hzeroAt (x : EuclideanSpace ℝ (Fin n)) (hx : x ∉ U) : chi x = 0 :=
    hzero.self_of_nhdsSet x hx
  have hCs : ∀ x v w, C x v w = C x w v := by
    intro x v w
    rw [hCa, hCa]
    by_cases hx : x ∈ U
    · rw [hsymm x hx v w, real_inner_comm v w]
    · simp only [hzeroAt x hx, zero_mul, zero_add, sub_zero, one_mul, real_inner_comm]
  have hCp : ∀ x v, v ≠ 0 → 0 < C x v v := by
    intro x v hv
    rw [hCa]
    by_cases hc : chi x = 0
    · simpa only [hc, zero_mul, zero_add, sub_zero, one_mul] using real_inner_self_pos.mpr hv
    · have hx : x ∈ U := by
        by_contra hn
        exact hc (hzeroAt x hn)
      exact add_pos_of_pos_of_nonneg
        (mul_pos (lt_of_le_of_ne (hchi x).1 (Ne.symm hc)) (hpos x hx v hv))
        (mul_nonneg (sub_nonneg.mpr (hchi x).2) real_inner_self_nonneg)
  let g := RiemannianMetric.ofEuclideanCoefficients C hC hCs hCp
  refine ⟨g, g.euclideanLeviCivitaData, ?_⟩
  intro x hx
  have ho : ∀ᶠ y in 𝓝 x, chi y = 1 := hone.filter_mono (nhds_le_nhdsSet hx)
  filter_upwards [ho] with y hy
  change C y = B y
  simp only [C, hy, one_smul, sub_self, zero_smul, add_zero]

end PoincareConjecture
