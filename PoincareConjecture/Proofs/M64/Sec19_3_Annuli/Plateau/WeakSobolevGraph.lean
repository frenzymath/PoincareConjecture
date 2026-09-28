import PoincareConjecture.Proofs.M03.Existence.EuclideanGraphRellichNative
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Approximation

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak EuclideanGraphRellichNative

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

theorem m64WeakSobolev_mem_completedGraph
    {u : E → ℝ} (hw : MemW1pWitness 2 u univ)
    {K : Set E} (hK : IsCompact K) (hs : tsupport u ⊆ K) :
    ∃ (hu : MemLp u 2 volume)
      (hg : ∀ i : Fin d, MemLp (fun x => hw.weakGrad x i) 2 volume),
      (hu.toLp u, fun i => (hg i).toLp (fun x => hw.weakGrad x i)) ∈
        closure (derivativeGraphSet (Metric.cthickening 1 K)) := by
  have hu : MemLp u 2 volume := by simpa using hw.memLp
  have hg (i : Fin d) : MemLp (fun x => hw.weakGrad x i) 2 volume := by
    simpa using hw.weakGrad_component_memLp i
  have hc : HasCompactSupport u := hK.of_isClosed_subset (isClosed_tsupport u) hs
  let hw' : MemW1pWitness (ENNReal.ofReal (2 : ℝ)) u univ :=
    { memLp := by simpa using hw.memLp
      weakGrad := hw.weakGrad
      weakGrad_component_memLp := fun i => by simpa using hw.weakGrad_component_memLp i
      isWeakGrad := hw.isWeakGrad }
  obtain ⟨f, hf, hfc, hfs, hfu, hfg⟩ :=
    exists_smooth_compactSupport_W1p_approx_univ (by norm_num : (1 : ℝ) < 2) hw' hc
  have hfl (j : ℕ) : MemLp (f j) 2 volume :=
    (hf j).continuous.memLp_of_hasCompactSupport (hfc j)
  have hgl (j : ℕ) (i : Fin d) : MemLp
      (fun x => fderiv ℝ (f j) x (EuclideanSpace.single i 1)) 2 volume :=
    (((hf j).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hfc j).fderiv_apply ℝ _)
  have hsupport (j : ℕ) : tsupport (f j) ⊆ Metric.cthickening 1 K := by
    have hsub := hfs j
    change tsupport (f j) ⊆ Metric.cthickening (((j : ℝ) + 1)⁻¹) (tsupport u) at hsub
    have hr : ((j : ℝ) + 1)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity : 0 < (j : ℝ) + 1)]
      linarith [Nat.cast_nonneg (α := ℝ) j]
    apply hsub.trans
    exact (Metric.cthickening_subset_of_subset _ hs).trans
      (Metric.cthickening_mono hr K)
  let F (j : ℕ) : GraphAmbient d :=
    ((hfl j).toLp (f j), fun i => (hgl j i).toLp
      (fun x => fderiv ℝ (f j) x (EuclideanSpace.single i 1)))
  have hF (j : ℕ) : F j ∈ derivativeGraphSet (Metric.cthickening 1 K) := by
    refine ⟨f j, (hf j).of_le (by simp), hfl j, hgl j, ?_, rfl, fun _ => rfl⟩
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hsupport j h))
  have hval : Tendsto (fun j => (hfl j).toLp (f j)) atTop (𝓝 (hu.toLp u)) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hfl u hu).mpr
    simpa only [ENNReal.ofReal_ofNat, Pi.sub_def] using hfu
  have hgrad (i : Fin d) : Tendsto
      (fun j => (hgl j i).toLp (fun x => fderiv ℝ (f j) x (EuclideanSpace.single i 1)))
      atTop (𝓝 ((hg i).toLp (fun x => hw.weakGrad x i))) := by
    apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun j => hgl j i) _ (hg i)).mpr
    simpa only [ENNReal.ofReal_ofNat, Pi.sub_def, hw'] using hfg i
  refine ⟨hu, hg, mem_closure_of_tendsto (hval.prodMk_nhds (tendsto_pi_nhds.mpr hgrad)) ?_⟩
  exact Eventually.of_forall hF

theorem m64WeakSobolev_l2_isCompact
    (u : ℕ → E → ℝ) (hw : ∀ j, MemW1pWitness 2 (u j) univ)
    {K : Set E} (hK : IsCompact K) (hs : ∀ j, tsupport (u j) ⊆ K)
    (hu : ∀ j, MemLp (u j) 2 volume)
    (hg : ∀ j (i : Fin d), MemLp (fun x => (hw j).weakGrad x i) 2 volume)
    {R : ℝ} (hR : 0 ≤ R) (hval : ∀ j, ‖(hu j).toLp (u j)‖ ≤ R)
    (hgrad : ∀ j i, ‖(hg j i).toLp (fun x => (hw j).weakGrad x i)‖ ≤ R) :
    IsCompact (closure (range (fun j => (hu j).toLp (u j)))) := by
  have hc := isCompact_closure_completedGraph_value (hK.cthickening (r := 1)) hR
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro _ ⟨j, rfl⟩
  refine ⟨((hu j).toLp (u j), fun i => (hg j i).toLp
    (fun x => (hw j).weakGrad x i)), ⟨?_, ?_⟩, rfl⟩
  · obtain ⟨hu', hg', hmem⟩ := m64WeakSobolev_mem_completedGraph (hw j) hK (hs j)
    exact hmem
  · rw [Metric.mem_closedBall, dist_zero_right, norm_prod_le_iff]
    exact ⟨hval j, (pi_norm_le_iff_of_nonneg hR).mpr (hgrad j)⟩

end PoincareConjecture
