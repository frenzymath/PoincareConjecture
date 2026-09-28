import PoincareConjecture.Proofs.M05.Geometry.RicciFlow.Pinching.Parabolic
import PoincareConjecture.Proofs.M05.Analysis.ODE.ParameterExistence
import Mathlib.Algebra.Star.Module

namespace Poincare.HamiltonIvey

noncomputable section

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

local instance : NormedAddCommGroup (E →L[ℝ] E) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace
local instance : TopologicalSpace (E →L[ℝ] E) :=
  (inferInstance : MetricSpace (E →L[ℝ] E)).toUniformSpace.toTopologicalSpace
local instance : AddCommGroup (E →L[ℝ] E) :=
  (inferInstance : NormedAddCommGroup (E →L[ℝ] E)).toAddCommGroup
local instance : Module ℝ (E →L[ℝ] E) :=
  (inferInstance : NormedSpace ℝ (E →L[ℝ] E)).toModule

private theorem endomorphismReaction_symmetric {A : E →ₗ[ℝ] E}
    (hA : A.IsSymmetric) : (endomorphismReaction A).IsSymmetric := by
  unfold endomorphismReaction
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  exact ((hA.mul_of_commute hA (Commute.refl A)).smul (by simp) |>.sub
    (hA.smul (by simp))).add (LinearMap.IsSymmetric.one.smul (by simp))

private theorem exists_symmetric_reaction_curve
    {A : E →L[ℝ] E} (hA : A.toLinearMap.IsSymmetric) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → E →L[ℝ] E,
      γ 0 = A ∧
      (∀ t, (γ t).toLinearMap.IsSymmetric) ∧
      ∀ t ∈ Icc (-ε) ε, HasDerivWithinAt γ
        (endomorphismReaction (γ t).toLinearMap).toContinuousLinearMap (Icc (-ε) ε) t := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let S := ↥(selfAdjoint.submodule ℝ (E →L[ℝ] E))
  let ι : S →L[ℝ] (E →L[ℝ] E) := (selfAdjoint.submodule ℝ (E →L[ℝ] E)).subtypeL
  let π : (E →L[ℝ] E) →L[ℝ] S :=
    (show (E →L[ℝ] E) →ₗ[ℝ] S from selfAdjointPart ℝ).toContinuousLinearMap
  let f : S → S := fun B => π (endomorphismReaction (ι B).toLinearMap).toContinuousLinearMap
  have hf : ContDiff ℝ 1 f :=
    (ContinuousLinearMap.contDiff π).comp ((contDiff_continuousEndomorphismReaction.of_le
      (show (1 : WithTop ℕ∞) ≤ ∞ by norm_num)).comp ι.contDiff)
  have hforget (B : S) : ι (f B) =
      (endomorphismReaction (ι B).toLinearMap).toContinuousLinearMap := by
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (endomorphismReaction_symmetric
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp B.property))).coe_selfAdjointPart_apply ℝ
  let A₀ : S := ⟨A, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hA⟩
  obtain ⟨r, ε, Z, L, hr, hε, hZ, _⟩ :=
    Poincare.ODE.Parameter.exists_forall_hasDerivWithinAt_lipschitzOnWith_of_contDiffAt
      (hf.contDiffAt (x := A₀)) (U := univ) (Filter.univ_mem)
  obtain ⟨hZ₀, hd, _⟩ := hZ A₀ (Metric.mem_closedBall_self hr.le)
  refine ⟨ε, hε, fun t => ι (Z A₀ t), ?_, ?_, ?_⟩
  · simp only [hZ₀]
    rfl
  · intro t
    exact ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (Z A₀ t).property
  · intro t ht
    convert! ι.hasFDerivAt.comp_hasDerivWithinAt t (hd t ht) using 1
    exact (hforget _).symm

theorem scaled_reaction_support_nonpos
    (hn : Module.finrank ℝ E = 3) {t : ℝ} (ht : 0 ≤ t)
    {A : E →L[ℝ] E} (hA : A ∈ continuousRegion hn 0)
    (l : (E →L[ℝ] E) →L[ℝ] ℝ)
    (hsupport : ∀ B ∈ continuousRegion hn 0, l (B - A) ≤ 0) :
    l ((1 + t)⁻¹ • (A + (endomorphismReaction A.toLinearMap).toContinuousLinearMap)) ≤ 0 := by
  obtain ⟨ε, hε, γ, hγ₀, hsymm, hd⟩ := exists_symmetric_reaction_curve hA.1
  have hsub : Icc 0 ε ⊆ Icc (-ε) ε := Icc_subset_Icc (by linarith) le_rfl
  have hc : ContinuousOn γ (Icc 0 ε) :=
    fun s hs => ((hd s (hsub hs)).mono hsub).continuousWithinAt
  have hinv : ∀ s ∈ Icc 0 ε, (γ s).toLinearMap ∈ region hn s := by
    apply operator_reaction_invariance hn (A := fun s => (γ s).toLinearMap)
      (by norm_num) hε.le
      (fun v => (ContinuousLinearMap.apply ℝ E v).continuous.comp_continuousOn hc)
      (fun s _ => hsymm s)
    · intro s hs v
      have hds := (hd s (hsub (Ioo_subset_Icc_self hs))).hasDerivAt
        (Icc_mem_nhds (by linarith [hs.1]) hs.2)
      simpa using hds.clm_apply (hasDerivAt_const s v)
    · simpa only [hγ₀] using (mem_continuousRegion hn 0 A).mp hA
  have hcarrier : ∀ s ∈ Icc 0 ε, (1 + s) • γ s ∈ continuousRegion hn 0 := by
    intro s hs
    exact (region_scale_iff hn hs.1 (γ s).toLinearMap).mp (hinv s hs)
  have hd₀ : HasDerivAt γ
      (endomorphismReaction A.toLinearMap).toContinuousLinearMap 0 := by
    simpa only [hγ₀] using
      (hd 0 ⟨by linarith, hε.le⟩).hasDerivAt (Icc_mem_nhds (by linarith) hε)
  have hscaled : HasDerivAt (fun s => (1 + s) • γ s)
      (A + (endomorphismReaction A.toLinearMap).toContinuousLinearMap) 0 := by
    convert!
      ((hasDerivAt_const 0 (1 : ℝ)).add (hasDerivAt_id 0)).smul hd₀
      using 1
    simp [hγ₀, add_comm]
  have hscalar : HasDerivAt (fun s => l ((1 + s) • γ s - A))
      (l (A + (endomorphismReaction A.toLinearMap).toContinuousLinearMap)) 0 :=
    l.hasFDerivAt.comp_hasDerivAt 0 (hscaled.sub_const A)
  have hmax : IsMaxOn (fun s => l ((1 + s) • γ s - A)) (Icc 0 ε) 0 := by
    intro s hs
    change l ((1 + s) • γ s - A) ≤ l ((1 + 0) • γ 0 - A)
    simpa only [add_zero, one_smul, hγ₀, sub_self, map_zero] using
      hsupport _ (hcarrier s hs)
  have hcone : ε - 0 ∈ posTangentConeAt (Icc (0 : ℝ) ε) 0 :=
    sub_mem_posTangentConeAt_of_segment_subset
      ((convex_Icc 0 ε).segment_subset ⟨le_rfl, hε.le⟩ ⟨hε.le, le_rfl⟩)
  have h := hmax.localize.hasFDerivWithinAt_nonpos
    hscalar.hasDerivWithinAt.hasFDerivWithinAt hcone
  change (ε - 0) * l (A + (endomorphismReaction A.toLinearMap).toContinuousLinearMap) ≤ 0 at h
  have hnonpos : l (A + (endomorphismReaction A.toLinearMap).toContinuousLinearMap) ≤ 0 := by
    nlinarith
  rw [map_smul, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (by linarith)) hnonpos

end

end Poincare.HamiltonIvey
