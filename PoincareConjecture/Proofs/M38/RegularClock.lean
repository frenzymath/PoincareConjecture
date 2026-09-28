import PoincareConjecture.Definitions.Ch11.BlowupLimits
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M38

theorem exists_smooth_unit_clock (Q : GeneralizedSliceCarrier)
    (f : Q.carrier → ℝ) (hf : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ f)
    (hreg : ∀ x, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x ≠ 0) :
    ∃ X : (x : Q.carrier) → TangentSpace (𝓡 3) x,
      ContMDiff (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% X) ∧
      ∀ x, mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x (X x) = 1 := by
  classical
  let : LocallyCompactSpace Q.carrier :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin 3)) Q.carrier
  let t (x : Q.carrier) : Set (TangentSpace (𝓡 3) x) :=
    {v | mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x v = 1}
  have hconv (x : Q.carrier) : Convex ℝ (t x) := by
    intro v hv w hw a b _ _ hab
    change mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x (a • v + b • w) = 1
    rw [map_add, map_smul, map_smul, hv, hw]
    simpa only [smul_eq_mul, mul_one] using hab
  have hlocal (x : Q.carrier) :
      ∃ U ∈ 𝓝 x, ∃ X : (y : Q.carrier) → TangentSpace (𝓡 3) y,
        ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% X) U ∧
        ∀ y ∈ U, X y ∈ t y := by
    obtain ⟨w, hw⟩ : ∃ w : TangentSpace (𝓡 3) x,
        mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f x w ≠ 0 := by
      by_contra h
      push Not at h
      exact hreg x (ContinuousLinearMap.ext h)
    let e := trivializationAt (EuclideanSpace ℝ (Fin 3)) (TangentSpace (𝓡 3)) x
    have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
    let v := (e ⟨x, w⟩).2
    let Y (y : Q.carrier) : TangentSpace (𝓡 3) y := e.symm y v
    have hYx : Y x = w := e.symm_apply_apply_mk hx w
    have hY : ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% Y) e.baseSet := by
      apply e.contMDiffOn_section_baseSet_iff.mpr
      apply contMDiffOn_const.congr
      intro y hy
      change (e ⟨y, e.symm y v⟩).2 = v
      rw [e.apply_mk_symm hy]
    let d (y : Q.carrier) : ℝ := mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f y (Y y)
    have hd : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞ d e.baseSet :=
      (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp_contMDiffOn
        ((hf.contMDiff_tangentMap (m := ∞) (by simp)).comp_contMDiffOn hY)
    have hdx : d x ≠ 0 := by simpa only [d, hYx] using hw
    let U := e.baseSet ∩ {y | d y ≠ 0}
    have hU : U ∈ 𝓝 x := inter_mem (e.open_baseSet.mem_nhds hx)
      ((hd.continuousOn.continuousAt (e.open_baseSet.mem_nhds hx)).preimage_mem_nhds
        (isOpen_compl_singleton.mem_nhds hdx))
    refine ⟨U, hU, fun y => (d y)⁻¹ • Y y, ?_, ?_⟩
    · exact ((hd.mono inter_subset_left).inv₀ (fun y hy => hy.2)).smul_section
        (hY.mono inter_subset_left)
    · intro y hy
      change mfderiv (𝓡 3) 𝓘(ℝ, ℝ) f y ((d y)⁻¹ • Y y) = 1
      rw [map_smul]
      exact inv_mul_cancel₀ hy.2
  obtain ⟨X, hX⟩ := exists_contMDiffSection_forall_mem_convex_of_local
    (𝓡 3) (n := ⊤) (TangentSpace (𝓡 3) : Q.carrier → Type) t hconv hlocal
  exact ⟨X, X.contMDiff, hX⟩

end PoincareConjecture.M38
