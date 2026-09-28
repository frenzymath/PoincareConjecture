import PoincareConjecture.Proofs.M11.SpatialCalculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace TopologicalSpace.Opens

variable {E : Type*} [NormedAddCommGroup E] (U : Opens E)



noncomputable def affineShift (x : U) (v : E) : U := by
  classical
  exact if h : x.val + v ∈ U then ⟨x.val + v, h⟩ else x



theorem affineShift_val {x : U} {v : E} (h : x.val + v ∈ U) :
    (U.affineShift x v).val = x.val + v := by
  simp only [affineShift, dif_pos h]


theorem affineShift_zero (x : U) : U.affineShift x 0 = x := by
  apply Subtype.ext
  rw [U.affineShift_val (by rw [add_zero]; exact x.property), add_zero]



theorem affineShift_domain_isOpen : IsOpen {z : U × E | z.1.val + z.2 ∈ U} :=
  U.isOpen.preimage ((continuous_subtype_val.comp continuous_fst).add continuous_snd)

variable [NormedSpace ℝ E]



theorem affineShift_contMDiffOn :
    ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) ∞
      (fun z : U × E => U.affineShift z.1 z.2) {z | z.1.val + z.2 ∈ U} := by
  have hadd : ContMDiff ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) ∞
      (fun z : U × E => z.1.val + z.2) :=
    (contMDiff_subtype_val.comp contMDiff_fst).add contMDiff_snd
  have hval : ContMDiffOn ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) (𝓘(ℝ, E)) ∞
      (Subtype.val ∘ fun z : U × E => U.affineShift z.1 z.2)
      {z | z.1.val + z.2 ∈ U} :=
    hadd.contMDiffOn.congr (fun _ hz => U.affineShift_val hz)
  intro z hz
  exact (ContMDiffWithinAt.subtypeVal_comp_iff U _ _ z).mp (hval z hz)




theorem affineShift_parameter_contMDiffAt (x : U) (v : E) :
    ContMDiffAt (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) ∞ (fun r : ℝ => U.affineShift x (r • v)) 0 := by
  have hmem : (x, (0 : ℝ) • v) ∈ {z : U × E | z.1.val + z.2 ∈ U} := by
    change x.val + (0 : ℝ) • v ∈ U
    simpa only [zero_smul, add_zero] using x.property
  have hi : ContMDiff (𝓘(ℝ, ℝ)) ((𝓘(ℝ, E)).prod (𝓘(ℝ, E))) ∞
      (fun r : ℝ => (x, r • v)) :=
    contMDiff_const.prodMk (contDiff_id.smul contDiff_const).contMDiff
  exact ((U.affineShift_contMDiffOn _ hmem).contMDiffAt
    (U.affineShift_domain_isOpen.mem_nhds hmem)).comp 0 hi.contMDiffAt



theorem affineShift_parameter_mfderiv (x : U) (v : E) :
    mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun r : ℝ => U.affineShift x (r • v)) 0 (1 : ℝ) = v := by
  have hf := U.affineShift_parameter_contMDiffAt x v
  have hc : ContMDiff (𝓘(ℝ, E)) (𝓘(ℝ, E)) ∞ (Subtype.val : U → E) :=
    contMDiff_subtype_val
  have hd := ((hc.mdifferentiable (by simp) _).hasMFDerivAt.comp 0
    (hf.mdifferentiableAt (by simp)).hasMFDerivAt).hasFDerivAt.hasDerivAt
  have hpoly : HasDerivAt (fun r : ℝ => x.val + r • v) v 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x.val
  have hval : HasDerivAt (fun r : ℝ => (U.affineShift x (r • v)).val) v 0 := by
    apply hpoly.congr_of_eventuallyEq
    have hnear : {r : ℝ | x.val + r • v ∈ U} ∈ 𝓝 0 :=
      (U.isOpen.preimage (continuous_const.add (continuous_id.smul continuous_const))).mem_nhds
        (by
          change x.val + (0 : ℝ) • v ∈ U
          simpa only [zero_smul, add_zero] using x.property)
    filter_upwards [hnear] with r hr
    exact U.affineShift_val hr
  have h := hd.unique hval
  rw [PoincareConjecture.Proofs.M11.mfderiv_openSubtype_val] at h
  change mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun r : ℝ => U.affineShift x (r • v)) 0
    (1 : ℝ) = v at h
  exact h

end TopologicalSpace.Opens
