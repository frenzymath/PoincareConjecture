import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.Realization
import PoincareLib.Geometry.Spacetime.Realization.Box.Spatial.Calculus
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Affine shifts inside an open spatial subset

The local test variations in Morgan-Tian Lemma 6.4, pp. 107-108,
use ordinary affine shifts in a compatible spatial coordinate domain.
The total map below is smooth on its explicit admissible domain.
M11's open-subset inclusion derivative identifies its actual tangent.
-/

set_option autoImplicit false
-- Open-subset tangent fibers use the ambient normed vector model.
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace TopologicalSpace.Opens

variable {E : Type*} [NormedAddCommGroup E] (U : Opens E)

/-- The affine shift when it lies in the open spatial domain, with an
arbitrary totalization elsewhere, as used in Lemma 6.4, pp. 107-108. -/
noncomputable def affineShift (x : U) (v : E) : U := by
  classical
  exact if h : x.val + v ∈ U then ⟨x.val + v, h⟩ else x

/-- On the admissible domain the shifted point has the prescribed
ambient value, the coordinate perturbation in Lemma 6.4, pp. 107-108. -/
theorem affineShift_val {x : U} {v : E} (h : x.val + v ∈ U) :
    (U.affineShift x v).val = x.val + v := by
  simp only [affineShift, dif_pos h]

/-- Zero shift fixes every spatial point, Lemma 6.4, pp. 107-108. -/
theorem affineShift_zero (x : U) : U.affineShift x 0 = x := by
  apply Subtype.ext
  rw [U.affineShift_val (by rw [add_zero]; exact x.property), add_zero]

/-- Admissibility of a spatial shift is an open condition,
the parameter-buffer step of Lemma 6.4, pp. 107-108. -/
theorem affineShift_domain_isOpen : IsOpen {z : U × E | z.1.val + z.2 ∈ U} :=
  U.isOpen.preimage ((continuous_subtype_val.comp continuous_fst).add continuous_snd)

variable [NormedSpace ℝ E]

/-- The totalized shift is smooth on its admissible domain,
the local coordinate construction in Lemma 6.4, pp. 107-108. -/
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

/-- An affine spatial perturbation is smooth near parameter zero,
where its actual spatial basepoint lies in the open domain,
Lemma 6.4, pp. 107-108. -/
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

/-- The parameter tangent of an affine spatial shift is the chosen
vector, using M11's actual open-subset derivative, Lemma 6.4, pp. 107-108. -/
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
  rw [PoincareMT.Proofs.M11.mfderiv_openSubtype_val] at h
  change mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, E)) (fun r : ℝ => U.affineShift x (r • v)) 0
    (1 : ℝ) = v at h
  exact h

end TopologicalSpace.Opens
