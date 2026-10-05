import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Lipschitz.RectangleFTC
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Weak.DerivativeClosure
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Actual weak columns of a Lipschitz observed annulus

Scalar Lipschitz extensions identify the actual derivatives with weak
partials. Finite-dimensional coordinate integration then gives L2 columns.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal

namespace PoincareMT

open Poincare.Analysis.Sobolev.Weak

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

/-- The actual partial derivative of a Lipschitz scalar annulus is its weak derivative on
the open rectangle. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64_lipschitz_scalar_weak_partial {f : LoopPlane → ℝ} {K : ℝ≥0}
    (hf : LipschitzOnWith K f m64AnnulusDomain) (i : Fin 2) :
    HasWeakPartialDeriv i (fun p => fderiv ℝ f p (EuclideanSpace.single i 1)) f S := by
  obtain ⟨F, hF, heq⟩ := hf.extend_real
  have hv : F =ᵐ[mu] f := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet] with p hp
    exact (heq (interior_subset hp)).symm
  have hd : (fun p => lineDeriv ℝ F p (EuclideanSpace.single i 1)) =ᵐ[mu]
      (fun p => fderiv ℝ f p (EuclideanSpace.single i 1)) := by
    filter_upwards [ae_restrict_mem isOpen_interior.measurableSet,
      ae_restrict_of_ae (hF.ae_differentiableAt (μ := volume))] with p hp hdp
    have hnear : f =ᶠ[𝓝 p] F := by
      filter_upwards [isOpen_interior.mem_nhds hp] with q hq
      exact heq (interior_subset hq)
    rw [hdp.lineDeriv_eq_fderiv, hnear.fderiv_eq]
  exact m64WeakPartialDeriv_ae_congr hv hd
    (hasWeakPartialDeriv_lineDeriv_of_lipschitz hF i)

/-- An actual Lipschitz observed annulus belongs to L2 on the open rectangle. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64_lipschitz_memLp_two
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : LoopPlane → F} {K : ℝ≥0} (hf : LipschitzOnWith K f m64AnnulusDomain) :
    MemLp f 2 mu := by
  apply (memLp_two_iff_integrable_sq_norm
    ((hf.continuousOn.mono interior_subset).aestronglyMeasurable
      isOpen_interior.measurableSet)).mpr
  exact (hf.continuousOn.norm.pow 2).integrableOn_compact
    m64AnnulusDomain_isCompact |>.mono_set interior_subset

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Coordinate projection preserves the actual annular Lipschitz bound with its
operator-norm factor. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64_lipschitz_coordinate {f : LoopPlane → E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f m64AnnulusDomain) (b : Fin m) :
    LipschitzOnWith
      (‖PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) b‖₊ * K)
      (fun p => f p b) m64AnnulusDomain :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) b).lipschitz.comp_lipschitzOnWith hf

/-- At almost every differentiability point the actual vector partial and coordinate partial
agree. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64_vector_partial_coordinate_ae {f : LoopPlane → E}
    (hdiff : ∀ᵐ p ∂mu, DifferentiableAt ℝ f p) (i : Fin 2) (b : Fin m) :
    (fun p => fderiv ℝ (fun q => f q b) p (EuclideanSpace.single i 1)) =ᵐ[mu]
      (fun p => (fderiv ℝ f p (EuclideanSpace.single i 1)) b) := by
  filter_upwards [hdiff] with p hp
  let P := PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin m => ℝ) b
  have hd := (P.hasFDerivAt.comp p hp.hasFDerivAt).fderiv
  exact congrArg (fun L => L (EuclideanSpace.single i 1)) hd

/-- The actual derivative columns of a Lipschitz observed annulus belong to L2. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64_lipschitz_vector_column_memLp {f : LoopPlane → E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f m64AnnulusDomain)
    (hdiff : ∀ᵐ p ∂mu, DifferentiableAt ℝ f p) (i : Fin 2) :
    MemLp (fun p => fderiv ℝ f p (EuclideanSpace.single i 1)) 2 mu := by
  let : IsFiniteMeasure mu := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono interior_subset).trans_lt m64AnnulusDomain_isCompact.measure_lt_top⟩
  apply MemLp.of_eval_piLp
  intro b
  have hh := (memLp_top_fderiv_apply_of_lipschitzOn isOpen_interior
    ((m64_lipschitz_coordinate hf b).mono interior_subset)
    (EuclideanSpace.single i 1)).mono_exponent (p := 2) le_top
  exact (memLp_congr_ae (m64_vector_partial_coordinate_ae hdiff i b)).mp hh

/-- The actual vector derivative columns of a Lipschitz observed annulus satisfy the
coordinate weak identities. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp.
447-449. -/
theorem m64_lipschitz_vector_weak_partial {f : LoopPlane → E} {K : ℝ≥0}
    (hf : LipschitzOnWith K f m64AnnulusDomain)
    (hdiff : ∀ᵐ p ∂mu, DifferentiableAt ℝ f p) (i : Fin 2) (b : Fin m) :
    HasWeakPartialDeriv i (fun p => (fderiv ℝ f p (EuclideanSpace.single i 1)) b)
      (fun p => f p b) S :=
  m64WeakPartialDeriv_ae_congr EventuallyEq.rfl (m64_vector_partial_coordinate_ae hdiff i b)
    (m64_lipschitz_scalar_weak_partial (m64_lipschitz_coordinate hf b) i)

end PoincareMT
