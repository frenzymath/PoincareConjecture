import PoincareConjecture.Proofs.M03.Existence.SpectralParabolicNative
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace PoincareConjecture.TimeL2BilinearNative

open SpectralHeatNative (timeMeasure)

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {T : ℝ}

abbrev TimePath (E : Type*) [TopologicalSpace E] (T : ℝ) := C(Icc (0 : ℝ) T, E)

abbrev TimeL2 (E : Type*) [NormedAddCommGroup E] (T : ℝ) := Lp E 2 (timeMeasure T)

def pathExtension (hT : 0 ≤ T) (A : TimePath E T) : ℝ → E :=
  IccExtend hT A

theorem continuous_pathExtension (hT : 0 ≤ T) (A : TimePath E T) :
    Continuous (pathExtension hT A) := A.continuous.Icc_extend'

theorem pathExtension_of_mem (hT : 0 ≤ T) (A : TimePath E T)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : pathExtension hT A t = A ⟨t, ht⟩ :=
  IccExtend_of_mem hT A ht

theorem norm_pathExtension_le (hT : 0 ≤ T) (A : TimePath E T) (t : ℝ) :
    ‖pathExtension hT A t‖ ≤ ‖A‖ :=
  A.norm_coe_le_norm (projIcc 0 T hT t)

theorem norm_product_field_le (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (A : TimePath E T) (V : ℝ → F) (t : ℝ) :
    ‖B (pathExtension hT A t) (V t)‖ ≤ ‖B‖ * ‖A‖ * ‖V t‖ := by
  exact (B.le_opNorm₂ _ _).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (norm_pathExtension_le hT A t) (norm_nonneg B))
      (norm_nonneg (V t)))

theorem memLp_product_field (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (A : TimePath E T) {V : ℝ → F} (hV : MemLp V 2 (timeMeasure T)) :
    MemLp (fun t => B (pathExtension hT A t) (V t)) 2 (timeMeasure T) := by
  apply hV.of_le_mul
    (B.aestronglyMeasurable_comp₂
      (continuous_pathExtension hT A).aestronglyMeasurable hV.aestronglyMeasurable)
  exact Eventually.of_forall (norm_product_field_le hT B A V)

def product (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (A : TimePath E T) (V : TimeL2 F T) : TimeL2 G T :=
  (memLp_product_field hT B A (Lp.memLp V)).toLp
    (fun t => B (pathExtension hT A t) (V t))

theorem product_ae_eq (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (A : TimePath E T) (V : TimeL2 F T) :
    product hT B A V =ᵐ[timeMeasure T]
      (fun t => B (pathExtension hT A t) (V t)) :=
  (memLp_product_field hT B A (Lp.memLp V)).coeFn_toLp

theorem product_ae_eq_on_interval (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (A : TimePath E T) (V : TimeL2 F T) :
    ∀ᵐ t ∂timeMeasure T, ∀ ht : t ∈ Icc (0 : ℝ) T,
      product hT B A V t = B (A ⟨t, ht⟩) (V t) := by
  filter_upwards [product_ae_eq hT B A V] with t ht
  intro htmem
  rw [ht, pathExtension_of_mem hT A htmem]

theorem norm_product_le (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (A : TimePath E T) (V : TimeL2 F T) :
    ‖product hT B A V‖ ≤ ‖B‖ * ‖A‖ * ‖V‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [product_ae_eq hT B A V] with t ht
  rw [ht]
  exact norm_product_field_le hT B A V t

theorem product_add_left (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (A C : TimePath E T) (V : TimeL2 F T) :
    product hT B (A + C) V = product hT B A V + product hT B C V := by
  apply Lp.ext
  filter_upwards [product_ae_eq hT B (A + C) V, product_ae_eq hT B A V,
    product_ae_eq hT B C V, Lp.coeFn_add (product hT B A V) (product hT B C V)]
      with t hAC hA hC hadd
  simp only [hAC, hadd, Pi.add_apply, hA, hC]
  change B (A (projIcc 0 T hT t) + C (projIcc 0 T hT t)) (V t) =
    B (A (projIcc 0 T hT t)) (V t) + B (C (projIcc 0 T hT t)) (V t)
  rw [map_add, ContinuousLinearMap.add_apply]

theorem product_smul_left (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (a : ℝ) (A : TimePath E T) (V : TimeL2 F T) :
    product hT B (a • A) V = a • product hT B A V := by
  apply Lp.ext
  filter_upwards [product_ae_eq hT B (a • A) V, product_ae_eq hT B A V,
    Lp.coeFn_smul a (product hT B A V)] with t haA hA hsmul
  simp only [haA, hsmul, Pi.smul_apply, hA]
  change B (a • A (projIcc 0 T hT t)) (V t) =
    a • B (A (projIcc 0 T hT t)) (V t)
  rw [map_smul, ContinuousLinearMap.smul_apply]

theorem product_add_right (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (A : TimePath E T) (V W : TimeL2 F T) :
    product hT B A (V + W) = product hT B A V + product hT B A W := by
  apply Lp.ext
  filter_upwards [product_ae_eq hT B A (V + W), product_ae_eq hT B A V,
    product_ae_eq hT B A W, Lp.coeFn_add V W,
    Lp.coeFn_add (product hT B A V) (product hT B A W)] with t hVW hV hW hin hout
  simp only [hVW, hout, Pi.add_apply, hV, hW, hin, map_add]

theorem product_smul_right (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (a : ℝ) (A : TimePath E T) (V : TimeL2 F T) :
    product hT B A (a • V) = a • product hT B A V := by
  apply Lp.ext
  filter_upwards [product_ae_eq hT B A (a • V), product_ae_eq hT B A V,
    Lp.coeFn_smul a V, Lp.coeFn_smul a (product hT B A V)] with t haV hV hin hout
  simp only [haV, hout, Pi.smul_apply, hV, hin, map_smul]

def productLinearMap (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G) :
    TimePath E T →ₗ[ℝ] TimeL2 F T →ₗ[ℝ] TimeL2 G T :=
  LinearMap.mk₂ ℝ (product hT B) (product_add_left hT B)
    (product_smul_left hT B) (product_add_right hT B) (product_smul_right hT B)

def productOperator (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G) :
    TimePath E T →L[ℝ] TimeL2 F T →L[ℝ] TimeL2 G T :=
  (productLinearMap hT B).mkContinuous₂ ‖B‖ (fun A V => by
    change ‖product hT B A V‖ ≤ ‖B‖ * ‖A‖ * ‖V‖
    exact norm_product_le hT B A V)

@[simp] theorem productOperator_apply (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (A : TimePath E T) (V : TimeL2 F T) :
    productOperator hT B A V = product hT B A V := rfl

theorem norm_productOperator_le (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G) :
    ‖productOperator hT B‖ ≤ ‖B‖ :=
  (productLinearMap hT B).mkContinuous₂_norm_le (norm_nonneg B) _

theorem product_sub_decomposition (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (A C : TimePath E T) (V W : TimeL2 F T) :
    product hT B A V - product hT B C W =
      product hT B A (V - W) + product hT B (A - C) W := by
  have hright : product hT B A (V - W) = product hT B A V - product hT B A W :=
    map_sub (productOperator hT B A) V W
  have hleft : product hT B (A - C) W = product hT B A W - product hT B C W := by
    simpa only [ContinuousLinearMap.sub_apply, productOperator_apply] using
      congrArg (fun L : TimeL2 F T →L[ℝ] TimeL2 G T => L W)
        (map_sub (productOperator hT B) A C)
  rw [hright, hleft]
  abel

theorem norm_product_sub_le (hT : 0 ≤ T) (B : E →L[ℝ] F →L[ℝ] G)
    (A C : TimePath E T) (V W : TimeL2 F T) :
    ‖product hT B A V - product hT B C W‖ ≤
      ‖B‖ * (‖A‖ * ‖V - W‖ + ‖A - C‖ * ‖W‖) := by
  rw [product_sub_decomposition hT B A C V W]
  calc
    _ ≤ ‖product hT B A (V - W)‖ + ‖product hT B (A - C) W‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖A‖ * ‖V - W‖ + ‖B‖ * ‖A - C‖ * ‖W‖ :=
      add_le_add (norm_product_le hT B A (V - W)) (norm_product_le hT B (A - C) W)
    _ = _ := by ring

end PoincareConjecture.TimeL2BilinearNative
