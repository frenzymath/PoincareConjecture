import PoincareConjecture.Proofs.M03.Existence.TensorProbeL2Native
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open MeasureTheory
open scoped Manifold ContDiff Bundle Topology

noncomputable section

universe u v

namespace PoincareConjecture.TensorProbeNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem contMDiff_pairing (h : SmoothTensor (n := n) (M := M))
    (V W : SmoothField (n := n) (M := M)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => h x (V x) (W x)) := by
  have hb : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : M => (⟨x, h x (V x) (W x)⟩ :
        Bundle.TotalSpace ℝ (fun _ : M => ℝ))) :=
    h.contMDiff.clm_bundle_apply₂ V.contMDiff W.contMDiff
  intro x
  have hx := (Bundle.contMDiffAt_totalSpace.mp (hb x)).2
  change ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun y => h y (V y) (W y)) x at hx
  exact hx

theorem contMDiff_directional {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    (V : SmoothField (n := n) (M := M)) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f x (V x)) := by
  have ht := hf.contMDiff_tangentMap (m := ∞) (by simp)
  have hcomp := ht.comp V.contMDiff
  exact (contMDiff_snd_tangentBundle_modelSpace ℝ 𝓘(ℝ, ℝ)).comp hcomp

variable {iota : Type v} [Fintype iota]

abbrev DerivativeCoefficients (iota : Type v) [Fintype iota] :=
  EuclideanSpace ℝ (iota × iota × iota)

def derivativeProbes (F : iota → SmoothField (n := n) (M := M)) :
    SmoothTensor (n := n) (M := M) →ₗ[ℝ] C(M, DerivativeCoefficients iota) where
  toFun h :=
    { toFun := fun x => WithLp.toLp 2 (fun ijk : iota × iota × iota =>
        mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
          (fun y => h y (F ijk.2.1 y) (F ijk.2.2 y)) x (F ijk.1 x))
      continuous_toFun := (PiLp.continuous_toLp 2 (fun _ : iota × iota × iota => ℝ)).comp
        (continuous_pi (fun ijk : iota × iota × iota =>
          (contMDiff_directional (contMDiff_pairing h (F ijk.2.1) (F ijk.2.2))
            (F ijk.1)).continuous)) }
  map_add' h k := by
    ext x ijk
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
        ((fun y => h y (F ijk.2.1 y) (F ijk.2.2 y)) +
          (fun y => k y (F ijk.2.1 y) (F ijk.2.2 y))) x (F ijk.1 x) = _
    rw [mfderiv_add
      ((contMDiff_pairing h (F ijk.2.1) (F ijk.2.2)).mdifferentiable (by simp) x)
      ((contMDiff_pairing k (F ijk.2.1) (F ijk.2.2)).mdifferentiable (by simp) x)]
    rfl
  map_smul' c h := by
    ext x ijk
    change mfderiv (𝓡 n) 𝓘(ℝ, ℝ)
        (c • (fun y => h y (F ijk.2.1 y) (F ijk.2.2 y))) x (F ijk.1 x) = _
    rw [(((contMDiff_pairing h (F ijk.2.1) (F ijk.2.2)).mdifferentiable
      (by simp) x).hasMFDerivAt.const_smul c).mfderiv]
    rfl

@[simp] theorem derivativeProbes_apply (F : iota → SmoothField (n := n) (M := M))
    (h : SmoothTensor (n := n) (M := M)) (x : M) (i j k : iota) :
    derivativeProbes F h x (i, j, k) =
      mfderiv (𝓡 n) 𝓘(ℝ, ℝ) (fun y => h y (F j y) (F k y)) x (F i x) := rfl

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (F : iota → SmoothField (n := n) (M := M)) (μ : Measure M) [IsFiniteMeasure μ]

def derivativeToLp : SmoothTensor (n := n) (M := M) →ₗ[ℝ] Lp (DerivativeCoefficients iota) 2 μ :=
  (ContinuousMap.toLp 2 μ ℝ).toLinearMap.comp (derivativeProbes F)

theorem derivativeToLp_coe (h : SmoothTensor (n := n) (M := M)) :
    derivativeToLp F μ h =ᵐ[μ] derivativeProbes F h :=
  ContinuousMap.coeFn_toLp μ (derivativeProbes F h)

abbrev FirstOrderAmbient :=
  WithLp 2 (tensorL2 F μ × Lp (DerivativeCoefficients iota) 2 μ)

def firstOrderImage : SmoothTensor (n := n) (M := M) →ₗ[ℝ] FirstOrderAmbient F μ :=
  (WithLp.linearEquiv 2 ℝ
    (tensorL2 F μ × Lp (DerivativeCoefficients iota) 2 μ)).symm.toLinearMap.comp
      ((intoTensorL2 F μ).prod (derivativeToLp F μ))

def firstOrderGraph : Submodule ℝ (FirstOrderAmbient F μ) :=
  (firstOrderImage F μ).range.topologicalClosure

instance firstOrderGraph_completeSpace : CompleteSpace (firstOrderGraph F μ) :=
  inferInstanceAs (CompleteSpace (firstOrderImage F μ).range.topologicalClosure)

def intoFirstOrderGraph : SmoothTensor (n := n) (M := M) →ₗ[ℝ] firstOrderGraph F μ :=
  (firstOrderImage F μ).codRestrict (firstOrderGraph F μ) (fun h =>
    (firstOrderImage F μ).range.le_topologicalClosure (LinearMap.mem_range_self _ h))

def graphValue : firstOrderGraph F μ →L[ℝ] tensorL2 F μ :=
  (WithLp.fstL 2 ℝ (tensorL2 F μ) (Lp (DerivativeCoefficients iota) 2 μ)).comp
    (firstOrderGraph F μ).subtypeL

@[simp] theorem graphValue_into (h : SmoothTensor (n := n) (M := M)) :
    graphValue F μ (intoFirstOrderGraph F μ h) = intoTensorL2 F μ h := rfl

theorem norm_graphValue_le (x : firstOrderGraph F μ) : ‖graphValue F μ x‖ ≤ ‖x‖ :=
  WithLp.norm_fst_le (tensorL2 F μ) (x : FirstOrderAmbient F μ)

theorem graphValue_denseRange : DenseRange (graphValue F μ) := by
  apply (intoTensorL2_denseRange F μ).mono
  rintro _ ⟨h, rfl⟩
  exact ⟨intoFirstOrderGraph F μ h, rfl⟩

theorem intoFirstOrderGraph_injective [μ.IsOpenPosMeasure]
    (hspan : ∀ x : M, Submodule.span ℝ (Set.range (fun i => F i x)) = ⊤) :
    Function.Injective (intoFirstOrderGraph F μ) := by
  intro h k heq
  apply intoTensorL2_injective F μ hspan
  exact congrArg (graphValue F μ) heq

theorem intoFirstOrderGraph_denseRange : DenseRange (intoFirstOrderGraph F μ) := by
  apply Topology.IsInducing.subtypeVal.dense_iff.mpr
  intro x
  have hincl : ((firstOrderImage F μ).range : Set (FirstOrderAmbient F μ)) ⊆
      Subtype.val '' Set.range (intoFirstOrderGraph F μ) := by
    rintro _ ⟨h, rfl⟩
    exact ⟨intoFirstOrderGraph F μ h, ⟨h, rfl⟩, rfl⟩
  exact closure_mono hincl x.property

theorem norm_firstOrderImage_sq (h : SmoothTensor (n := n) (M := M)) :
    ‖firstOrderImage F μ h‖ ^ 2 = ‖tensorToLp F μ h‖ ^ 2 + ‖derivativeToLp F μ h‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 (firstOrderImage F μ h)

end PoincareConjecture.TensorProbeNative
