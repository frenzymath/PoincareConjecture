import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.Topology.Algebra.Module.Basic















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

local notation "ModelE" => EuclideanSpace ℝ (Fin n)
local notation "FiberBilin" =>
  fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ

abbrev SmoothTensor :=
  ContMDiffSection (𝓡 n) (ModelE →L[ℝ] ModelE →L[ℝ] ℝ) ∞ FiberBilin

abbrev SmoothField :=
  ContMDiffSection (𝓡 n) ModelE ∞ (TangentSpace (𝓡 n) : M → Type _)


def metricTensor (g : RiemannianMetric n M) : SmoothTensor (n := n) (M := M) :=
  ⟨g.inner, g.contMDiff⟩

@[simp] theorem metricTensor_apply (g : RiemannianMetric n M) (x : M)
    (v w : TangentSpace (𝓡 n) x) : metricTensor g x v w = g.inner x v w := rfl

theorem continuous_pairing (h : SmoothTensor (n := n) (M := M))
    (V W : SmoothField (n := n) (M := M)) :
    Continuous (fun x => h x (V x) (W x)) := by
  have hb : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : M => (⟨x, h x (V x) (W x)⟩ :
        Bundle.TotalSpace ℝ (fun _ : M => ℝ))) :=
    h.contMDiff.clm_bundle_apply₂ V.contMDiff W.contMDiff
  have hs : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => h x (V x) (W x)) := by
    intro x
    have hx := (Bundle.contMDiffAt_totalSpace.mp (hb x)).2
    change ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun y => h y (V y) (W y)) x at hx
    exact hx
  exact hs.continuous

variable {iota : Type v} [Fintype iota]

abbrev Coefficients (iota : Type v) [Fintype iota] := EuclideanSpace ℝ (iota × iota)


def probes (F : iota → SmoothField (n := n) (M := M)) :
    SmoothTensor (n := n) (M := M) →ₗ[ℝ] C(M, Coefficients iota) where
  toFun h :=
    { toFun := fun x => WithLp.toLp 2 (fun ij : iota × iota => h x (F ij.1 x) (F ij.2 x))
      continuous_toFun := (PiLp.continuous_toLp 2 (fun _ : iota × iota => ℝ)).comp
        (continuous_pi (fun ij : iota × iota =>
          continuous_pairing h (F ij.1) (F ij.2))) }
  map_add' h k := by
    ext x ij
    rfl
  map_smul' c h := by
    ext x ij
    rfl

@[simp] theorem probes_apply (F : iota → SmoothField (n := n) (M := M))
    (h : SmoothTensor (n := n) (M := M)) (x : M) (i j : iota) :
    probes F h x (i, j) = h x (F i x) (F j x) := rfl

theorem probes_injective (F : iota → SmoothField (n := n) (M := M))
    (hspan : ∀ x : M, Submodule.span ℝ (Set.range (fun i => F i x)) = ⊤) :
    Function.Injective (probes F) := by
  intro h k heq
  apply ContMDiffSection.ext
  intro x
  have hpair (i j : iota) : h x (F i x) (F j x) = k x (F i x) (F j x) :=
    by simpa only [probes_apply] using
      congrArg (fun p : C(M, Coefficients iota) => p x (i, j)) heq
  have houter : (h x).toLinearMap = (k x).toLinearMap := by
    apply LinearMap.ext_on_range (hspan x)
    intro i
    have hinner : (h x (F i x)).toLinearMap = (k x (F i x)).toLinearMap :=
      LinearMap.ext_on_range (hspan x) (hpair i)
    apply ContinuousLinearMap.ext
    intro w
    exact LinearMap.congr_fun hinner w
  apply ContinuousLinearMap.ext
  intro v
  exact LinearMap.congr_fun houter v

variable [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  (F : iota → SmoothField (n := n) (M := M)) (μ : Measure M) [IsFiniteMeasure μ]


def tensorToLp : SmoothTensor (n := n) (M := M) →ₗ[ℝ] Lp (Coefficients iota) 2 μ :=
  (ContinuousMap.toLp 2 μ ℝ).toLinearMap.comp (probes F)

theorem tensorToLp_coe (h : SmoothTensor (n := n) (M := M)) :
    tensorToLp F μ h =ᵐ[μ] probes F h :=
  ContinuousMap.coeFn_toLp μ (probes F h)

theorem tensorToLp_injective [μ.IsOpenPosMeasure]
    (hspan : ∀ x : M, Submodule.span ℝ (Set.range (fun i => F i x)) = ⊤) :
    Function.Injective (tensorToLp F μ) := by
  intro h k heq
  apply probes_injective F hspan
  exact ContinuousMap.toLp_injective μ heq

theorem tensorToLp_norm_sq (h : SmoothTensor (n := n) (M := M)) :
    ‖tensorToLp F μ h‖ ^ 2 = ∫ x, ‖probes F h x‖ ^ 2 ∂μ := by
  calc
    ‖tensorToLp F μ h‖ ^ 2 = inner ℝ (tensorToLp F μ h) (tensorToLp F μ h) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫ x, inner ℝ (tensorToLp F μ h x) (tensorToLp F μ h x) ∂μ := rfl
    _ = ∫ x, ‖probes F h x‖ ^ 2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [tensorToLp_coe F μ h] with x hx
      rw [hx, real_inner_self_eq_norm_sq]


def tensorL2 : Submodule ℝ (Lp (Coefficients iota) 2 μ) :=
  (tensorToLp F μ).range.topologicalClosure

instance tensorL2_completeSpace : CompleteSpace (tensorL2 F μ) :=
  inferInstanceAs (CompleteSpace (tensorToLp F μ).range.topologicalClosure)


def intoTensorL2 : SmoothTensor (n := n) (M := M) →ₗ[ℝ] tensorL2 F μ :=
  (tensorToLp F μ).codRestrict (tensorL2 F μ) (fun h =>
    (tensorToLp F μ).range.le_topologicalClosure (LinearMap.mem_range_self _ h))

@[simp] theorem intoTensorL2_coe (h : SmoothTensor (n := n) (M := M)) :
    (intoTensorL2 F μ h : Lp (Coefficients iota) 2 μ) = tensorToLp F μ h := rfl

theorem intoTensorL2_injective [μ.IsOpenPosMeasure]
    (hspan : ∀ x : M, Submodule.span ℝ (Set.range (fun i => F i x)) = ⊤) :
    Function.Injective (intoTensorL2 F μ) := by
  intro h k heq
  apply tensorToLp_injective F μ hspan
  exact congrArg (fun z : tensorL2 F μ => (z : Lp (Coefficients iota) 2 μ)) heq

theorem intoTensorL2_denseRange : DenseRange (intoTensorL2 F μ) := by
  apply Topology.IsInducing.subtypeVal.dense_iff.mpr
  intro x
  have hincl : ((tensorToLp F μ).range : Set (Lp (Coefficients iota) 2 μ)) ⊆
      Subtype.val '' Set.range (intoTensorL2 F μ) := by
    rintro _ ⟨h, rfl⟩
    exact ⟨intoTensorL2 F μ h, ⟨h, rfl⟩, rfl⟩
  exact closure_mono hincl x.property

end PoincareConjecture.TensorProbeNative
