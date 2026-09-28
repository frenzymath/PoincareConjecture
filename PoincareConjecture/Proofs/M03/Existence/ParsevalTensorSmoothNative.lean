import PoincareConjecture.Proofs.M03.Existence.ParsevalTensorDecodeNative
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

open Bundle Filter Set
open scoped Manifold ContDiff Bundle BigOperators Topology

noncomputable section

universe u v

namespace PoincareConjecture.ParsevalTensorNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "DualE" => E →L[ℝ] ℝ
local notation "BilinE" => E →L[ℝ] E →L[ℝ] ℝ
local notation "DualFib" => fun x : M => TangentSpace (𝓡 n) x →L[ℝ] ℝ
local notation "BilinFib" => fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ

def covectorProduct (g : RiemannianMetric n M) (alpha beta : (x : M) → DualFib x)
    (x : M) : BilinFib x :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  (alpha x).smulRight (beta x)

theorem covectorProduct_apply (g : RiemannianMetric n M)
    (alpha beta : (x : M) → DualFib x) (x : M) (v w : TangentSpace (𝓡 n) x) :
    covectorProduct g alpha beta x v w = alpha x v * beta x w := rfl

private theorem covector_inCoordinates_apply (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace (𝓡 n)) p).baseSet)
    (alpha : DualFib x) (v : E) :
    ContinuousLinearMap.inCoordinates E (TangentSpace (𝓡 n)) ℝ (fun _ : M => ℝ)
        p x p x alpha v =
      alpha ((trivializationAt E (TangentSpace (𝓡 n)) p).symm x v) := by
  simp only [ContinuousLinearMap.inCoordinates, ContinuousLinearMap.comp_apply]
  change (Bundle.Trivial.trivialization M ℝ).continuousLinearMapAt ℝ x
      (alpha ((trivializationAt E (TangentSpace (𝓡 n)) p).symmL ℝ x v)) = _
  rw [Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply,
    (trivializationAt E (TangentSpace (𝓡 n)) p).symmL_apply hx]

private theorem covectorProduct_coordinates (g : RiemannianMetric n M)
    (alpha beta : (x : M) → DualFib x) (p x : M)
    (hx : x ∈ (trivializationAt E (TangentSpace (𝓡 n)) p).baseSet) :
    (trivializationAt BilinE BilinFib p
      (TotalSpace.mk' BilinE x (covectorProduct g alpha beta x))).2 =
      ((trivializationAt DualE DualFib p (TotalSpace.mk' DualE x (alpha x))).2).smulRight
        ((trivializationAt DualE DualFib p (TotalSpace.mk' DualE x (beta x))).2) := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hreal : x ∈ (trivializationAt ℝ (fun _ : M => ℝ) p).baseSet := mem_univ x
  simp only [hom_trivializationAt_apply]
  ext v w
  rw [inCoordinates_apply_eq₂ hx hx hreal]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, covector_inCoordinates_apply p x hx, covectorProduct_apply]
  change (Bundle.Trivial.trivialization M ℝ).linearMapAt ℝ x _ = _
  rw [Bundle.Trivial.linearMapAt_trivialization, LinearMap.id_apply]

theorem covectorProduct_contMDiff (g : RiemannianMetric n M)
    (alpha beta : (x : M) → DualFib x)
    (halpha : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, DualE)) ∞
      (fun x => TotalSpace.mk' DualE x (alpha x)))
    (hbeta : ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, DualE)) ∞
      (fun x => TotalSpace.mk' DualE x (beta x))) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, BilinE)) ∞
      (fun x => TotalSpace.mk' BilinE x (covectorProduct g alpha beta x)) := by
  intro x
  have ha := (Bundle.contMDiffAt_totalSpace.mp (halpha x)).2
  have hb := (Bundle.contMDiffAt_totalSpace.mp (hbeta x)).2
  have hprod : ContMDiffAt (𝓡 n) 𝓘(ℝ, BilinE) ∞
      (fun y =>
        ((trivializationAt DualE DualFib x (TotalSpace.mk' DualE y (alpha y))).2).smulRight
          ((trivializationAt DualE DualFib x (TotalSpace.mk' DualE y (beta y))).2)) x :=
    ContDiff.comp_contMDiffAt
      (g := fun p : DualE × DualE => p.1.smulRight p.2)
      (contDiff_fst.smulRight contDiff_snd) (ha.prodMk_space hb)
  apply Bundle.contMDiffAt_totalSpace.mpr
  refine ⟨contMDiffAt_id, ?_⟩
  apply hprod.congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace (𝓡 n)) x).open_baseSet.mem_nhds
    (mem_baseSet_trivializationAt E (TangentSpace (𝓡 n)) x)] with y hy
  exact covectorProduct_coordinates g alpha beta x y hy

def coframeTensor (g : RiemannianMetric n M)
    (V W : TensorProbeNative.SmoothField (n := n) (M := M)) :
    TensorProbeNative.SmoothTensor (n := n) (M := M) where
  toFun := covectorProduct g (fun x => g.inner x (V x)) (fun x => g.inner x (W x))
  contMDiff_toFun := covectorProduct_contMDiff g _ _
    (g.contMDiff.clm_bundle_apply V.contMDiff) (g.contMDiff.clm_bundle_apply W.contMDiff)

theorem coframeTensor_apply (g : RiemannianMetric n M)
    (V W : TensorProbeNative.SmoothField (n := n) (M := M)) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    coframeTensor g V W x v w = g.inner x (V x) v * g.inner x (W x) w := rfl

variable {iota : Type v} [Fintype iota]

theorem nativeDecode_eq_sum (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (x : M) (C : TensorProbeNative.Coefficients iota) :
    nativeDecode g F x C = ∑ ab : iota × iota,
      C ab • coframeTensor g (F ab.1) (F ab.2) x := by
  ext v w
  rw [nativeDecode_apply]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    coframeTensor_apply, smul_eq_mul, mul_assoc]

theorem nativeDecode_contMDiff (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (C : M → TensorProbeNative.Coefficients iota)
    (hC : ∀ ab : iota × iota, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => C x ab)) :
    ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, BilinE)) ∞
      (fun x => TotalSpace.mk' BilinE x (nativeDecode g F x (C x))) := by
  have hterm (ab : iota × iota) :
      ContMDiff (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, BilinE)) ∞
        (fun x => TotalSpace.mk' BilinE x
          (C x ab • coframeTensor g (F ab.1) (F ab.2) x)) :=
    (hC ab).smul_section (coframeTensor g (F ab.1) (F ab.2)).contMDiff
  have hsum := ContMDiff.sum_section (s := Finset.univ) (fun ab _ => hterm ab)
  convert hsum using 1
  funext x
  exact congrArg (fun h : BilinFib x => (TotalSpace.mk' BilinE x h : TotalSpace BilinE BilinFib))
    (nativeDecode_eq_sum g F x (C x))

def smoothDecode (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (C : M → TensorProbeNative.Coefficients iota)
    (hC : ∀ ab : iota × iota, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => C x ab)) :
    TensorProbeNative.SmoothTensor (n := n) (M := M) :=
  ⟨fun x => nativeDecode g F x (C x), nativeDecode_contMDiff g F C hC⟩

@[simp] theorem smoothDecode_apply (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (C : M → TensorProbeNative.Coefficients iota)
    (hC : ∀ ab : iota × iota, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => C x ab))
    (x : M) : smoothDecode g F C hC x = nativeDecode g F x (C x) := rfl

theorem probes_smoothDecode (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (C : M → TensorProbeNative.Coefficients iota)
    (hC : ∀ ab : iota × iota, ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => C x ab))
    (x : M) :
    TensorProbeNative.probes F (smoothDecode g F C hC) x = nativeProjection g F x (C x) := by
  apply PiLp.ext
  rintro ⟨a, b⟩
  rfl

theorem nativeDecode_contMDiffOn_spacetime (g : RiemannianMetric n M)
    (F : iota → TensorProbeNative.SmoothField (n := n) (M := M))
    (C : ℝ × M → TensorProbeNative.Coefficients iota) {S : Set (ℝ × M)}
    (hC : ∀ ab : iota × iota,
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, ℝ) ∞ (fun p => C p ab) S) :
    ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, BilinE)) ∞
      (fun p : ℝ × M => (TotalSpace.mk' BilinE p.2
        (nativeDecode g F p.2 (C p)) : TotalSpace BilinE BilinFib)) S := by
  intro p hp
  let e := trivializationAt BilinE BilinFib p.2
  have hframe (ab : iota × iota) :
      ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) ((𝓡 n).prod 𝓘(ℝ, BilinE)) ∞
        (fun q : ℝ × M => (TotalSpace.mk' BilinE q.2
          (coframeTensor g (F ab.1) (F ab.2) q.2) : TotalSpace BilinE BilinFib)) :=
    (coframeTensor g (F ab.1) (F ab.2)).contMDiff.comp contMDiff_snd
  have hterm (ab : iota × iota) :
      ContMDiffWithinAt (𝓘(ℝ, ℝ).prod (𝓡 n)) 𝓘(ℝ, BilinE) ∞
        (fun q : ℝ × M => C q ab •
          (e (TotalSpace.mk' BilinE q.2
            (coframeTensor g (F ab.1) (F ab.2) q.2) : TotalSpace BilinE BilinFib)).2)
        S p :=
    (hC ab p hp).smul
      (Bundle.contMDiffWithinAt_totalSpace.mp (hframe ab p).contMDiffWithinAt).2
  have hsum := ContMDiffWithinAt.sum (t := Finset.univ) (fun ab _ => hterm ab)
  have heq (q : ℝ × M) (hq : q.2 ∈ e.baseSet) :
      (e (TotalSpace.mk' BilinE q.2 (nativeDecode g F q.2 (C q)) :
        TotalSpace BilinE BilinFib)).2 =
        ∑ ab : iota × iota, C q ab •
          (e (TotalSpace.mk' BilinE q.2
            (coframeTensor g (F ab.1) (F ab.2) q.2) : TotalSpace BilinE BilinFib)).2 := by
    let A : BilinFib q.2 →L[ℝ] BilinE :=
      Bundle.Trivialization.continuousLinearMapAt (F := BilinE) («E» := BilinFib) ℝ e q.2
    have hA (y : BilinFib q.2) :
        A y = (e (TotalSpace.mk' BilinE q.2 y : TotalSpace BilinE BilinFib)).2 :=
      Bundle.Trivialization.continuousLinearMapAt_apply_of_mem
        (R := ℝ) (F := BilinE) («E» := BilinFib) (B := M) (b := q.2) e hq y
    calc
      _ = A (nativeDecode g F q.2 (C q)) := (hA _).symm
      _ = ∑ ab : iota × iota, C q ab • A (coframeTensor g (F ab.1) (F ab.2) q.2) := by
        rw [nativeDecode_eq_sum, map_sum]
        simp only [map_smul]
      _ = _ := by simp only [hA]
  have hbase : ∀ᶠ q : ℝ × M in 𝓝[S] p, q.2 ∈ e.baseSet :=
    continuous_snd.continuousWithinAt
      (e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt BilinE BilinFib p.2))
  apply Bundle.contMDiffWithinAt_totalSpace.mpr
  refine ⟨contMDiffWithinAt_snd, ?_⟩
  apply hsum.congr_of_eventuallyEq
  · filter_upwards [hbase] with q hq
    exact heq q hq
  · exact heq p (mem_baseSet_trivializationAt BilinE BilinFib p.2)

end PoincareConjecture.ParsevalTensorNative

end
