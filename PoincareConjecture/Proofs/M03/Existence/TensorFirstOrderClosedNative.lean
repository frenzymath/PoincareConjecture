import PoincareConjecture.Proofs.M03.Existence.NativeDirectionalClosedNative
import Mathlib.Topology.Sequences

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

noncomputable section

universe u v w

namespace PoincareConjecture.TensorProbeNative

section Coordinates

variable {X : Type u} [MeasurableSpace X] {alpha : Type v} [Fintype alpha]

def coefficientL2 (μ : Measure X) (i : alpha) :
    Lp (EuclideanSpace ℝ alpha) 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : alpha => ℝ) i).compLpL 2 μ

theorem coefficientL2_coe (μ : Measure X) (i : alpha)
    (f : Lp (EuclideanSpace ℝ alpha) 2 μ) :
    coefficientL2 μ i f =ᵐ[μ] fun x => f x i :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : alpha => ℝ) i).coeFn_compLpL f

end Coordinates

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [CompactSpace M] [MeasurableSpace M] [BorelSpace M]
  {iota : Type v} [Fintype iota] {kappa : Type w} [Finite kappa]
  (F : iota → SmoothField (n := n) (M := M))
  (p : kappa → M) (φ : kappa → C(M, ℝ)) (μ : Measure M) [IsFiniteMeasure μ]

local notation "ModelE" => EuclideanSpace ℝ (Fin n)

theorem derivativeToLp_limit_zero
    (hμ : μ = Measure.sum (fun i : kappa =>
      ChartMeasureNative.weightedChartMeasure (chartAt ModelE (p i)) (φ i)))
    (h : ℕ → SmoothTensor (n := n) (M := M))
    (w : Lp (DerivativeCoefficients iota) 2 μ)
    (hval : Tendsto (fun j => tensorToLp F μ (h j)) atTop (𝓝 0))
    (hderiv : Tendsto (fun j => derivativeToLp F μ (h j))
      atTop (𝓝 w)) : w = 0 := by
  have hcoordinate (ijk : iota × iota × iota) : coefficientL2 μ ijk w = 0 := by
    let f : ℕ → M → ℝ := fun j x => h j x (F ijk.2.1 x) (F ijk.2.2 x)
    let P : Lp (Coefficients iota) 2 μ →L[ℝ] Lp ℝ 2 μ :=
      coefficientL2 μ (ijk.2.1, ijk.2.2)
    let Q : Lp (DerivativeCoefficients iota) 2 μ →L[ℝ] Lp ℝ 2 μ :=
      coefficientL2 μ ijk
    have hP (j : ℕ) : P (tensorToLp F μ (h j)) =ᵐ[μ] f j := by
      filter_upwards [coefficientL2_coe μ (ijk.2.1, ijk.2.2)
        (tensorToLp F μ (h j)), tensorToLp_coe F μ (h j)] with x hx hp
      change P (tensorToLp F μ (h j)) x = _
      rw [hx, hp]
      rfl
    have hQ (j : ℕ) : Q (derivativeToLp F μ (h j)) =ᵐ[μ]
        scalarDirectional (F ijk.1) (f j) := by
      filter_upwards [coefficientL2_coe μ ijk (derivativeToLp F μ (h j)),
        derivativeToLp_coe F μ (h j)] with x hx hd
      change Q (derivativeToLp F μ (h j)) x = _
      rw [hx, hd]
      rfl
    have hfLp (j : ℕ) : MemLp (f j) 2 μ :=
      MemLp.ae_eq (hP j) (Lp.memLp (P (tensorToLp F μ (h j))))
    have hDfLp (j : ℕ) : MemLp (scalarDirectional (F ijk.1) (f j)) 2 μ :=
      MemLp.ae_eq (hQ j) (Lp.memLp (Q (derivativeToLp F μ (h j))))
    have hPeq (j : ℕ) : P (tensorToLp F μ (h j)) = (hfLp j).toLp (f j) := by
      apply Lp.ext
      exact (hP j).trans (hfLp j).coeFn_toLp.symm
    have hQeq (j : ℕ) : Q (derivativeToLp F μ (h j)) =
        (hDfLp j).toLp (scalarDirectional (F ijk.1) (f j)) := by
      apply Lp.ext
      exact (hQ j).trans (hDfLp j).coeFn_toLp.symm
    have hflim : Tendsto (fun j => (hfLp j).toLp (f j)) atTop (𝓝 0) := by
      have hlim := ((P.continuous.tendsto 0).comp hval).congr' (Eventually.of_forall hPeq)
      simpa only [map_zero] using hlim
    have hDflim : Tendsto (fun j =>
        (hDfLp j).toLp (scalarDirectional (F ijk.1) (f j))) atTop (𝓝 (Q w)) :=
      ((Q.continuous.tendsto w).comp hderiv).congr' (Eventually.of_forall hQeq)
    subst μ
    exact scalarDirectional_limit_zero p φ (F ijk.1) f
      (fun j => contMDiff_pairing (h j) (F ijk.2.1) (F ijk.2.2))
      hfLp hDfLp (Q w) hflim hDflim
  have hcoeffzero (ijk : iota × iota × iota) : (fun x => w x ijk) =ᵐ[μ] 0 := by
    have hcoe := coefficientL2_coe μ ijk w
    rw [hcoordinate] at hcoe
    exact hcoe.symm.trans (Lp.coeFn_zero ℝ 2 μ)
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [ae_all_iff.mpr hcoeffzero] with x hx
  ext ijk
  exact hx ijk

theorem graphValue_eq_zero_iff
    (hμ : μ = Measure.sum (fun i : kappa =>
      ChartMeasureNative.weightedChartMeasure (chartAt ModelE (p i)) (φ i)))
    (x : firstOrderGraph F μ) : graphValue F μ x = 0 ↔ x = 0 := by
  constructor
  · intro hx
    have hxclosure : (x : FirstOrderAmbient F μ) ∈
        closure (Set.range (firstOrderImage F μ)) := x.property
    obtain ⟨s, hs, hslim⟩ := mem_closure_iff_seq_limit.mp hxclosure
    choose h hh using hs
    have hhlim : Tendsto (fun j => firstOrderImage F μ (h j)) atTop
        (𝓝 (x : FirstOrderAmbient F μ)) :=
      hslim.congr' (Eventually.of_forall (fun j => (hh j).symm))
    let P : FirstOrderAmbient F μ →L[ℝ] Lp (Coefficients iota) 2 μ :=
      (tensorL2 F μ).subtypeL.comp
        (WithLp.fstL 2 ℝ (tensorL2 F μ) (Lp (DerivativeCoefficients iota) 2 μ))
    let Q : FirstOrderAmbient F μ →L[ℝ] Lp (DerivativeCoefficients iota) 2 μ :=
      WithLp.sndL 2 ℝ (tensorL2 F μ) (Lp (DerivativeCoefficients iota) 2 μ)
    have hPx : P (x : FirstOrderAmbient F μ) = 0 :=
      congrArg (fun y : tensorL2 F μ => (y : Lp (Coefficients iota) 2 μ)) hx
    have hval : Tendsto (fun j => tensorToLp F μ (h j)) atTop (𝓝 0) := by
      have hlim := (P.continuous.tendsto (x : FirstOrderAmbient F μ)).comp hhlim
      rw [hPx] at hlim
      exact hlim
    have hderiv : Tendsto (fun j => derivativeToLp F μ (h j)) atTop
        (𝓝 (Q (x : FirstOrderAmbient F μ))) :=
      (Q.continuous.tendsto (x : FirstOrderAmbient F μ)).comp hhlim
    have hQx := derivativeToLp_limit_zero F p φ μ hμ h
      (Q (x : FirstOrderAmbient F μ)) hval hderiv
    apply Subtype.ext
    apply WithLp.ofLp_injective 2
    exact Prod.ext hx hQx
  · rintro rfl
    exact map_zero _

theorem graphValue_injective
    (hμ : μ = Measure.sum (fun i : kappa =>
      ChartMeasureNative.weightedChartMeasure (chartAt ModelE (p i)) (φ i))) :
    Function.Injective (graphValue F μ) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply (graphValue_eq_zero_iff F p φ μ hμ (x - y)).mp
  rw [map_sub, hxy, sub_self]

end PoincareConjecture.TensorProbeNative
