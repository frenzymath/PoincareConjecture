import PoincareConjecture.Proofs.M03.Existence.IntrinsicRicciJetNative
import Mathlib.Geometry.Manifold.VectorField.LieBracket

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle BigOperators Topology

noncomputable section

universe u

namespace PoincareConjecture.DeTurckNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

def chartFrame (p : M) (i : Fin n) : (y : M) → TangentSpace (𝓡 n) y :=
  VectorField.mpullback (𝓡 n) 𝓘(ℝ, E) (extChartAt (𝓡 n) p)
    (fun _ : E => (PiLp.basisFun 2 ℝ (Fin n)) i)

private theorem contMDiff_constant_model_field (v : E) :
    ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun x : E => (⟨x, v⟩ : TangentBundle 𝓘(ℝ, E) E)) := by
  exact contMDiff_vectorSpace_iff_contDiff.mpr contDiff_const

theorem chartFrame_contMDiffOn (p : M) (i : Fin n) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (chartFrame p i))
      (chartAt E p).source := by
  intro y hy
  have hmap : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ (extChartAt (𝓡 n) p) y :=
    contMDiffAt_extChartAt' hy
  have hinv : (mfderiv (𝓡 n) 𝓘(ℝ, E) (extChartAt (𝓡 n) p) y).IsInvertible :=
    isInvertible_mfderiv_extChartAt (by simpa only [extChartAt_source] using hy)
  have hconst := contMDiff_constant_model_field ((PiLp.basisFun 2 ℝ (Fin n)) i)
    (extChartAt (𝓡 n) p y)
  exact (hconst.mpullback_vectorField_preimage hmap hinv (by simp)).contMDiffWithinAt

def chartDifferentialEquiv (p y : M) (hy : y ∈ (chartAt E p).source) :
    TangentSpace (𝓡 n) y ≃L[ℝ] E :=
  Classical.choose (isInvertible_mfderiv_extChartAt (I := 𝓡 n) (x := p)
    (show y ∈ (extChartAt (𝓡 n) p).source by
      simpa only [extChartAt_source] using hy))

theorem chartDifferentialEquiv_coe (p y : M) (hy : y ∈ (chartAt E p).source) :
    (chartDifferentialEquiv p y hy : TangentSpace (𝓡 n) y →L[ℝ] E) =
      mfderiv (𝓡 n) 𝓘(ℝ, E) (extChartAt (𝓡 n) p) y :=
  Classical.choose_spec (isInvertible_mfderiv_extChartAt (I := 𝓡 n) (x := p)
    (show y ∈ (extChartAt (𝓡 n) p).source by
      simpa only [extChartAt_source] using hy))

def chartFrameBasis (p y : M) (hy : y ∈ (chartAt E p).source) :
    Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) y) :=
  (PiLp.basisFun 2 ℝ (Fin n)).map (chartDifferentialEquiv p y hy).symm.toLinearEquiv

theorem chartFrame_eq_basis (p y : M) (hy : y ∈ (chartAt E p).source)
    (i : Fin n) : chartFrame p i y = chartFrameBasis p y hy i := by
  change (mfderiv (𝓡 n) 𝓘(ℝ, E) (extChartAt (𝓡 n) p) y).inverse
      ((PiLp.basisFun 2 ℝ (Fin n)) i) = _
  rw [← chartDifferentialEquiv_coe p y hy]
  change ((chartDifferentialEquiv p y hy : TangentSpace (𝓡 n) y →L[ℝ] E).inverse)
      ((PiLp.basisFun 2 ℝ (Fin n)) i) = _
  rw [ContinuousLinearMap.inverse_equiv]
  rfl

theorem chartFrame_mlieBracket_eq_zero (p y : M)
    (hy : y ∈ (chartAt E p).source) (i j : Fin n) :
    VectorField.mlieBracket (𝓡 n) (chartFrame p i) (chartFrame p j) y = 0 := by
  have hmin : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  letI : IsManifold (𝓡 n) (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) hmin
  have hmap : ContMDiffAt (𝓡 n) 𝓘(ℝ, E) ∞ (extChartAt (𝓡 n) p) y :=
    contMDiffAt_extChartAt' hy
  have hconst (k : Fin n) :=
    contMDiff_constant_model_field ((PiLp.basisFun 2 ℝ (Fin n)) k)
      (extChartAt (𝓡 n) p y)
  have hnat := VectorField.mpullback_mlieBracket
    ((hconst i).mdifferentiableAt (by simp))
    ((hconst j).mdifferentiableAt (by simp)) hmap hmin
  have hzero : VectorField.mlieBracket 𝓘(ℝ, E)
      (fun _ : E => (PiLp.basisFun 2 ℝ (Fin n)) i)
      (fun _ : E => (PiLp.basisFun 2 ℝ (Fin n)) j) = 0 := by
    ext z
    change VectorField.mlieBracketWithin 𝓘(ℝ, E)
      (fun _ : E => (PiLp.basisFun 2 ℝ (Fin n)) i)
      (fun _ : E => (PiLp.basisFun 2 ℝ (Fin n)) j) Set.univ z = 0
    rw [VectorField.mlieBracketWithin_eq_lieBracketWithin]
    simp [VectorField.lieBracketWithin]
  simpa only [chartFrame, hzero, VectorField.mpullback_zero, Pi.zero_apply] using hnat.symm

theorem ricci_eq_ricciJet_chartFrame
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (p : M)
    {x : M} (hx : x ∈ (chartAt E p).source) (i j : Fin n) :
    D.ricci x (chartFrame p i x) (chartFrame p j x) =
      ricciJet (frameMetricJet g (chartFrame p) x) i j := by
  exact ricci_eq_ricciJet_frameMetricJet D (chartAt E p).open_source
    (chartFrame p) (chartFrame_contMDiffOn p) (chartFrameBasis p)
    (chartFrame_eq_basis p) (chartFrame_mlieBracket_eq_zero p) hx i j

end PoincareConjecture.DeTurckNative

end
