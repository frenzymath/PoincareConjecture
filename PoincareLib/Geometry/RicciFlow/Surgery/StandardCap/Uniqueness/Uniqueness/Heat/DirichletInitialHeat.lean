import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Imports
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Uniqueness.Uniqueness.Heat.DirichletLaplacian

/-!
# Actual compact-domain heat with nonzero supported initial data

Morgan-Tian, Section 12.5, p. 304: cutoff initial rotation components
are genuine supported smooth initial data. Subtracting that initial
function gives a zero-initial problem with its literal Laplacian as
forcing. The constructed spectral response therefore supplies the
actual weak homogeneous Dirichlet heat equation.
-/

set_option autoImplicit false
set_option maxSynthPendingDepth 5
set_option backward.isDefEq.respectTransparency false

noncomputable section

open MeasureTheory Set
open scoped Topology ENNReal SchwartzMap

namespace PoincareMT.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

private theorem generator_graph_add {W H : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (J : W →L[ℝ] H) {u a v b : H}
    (hu : HilbertResolventNative.InGeneratorGraph J u a)
    (hv : HilbertResolventNative.InGeneratorGraph J v b) :
    HilbertResolventNative.InGeneratorGraph J (u + v) (a + b) := by
  unfold HilbertResolventNative.InGeneratorGraph at hu hv ⊢
  rw [add_add_add_comm, map_add, hu, hv]

/-- Section 12.5, p. 304: the actual spectral construction admits
every supported smooth initial function and solves the homogeneous
equation for the proved Dirichlet generator. -/
theorem exists_dirichlet_initial_heat {K : Set V} (hK : IsCompact K)
    {T : ℝ} (hT : 0 ≤ T) (f : supportedTests K) :
    ∃ U D A : ℝ → dirichletValue K,
      U 0 = intoDirichletValue K f ∧ ContinuousOn U (Icc (0 : ℝ) T) ∧
      MemLp D 2 (SpectralHeatNative.timeMeasure T) ∧
      MemLp A 2 (SpectralHeatNative.timeMeasure T) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T, HasDerivAt U (D t) t) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T, D t + A t = 0) ∧
      (∀ᵐ t ∂SpectralHeatNative.timeMeasure T,
        HilbertResolventNative.InGeneratorGraph («V» := dirichletForm K)
          (dirichletInclusion K) (U t) (A t)) := by
  let L := intoDirichletValue K (testLaplacian hK.isClosed f)
  obtain ⟨W, D, A, hW0, hWcont, hD, hA, hderiv, heq, hgraph, _⟩ :=
    exists_dirichlet_response hK hT
      (memLp_const L : MemLp (fun _ : ℝ => L) 2 (SpectralHeatNative.timeMeasure T))
  refine ⟨fun t => intoDirichletValue K f + W t, D, fun t => -L + A t,
    by simpa only [add_zero] using congrArg (fun z => intoDirichletValue K f + z) hW0,
    continuousOn_const.add hWcont,
    hD, (memLp_const (-L)).add hA, ?_, ?_, ?_⟩
  · filter_upwards [hderiv] with t ht
    simpa only [zero_add] using! (hasDerivAt_const t (intoDirichletValue K f)).add ht
  · filter_upwards [heq] with t ht
    calc
      D t + (-L + A t) = -L + (D t + A t) := by abel
      _ = 0 := by rw [ht, neg_add_cancel]
  · filter_upwards [hgraph] with t ht
    exact generator_graph_add (W := dirichletForm K) (H := dirichletValue K) (dirichletInclusion K)
      (dirichletGenerator_laplacian hK.isClosed f) ht

/-- Actual derivative coordinates on the completed supported graph. -/
def dirichletGradient (K : Set V) : dirichletForm K →L[ℝ] DirichletGradient n :=
  (WithLp.sndL 2 ℝ (dirichletValue K) (DirichletGradient n)).comp
    (dirichletForm K).subtypeL

@[simp] theorem dirichletGradient_into (K : Set V) (f : supportedTests K) :
    dirichletGradient K (intoDirichletForm K f) = testGradient K f := rfl

/-- Section 12.5, p. 304: the constructed generator equation is the
actual weak heat equation against every supported smooth test. -/
theorem dirichlet_generator_weak_heat {K : Set V} {U D : dirichletValue K}
    (hgraph : HilbertResolventNative.InGeneratorGraph («V» := dirichletForm K)
      (dirichletInclusion K) U (-D)) :
    ∃ v : dirichletForm K, dirichletInclusion K v = U ∧
      ∀ φ : supportedTests K,
        inner ℝ (intoDirichletValue K φ) D =
          -inner ℝ (testGradient K φ) (dirichletGradient K v) := by
  obtain ⟨v, hv, hpair⟩ :=
    (HilbertResolventNative.inGeneratorGraph_iff_variational
      («V» := dirichletForm K) (H := dirichletValue K) _ _ _).mp hgraph
  refine ⟨v, hv, ?_⟩
  intro φ
  have h := hpair (intoDirichletForm K φ)
  change inner ℝ (dirichletImage K φ) (v : DirichletAmbient K) =
    inner ℝ (intoDirichletValue K φ) (U + -D) at h
  rw [WithLp.prod_inner_apply] at h
  change inner ℝ (intoDirichletValue K φ) (dirichletInclusion K v) +
    inner ℝ (testGradient K φ) (dirichletGradient K v) =
      inner ℝ (intoDirichletValue K φ) (U + -D) at h
  rw [hv, inner_add_right, inner_neg_right] at h
  linarith only [h]

end PoincareMT.M35.Uniqueness.Heat
