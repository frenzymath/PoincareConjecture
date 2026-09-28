import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Green.CompactSupport
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Linearity
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Bundle InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

def testFunctions (Ω : Set M) : Submodule ℝ (M → ℝ) where
  carrier := {f | ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f ∧
    HasCompactSupport f ∧ tsupport f ⊆ Ω}
  zero_mem' := ⟨contMDiff_const, by simp [HasCompactSupport], by simp⟩
  add_mem' := by
    intro f h hf hh
    refine ⟨hf.1.add hh.1, hf.2.1.add hh.2.1, ?_⟩
    exact (tsupport_add (f := f) (g := h)).trans (union_subset hf.2.2 hh.2.2)
  smul_mem' := by
    intro c f hf
    refine ⟨contMDiff_const.mul hf.1, hf.2.1.smul_left, ?_⟩
    exact (closure_mono (Function.support_const_smul_subset c f)).trans hf.2.2

def EnergyTest (_D : LeviCivitaData g) (Ω : Set M) := ↥(testFunctions (n := n) Ω)

variable (D : LeviCivitaData g) (Ω : Set M)

instance : AddCommGroup (EnergyTest D Ω) := inferInstanceAs (AddCommGroup ↥(testFunctions Ω))
instance : Module ℝ (EnergyTest D Ω) := inferInstanceAs (Module ℝ ↥(testFunctions Ω))

instance : CoeFun (EnergyTest D Ω) (fun _ => M → ℝ) := ⟨fun f => f.1⟩

variable {D Ω}

theorem EnergyTest.smooth (f : EnergyTest D Ω) :
    ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ (f : M → ℝ) := by exact f.2.1

theorem EnergyTest.hasCompactSupport (f : EnergyTest D Ω) :
    HasCompactSupport (f : M → ℝ) := by exact f.2.2.1

theorem EnergyTest.support_subset (f : EnergyTest D Ω) :
    tsupport (f : M → ℝ) ⊆ Ω := by exact f.2.2.2

@[simp] theorem EnergyTest.coe_add (f h : EnergyTest D Ω) :
    ⇑(f + h) = fun x => f x + h x := rfl

@[simp] theorem EnergyTest.coe_smul (c : ℝ) (f : EnergyTest D Ω) :
    ⇑(c • f) = fun x => c * f x := rfl

variable [MeasurableSpace M] [BorelSpace M] [T3Space M]

theorem EnergyTest.integrable_mul (f h : EnergyTest D Ω) :
    Integrable (fun x => f x * h x) g.volumeMeasure :=
  (f.smooth.continuous.mul h.smooth.continuous).integrable_of_hasCompactSupport
    f.hasCompactSupport.mul_right

theorem EnergyTest.integrable_gradient (f h : EnergyTest D Ω) :
    Integrable (fun x => g.inner x (D.gradient f x) (D.gradient h x)) g.volumeMeasure :=
  D.integrable_inner_gradient f.smooth h.smooth f.hasCompactSupport

def energyInner (f h : EnergyTest D Ω) : ℝ :=
  (∫ x, f x * h x ∂g.volumeMeasure) +
    ∫ x, g.inner x (D.gradient f x) (D.gradient h x) ∂g.volumeMeasure

theorem energyInner_symm (f h : EnergyTest D Ω) : energyInner f h = energyInner h f := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  unfold energyInner
  congr 1
  · exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change inner ℝ (D.gradient f x) (D.gradient h x) =
        inner ℝ (D.gradient h x) (D.gradient f x)
      exact real_inner_comm _ _

theorem integral_gradient_self_nonneg (f : EnergyTest D Ω) :
    0 ≤ ∫ x, g.inner x (D.gradient f x) (D.gradient f x) ∂g.volumeMeasure := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply integral_nonneg
  intro x
  change 0 ≤ inner ℝ (D.gradient f x) (D.gradient f x)
  exact real_inner_self_nonneg

theorem energyInner_nonneg (f : EnergyTest D Ω) : 0 ≤ energyInner f f :=
  add_nonneg (integral_nonneg fun x => mul_self_nonneg (f x)) (integral_gradient_self_nonneg f)

theorem energyInner_add_left (f h k : EnergyTest D Ω) :
    energyInner (f + h) k = energyInner f k + energyInner h k := by
  have hgrad (x : M) : D.gradient (fun y => f y + h y) x = D.gradient f x + D.gradient h x :=
    D.gradient_add ((f.smooth x).mdifferentiableAt (by simp))
      ((h.smooth x).mdifferentiableAt (by simp))
  simp only [energyInner, EnergyTest.coe_add, add_mul, hgrad, map_add, add_apply,
    integral_add (f.integrable_mul k) (h.integrable_mul k),
    integral_add (f.integrable_gradient k) (h.integrable_gradient k)]
  ring

theorem energyInner_smul_left (c : ℝ) (f h : EnergyTest D Ω) :
    energyInner (c • f) h = c * energyInner f h := by
  have hgrad (x : M) : D.gradient (fun y => c * f y) x = c • D.gradient f x := by
    apply (g.inner_isInvertible x).injective
    ext v
    simp only [D.inner_gradient, mvfderiv_const_mul,
      map_smul, smul_apply, smul_eq_mul]
  simp only [energyInner, EnergyTest.coe_smul, hgrad, map_smul, smul_apply,
    smul_eq_mul, mul_assoc, integral_const_mul]
  ring

instance : PreInnerProductSpace.Core ℝ (EnergyTest D Ω) where
  inner := energyInner
  conj_inner_symm f h := energyInner_symm h f
  re_inner_nonneg := energyInner_nonneg
  add_left := energyInner_add_left
  smul_left f h c := energyInner_smul_left c f h

instance : SeminormedAddCommGroup (EnergyTest D Ω) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

instance : InnerProductSpace ℝ (EnergyTest D Ω) := InnerProductSpace.ofCore _

@[simp] theorem EnergyTest.inner_eq (f h : EnergyTest D Ω) :
    ⟪f, h⟫_ℝ = energyInner f h := rfl

abbrev H1Zero (D : LeviCivitaData g) (Ω : Set M) := UniformSpace.Completion (EnergyTest D Ω)

theorem EnergyTest.norm_sq (f : EnergyTest D Ω) : ‖f‖ ^ 2 = energyInner f f :=
  (real_inner_self_eq_norm_sq f).symm

theorem energyInner_eq_integral_oneSubLaplacian [PreconnectedSpace M]
    (f h : EnergyTest D Ω) :
    energyInner f h = ∫ x, (f x - D.laplacian f x) * h x ∂g.volumeMeasure := by
  have hgreen := D.integral_mul_laplacian h.smooth f.smooth h.hasCompactSupport
  have hsymm : (∫ x, g.inner x (D.gradient f x) (D.gradient h x) ∂g.volumeMeasure) =
      ∫ x, g.inner x (D.gradient h x) (D.gradient f x) ∂g.volumeMeasure := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change inner ℝ (D.gradient f x) (D.gradient h x) =
        inner ℝ (D.gradient h x) (D.gradient f x)
      exact real_inner_comm _ _
  have heq : (fun x => (f x - D.laplacian f x) * h x) =
      fun x => f x * h x - h x * D.laplacian f x := by funext x; ring
  rw [heq, integral_sub (f.integrable_mul h)
    (D.integrable_mul_laplacian h.smooth f.smooth h.hasCompactSupport)]
  unfold energyInner
  rw [hsymm, hgreen]
  ring

end PoincareConjecture.LeviCivitaData.Dirichlet
