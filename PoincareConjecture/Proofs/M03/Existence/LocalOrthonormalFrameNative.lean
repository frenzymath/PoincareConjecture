import PoincareConjecture.Proofs.M03.Existence.CoordinateFrameNative
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection










set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

noncomputable section

universe u

namespace PoincareConjecture.ParsevalFrameNative

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)

def metricGramSchmidt (g : RiemannianMetric n M)
    (F : Fin n → (x : M) → TangentSpace (𝓡 n) x) (i : Fin n) (x : M) :
    TangentSpace (𝓡 n) x :=
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  InnerProductSpace.gramSchmidt ℝ (fun j => F j x) i

def metricOrthonormalize (g : RiemannianMetric n M)
    (F : Fin n → (x : M) → TangentSpace (𝓡 n) x) (i : Fin n) (x : M) :
    TangentSpace (𝓡 n) x :=
  (Real.sqrt (g.inner x (metricGramSchmidt g F i x) (metricGramSchmidt g F i x)))⁻¹ •
    metricGramSchmidt g F i x

theorem metricGramSchmidt_ne_zero (g : RiemannianMetric n M)
    (F : Fin n → (x : M) → TangentSpace (𝓡 n) x) (x : M)
    (hF : LinearIndependent ℝ (fun j => F j x)) (i : Fin n) :
    metricGramSchmidt g F i x ≠ 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact InnerProductSpace.gramSchmidt_ne_zero i hF

theorem metricGramSchmidt_recurrence (g : RiemannianMetric n M)
    (F : Fin n → (x : M) → TangentSpace (𝓡 n) x) (i : Fin n) (x : M) :
    metricGramSchmidt g F i x = F i x -
      ∑ j ∈ Finset.Iio i,
        (g.inner x (metricGramSchmidt g F j x) (F i x) /
          g.inner x (metricGramSchmidt g F j x) (metricGramSchmidt g F j x)) •
            metricGramSchmidt g F j x := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply eq_sub_iff_add_eq.mpr
  have h := InnerProductSpace.gramSchmidt_def'' ℝ (fun j => F j x) i
  change metricGramSchmidt g F i x +
    (∑ j ∈ Finset.Iio i,
      (inner ℝ (metricGramSchmidt g F j x) (F i x) /
        inner ℝ (metricGramSchmidt g F j x) (metricGramSchmidt g F j x)) •
          metricGramSchmidt g F j x) = F i x
  simpa only [metricGramSchmidt, real_inner_self_eq_norm_sq,
    RCLike.ofReal_real_eq_id, id_eq] using h.symm

theorem contMDiffOn_scalar_inverse {s : Set M} {f : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f s) (hzero : ∀ x ∈ s, f x ≠ 0) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => (f x)⁻¹) s := by
  intro x hx
  exact ((contDiffAt_inv ℝ (hzero x hx)).contMDiffAt).comp_contMDiffWithinAt x (hf x hx)

theorem contMDiffOn_scalar_sqrt {s : Set M} {f : M → ℝ}
    (hf : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ f s) (hzero : ∀ x ∈ s, f x ≠ 0) :
    ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞ (fun x => Real.sqrt (f x)) s := by
  intro x hx
  exact (Real.contDiffAt_sqrt (hzero x hx)).contMDiffAt.comp_contMDiffWithinAt x (hf x hx)


theorem metricGramSchmidt_contMDiffOn (g : RiemannianMetric n M)
    (F : Fin n → (x : M) → TangentSpace (𝓡 n) x) {U : Set M}
    (hF : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (F i)) U)
    (hlin : ∀ x ∈ U, LinearIndependent ℝ (fun i => F i x)) (i : Fin n) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (metricGramSchmidt g F i)) U := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  induction i using Fin.strong_induction_on with
  | h i ih =>
      have hterm (j : Fin n) (hj : j ∈ Finset.Iio i) :
          ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞
            (T% (fun x =>
              (g.inner x (metricGramSchmidt g F j x) (F i x) /
                g.inner x (metricGramSchmidt g F j x) (metricGramSchmidt g F j x)) •
                  metricGramSchmidt g F j x)) U := by
        have hs := ih j (Finset.mem_Iio.mp hj)
        have hden : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
            (fun x => g.inner x (metricGramSchmidt g F j x) (metricGramSchmidt g F j x)) U :=
          hs.inner_bundle hs
        have hnonzero : ∀ x ∈ U,
            g.inner x (metricGramSchmidt g F j x) (metricGramSchmidt g F j x) ≠ 0 :=
          fun x hx => ne_of_gt (g.pos x _ (metricGramSchmidt_ne_zero g F x (hlin x hx) j))
        have hnum : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
            (fun x => g.inner x (metricGramSchmidt g F j x) (F i x)) U :=
          hs.inner_bundle (hF i)
        have hcoef : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
            (fun x => g.inner x (metricGramSchmidt g F j x) (F i x) /
              g.inner x (metricGramSchmidt g F j x) (metricGramSchmidt g F j x)) U := by
          simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_def, div_eq_mul_inv] using
            hnum.smul (contMDiffOn_scalar_inverse hden hnonzero)
        exact hcoef.smul_section hs
      have hsum := ContMDiffOn.sum_section hterm
      have hrec := (hF i).sub_section hsum
      convert hrec using 1
      funext x
      exact congrArg (fun v : TangentSpace (𝓡 n) x => (⟨x, v⟩ : TangentBundle (𝓡 n) M))
        (metricGramSchmidt_recurrence g F i x)

theorem metricOrthonormalize_contMDiffOn (g : RiemannianMetric n M)
    (F : Fin n → (x : M) → TangentSpace (𝓡 n) x) {U : Set M}
    (hF : ∀ i, ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (F i)) U)
    (hlin : ∀ x ∈ U, LinearIndependent ℝ (fun i => F i x)) (i : Fin n) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (metricOrthonormalize g F i)) U := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hGS := metricGramSchmidt_contMDiffOn g F hF hlin i
  have hsq : ContMDiffOn (𝓡 n) 𝓘(ℝ, ℝ) ∞
      (fun x => g.inner x (metricGramSchmidt g F i x) (metricGramSchmidt g F i x)) U :=
    hGS.inner_bundle hGS
  have hpos : ∀ x ∈ U,
      0 < g.inner x (metricGramSchmidt g F i x) (metricGramSchmidt g F i x) :=
    fun x hx => g.pos x _ (metricGramSchmidt_ne_zero g F x (hlin x hx) i)
  exact (contMDiffOn_scalar_inverse
    (contMDiffOn_scalar_sqrt hsq (fun x hx => ne_of_gt (hpos x hx)))
    (fun x hx => ne_of_gt (Real.sqrt_pos.mpr (hpos x hx)))).smul_section hGS

theorem metricOrthonormalize_eq_gramSchmidtNormed (g : RiemannianMetric n M)
    (F : Fin n → (x : M) → TangentSpace (𝓡 n) x) (i : Fin n) (x : M) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    metricOrthonormalize g F i x =
      InnerProductSpace.gramSchmidtNormed ℝ (fun j => F j x) i := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change (Real.sqrt (inner ℝ (metricGramSchmidt g F i x) (metricGramSchmidt g F i x)))⁻¹ •
      metricGramSchmidt g F i x = _
  rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  rfl

theorem metricOrthonormalize_sum_repr (g : RiemannianMetric n M)
    (F : Fin n → (x : M) → TangentSpace (𝓡 n) x) (x : M)
    (hlin : LinearIndependent ℝ (fun i => F i x))
    (hspan : Submodule.span ℝ (range (fun i => F i x)) = ⊤)
    (v : TangentSpace (𝓡 n) x) :
    (∑ i, g.inner x (metricOrthonormalize g F i x) v • metricOrthonormalize g F i x) = v := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have horth := InnerProductSpace.gramSchmidtNormed_orthonormal hlin
  have hsp : Submodule.span ℝ (range (InnerProductSpace.gramSchmidtNormed ℝ (fun i => F i x))) = ⊤ := by
    rw [InnerProductSpace.span_gramSchmidtNormed_range, InnerProductSpace.span_gramSchmidt, hspan]
  let b := OrthonormalBasis.mk horth hsp.ge
  have hb := b.sum_repr' v
  change (∑ i, inner ℝ (metricOrthonormalize g F i x) v • metricOrthonormalize g F i x) = v
  simpa only [b, OrthonormalBasis.coe_mk,
    metricOrthonormalize_eq_gramSchmidtNormed] using hb

def chartOrthonormalFrame (g : RiemannianMetric n M) (p : M) (i : Fin n) :
    (x : M) → TangentSpace (𝓡 n) x :=
  metricOrthonormalize g (DeTurckNative.chartFrame p) i

theorem chartOrthonormalFrame_contMDiffOn (g : RiemannianMetric n M) (p : M) (i : Fin n) :
    ContMDiffOn (𝓡 n) ((𝓡 n).prod 𝓘(ℝ, E)) ∞ (T% (chartOrthonormalFrame g p i))
      (chartAt E p).source := by
  apply metricOrthonormalize_contMDiffOn g (DeTurckNative.chartFrame p)
    (DeTurckNative.chartFrame_contMDiffOn p)
  intro x hx
  convert (DeTurckNative.chartFrameBasis p x hx).linearIndependent using 1
  funext j
  exact DeTurckNative.chartFrame_eq_basis p x hx j

theorem chartOrthonormalFrame_sum_repr (g : RiemannianMetric n M) (p : M)
    (x : M) (hx : x ∈ (chartAt E p).source) (v : TangentSpace (𝓡 n) x) :
    (∑ i, g.inner x (chartOrthonormalFrame g p i x) v • chartOrthonormalFrame g p i x) = v := by
  have hlin : LinearIndependent ℝ (fun i => DeTurckNative.chartFrame (n := n) p i x) := by
    convert (DeTurckNative.chartFrameBasis p x hx).linearIndependent using 1
    funext j
    exact DeTurckNative.chartFrame_eq_basis p x hx j
  have hspan : Submodule.span ℝ (range (fun i => DeTurckNative.chartFrame (n := n) p i x)) = ⊤ := by
    rw [show (fun i => DeTurckNative.chartFrame (n := n) p i x) =
      (fun i => DeTurckNative.chartFrameBasis p x hx i) from
        funext (DeTurckNative.chartFrame_eq_basis p x hx)]
    exact (DeTurckNative.chartFrameBasis p x hx).span_eq
  exact metricOrthonormalize_sum_repr g (DeTurckNative.chartFrame p) x hlin hspan v

end PoincareConjecture.ParsevalFrameNative

end
