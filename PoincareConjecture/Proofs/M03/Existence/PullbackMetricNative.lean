import PoincareConjecture.Definitions.Ch01.RiemannianMetric
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection










set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Manifold ContDiff Bundle

noncomputable section

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "FiberBilin" =>
  fun x : M => TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ

noncomputable def pinner (g : RiemannianMetric n M)
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) (x : M) :
    TangentSpace (𝓡 n) x →L[ℝ] TangentSpace (𝓡 n) x →L[ℝ] ℝ := by
  letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let A := Φ.mfderivToContinuousLinearEquiv (by simp) x
  exact (((ContinuousLinearMap.precompL (𝕜 := ℝ) (TangentSpace (𝓡 n) x)
    (g.inner (Φ x))) A.toContinuousLinearMap).comp A.toContinuousLinearMap).flip

theorem pinner_apply (g : RiemannianMetric n M)
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) (x : M)
    (v w : TangentSpace (𝓡 n) x) :
    pinner g Φ x v w = g.inner (Φ x) (mfderiv (𝓡 n) (𝓡 n) Φ x v)
      (mfderiv (𝓡 n) (𝓡 n) Φ x w) := by
  simp [pinner, Diffeomorph.mfderivToContinuousLinearEquiv_coe]

noncomputable def pullbackMetric (g : RiemannianMetric n M)
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞)
    (hsmooth : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) x (pinner g Φ x))) :
    RiemannianMetric n M where
  inner := pinner g Φ
  symm x v w := by
    rw [pinner_apply, pinner_apply, g.symm]
  pos x v hv := by
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let A := Φ.mfderivToContinuousLinearEquiv (by simp) x
    apply g.pos (Φ x) (A v)
    intro hz
    apply hv
    exact A.injective (by simpa using hz)
  isVonNBounded x := by
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let A := Φ.mfderivToContinuousLinearEquiv (by simp) x
    let Ainv := A.symm.toContinuousLinearMap
    refine ((g.isVonNBounded (Φ x)).image Ainv).subset ?_
    intro v hv
    refine ⟨A v, ?_, ?_⟩
    · change g.inner (Φ x) (A v) (A v) < 1
      exact hv
    · exact A.symm_apply_apply v
  contMDiff := hsmooth

theorem pullbackMetric_inner (g : RiemannianMetric n M)
    (Φ : Diffeomorph (𝓡 n) (𝓡 n) M M ∞) (hsmooth : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) x (pinner g Φ x)))
    (x : M) (v w : TangentSpace (𝓡 n) x) :
    (pullbackMetric g Φ hsmooth).inner x v w =
      g.inner (Φ x) (mfderiv (𝓡 n) (𝓡 n) Φ x v)
        (mfderiv (𝓡 n) (𝓡 n) Φ x w) := by
  exact pinner_apply g Φ x v w

theorem pullbackMetric_refl (g : RiemannianMetric n M)
    (hsmooth : ContMDiff (𝓡 n)
      ((𝓡 n).prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x : M => Bundle.TotalSpace.mk'
        (E →L[ℝ] E →L[ℝ] ℝ) x
          (pinner g (Diffeomorph.refl (𝓡 n) M ∞) x))) :
    pullbackMetric g (Diffeomorph.refl (𝓡 n) M ∞) hsmooth = g := by
  have hinner : ∀ x (v w : TangentSpace (𝓡 n) x),
      (pullbackMetric g (Diffeomorph.refl (𝓡 n) M ∞) hsmooth).inner x v w =
        g.inner x v w := by
    intro x v w
    rw [pullbackMetric_inner]
    simp only [Diffeomorph.coe_refl, mfderiv_id,
      ContinuousLinearMap.id_apply, id_eq]
    change g.inner x v w = g.inner x v w
    rfl
  have hp := hinner
  cases h₁ : pullbackMetric g (Diffeomorph.refl (𝓡 n) M ∞) hsmooth
  cases h₂ : g
  rw [h₁, h₂] at hp
  simp only [Bundle.ContMDiffRiemannianMetric.mk.injEq]
  funext x
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  exact hp x v w

end PoincareConjecture
