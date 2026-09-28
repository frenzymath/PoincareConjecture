import PoincareConjecture.Proofs.M35.Uniqueness.Heat.RawCoordinateOperator
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Limit.RicciConvergence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set
open scoped Manifold ContDiff Bundle Topology Matrix.Norms.Elementwise

namespace PoincareConjecture.M35.Uniqueness.Heat

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin n)

def rawCoordinateGram (g : RiemannianMetric n V) (x : V) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => g.inner x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)

theorem rawCoordinateGram_contDiff (g : RiemannianMetric n V) :
    ContDiff ℝ ∞ (rawCoordinateGram g) := by
  apply contDiff_pi.mpr
  intro i
  apply contDiff_pi.mpr
  intro j
  exact ((contDiff_iff_contDiffAt.mpr g.contDiffAt_euclideanCoefficients).clm_apply
    contDiff_const).clm_apply contDiff_const

theorem rawCoordinateGram_posDef (g : RiemannianMetric n V) (x : V) :
    (rawCoordinateGram g x).PosDef := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : V → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let b : Module.Basis (Fin n) ℝ (TangentSpace (𝓡 n) x) :=
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hb (i : Fin n) : b i = EuclideanSpace.single i 1 :=
    EuclideanSpace.basisFun_apply (Fin n) ℝ i
  have hg : rawCoordinateGram g x = Matrix.gram ℝ b := by
    ext i j
    change g.inner x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) =
      g.inner x (b i) (b j)
    rw [hb, hb]
  rw [hg]
  exact Matrix.posDef_gram_of_linearIndependent b.linearIndependent


def rawHeatPrincipalSymbol (g : RiemannianMetric n V) (x : V) (ℓ : V →L[ℝ] ℝ) : ℝ :=
  DeTurckNative.quadratic (rawCoordinateGram g x)⁻¹
    (fun i => ℓ (EuclideanSpace.single i 1))


theorem rawHeatPrincipalSymbol_eq_inverse_gram (g : RiemannianMetric n V)
    (x : V) (ℓ : V →L[ℝ] ℝ) :
    rawHeatPrincipalSymbol g x ℓ =
      DeTurckNative.quadratic (rawCoordinateGram g x)⁻¹
        (fun i => ℓ (EuclideanSpace.single i 1)) := rfl



theorem exists_raw_compact_ellipticity (g : RiemannianMetric n V)
    {K : Set V} (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ ℓ : V →L[ℝ] ℝ,
      c * ‖fun i : Fin n => ℓ (EuclideanSpace.single i 1)‖ ^ 2 ≤
        rawHeatPrincipalSymbol g x ℓ := by
  obtain ⟨c, hc, hb⟩ := DeTurckNative.exists_uniform_inverse_quadratic_lower_bound
    (rawCoordinateGram g) hK (rawCoordinateGram_contDiff g).continuous.continuousOn
    (fun x _ => rawCoordinateGram_posDef g x)
  refine ⟨c, hc, ?_⟩
  intro x hx ℓ
  rw [rawHeatPrincipalSymbol_eq_inverse_gram]
  exact hb x hx _



theorem exists_raw_compact_principal_bound (g : RiemannianMetric n V)
    {K : Set V} (hK : IsCompact K) :
    ∃ B : ℝ, 0 < B ∧ ∀ x ∈ K, ‖(rawCoordinateGram g x)⁻¹‖ ≤ B := by
  have hc := DeTurckNative.continuousOn_inverse_posDef (K := K) (rawCoordinateGram g)
    (rawCoordinateGram_contDiff g).continuous.continuousOn
    (fun x _ => rawCoordinateGram_posDef g x)
  obtain ⟨B, hB, hb⟩ := (hK.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  exact ⟨B, hB, fun x hx => hb _ ⟨x, hx, rfl⟩⟩

end PoincareConjecture.M35.Uniqueness.Heat
