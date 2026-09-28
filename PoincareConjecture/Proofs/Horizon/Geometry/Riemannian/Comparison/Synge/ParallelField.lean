import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Synge.LinearAlgebra
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Frame.Field
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Conjugate.Realization.Junction
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Volume.Transverse.RadialFrame
import Mathlib.Analysis.InnerProductSpace.NormDet

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff Manifold Bundle

namespace PoincareConjecture.Synge

open ConnectionAlongCurve ConnectionVariation

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M}

theorem exists_parallel_normal_field_of_negative_holonomy
    {q : ℝ → M} {I : Set ℝ} {a b : ℝ}
    (hab : a < b) (hI : IsOpen I) (hgeo : g.IsGeodesicOn q I)
    (hsub : Icc a b ⊆ I)
    (P : ℝ → EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hi : ∀ t ∈ Icc a b, (P t).IsInvertible)
    (hP : ∀ t ∈ Icc a b, ∀ u,
      ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s u)) t ∧
      manifoldCovDerivAlong g q (fun s => P s u) 1 t = 0)
    (hp : ∀ t ∈ Icc a b, ∀ u v,
      g.inner (q t) (P t u) (P t v) = inner ℝ u v)
    (F : M → M) (hend : q b = F (q a))
    (hF : ∀ u v, g.inner (F (q a))
      (mfderiv (𝓡 3) (𝓡 3) F (q a) u) (mfderiv (𝓡 3) (𝓡 3) F (q a) v) =
      g.inner (q a) u v)
    (hvelocity : mfderiv (𝓡 3) (𝓡 3) F (q a)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) q a 1) = mfderiv 𝓘(ℝ, ℝ) (𝓡 3) q b 1)
    (hne : mfderiv 𝓘(ℝ, ℝ) (𝓡 3) q a 1 ≠ 0)
    (hdet : LinearMap.det (((P b).inverse.comp
      ((mfderiv (𝓡 3) (𝓡 3) F (q a)).comp (P a))).toLinearMap) < 0) :
    ∃ w : EuclideanSpace ℝ (Fin 3), w ≠ 0 ∧
      P b w = mfderiv (𝓡 3) (𝓡 3) F (q a) (P a w) ∧
      ∀ t ∈ Icc a b,
        ContDiffAt ℝ ∞ (chartField q (q t) (fun s => P s w)) t ∧
        manifoldCovDerivAlong g q (fun s => P s w) 1 t = 0 ∧
        P t w ≠ 0 ∧
        g.inner (q t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) q t 1) (P t w) = 0 := by
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  let A := (P b).inverse.comp ((mfderiv (𝓡 3) (𝓡 3) F (q a)).comp (P a))
  have hA : ∀ u v, inner ℝ (A u) (A v) = inner ℝ u v := by
    intro u v
    rw [← hp b hb]
    change g.inner (q b) (P b ((P b).inverse _))
      (P b ((P b).inverse _)) = inner ℝ u v
    rw [(hi b hb).self_apply_inverse, (hi b hb).self_apply_inverse, hend]
    change g.inner (F (q a))
      (mfderiv (𝓡 3) (𝓡 3) F (q a) (P a u))
      (mfderiv (𝓡 3) (𝓡 3) F (q a) (P a v)) = inner ℝ u v
    exact (hF (P a u) (P a v)).trans (hp a ha u v)
  let L := A.toLinearMap.isometryOfInner hA
  let H : EuclideanSpace ℝ (Fin 3) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3) :=
    LinearIsometryEquiv.ofSurjective L
      (LinearMap.injective_iff_surjective.mp L.injective)
  have hHdet : H.toLinearMap.det = -1 := by
    have hn := L.normDet_eq_one
    rw [LinearMap.normDet_eq_abs_det] at hn
    change |A.toLinearMap.det| = 1 at hn
    rw [abs_of_neg hdet] at hn
    change A.toLinearMap.det = -1
    linarith
  let v := (P a).inverse (mfderiv 𝓘(ℝ, ℝ) (𝓡 3) q a 1)
  have hva : P a v = mfderiv 𝓘(ℝ, ℝ) (𝓡 3) q a 1 :=
    (hi a ha).self_apply_inverse _
  have hv : v ≠ 0 := by
    intro hz
    exact hne (by simpa [hz] using hva.symm)
  have hq : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ q I :=
    fun t ht => (Conjugate.Realization.contMDiffAt_of_isGeodesicOn hgeo ht).contMDiffWithinAt
  have hvt : ∀ t ∈ Icc a b, P t v = mfderiv 𝓘(ℝ, ℝ) (𝓡 3) q t 1 :=
    fun t ht => g.parallel_frame_velocity hab hI hgeo hq hsub hi hP v hva ht
  have hHv : H v = v := by
    change (P b).inverse (mfderiv (𝓡 3) (𝓡 3) F (q a) (P a v)) = v
    rw [hva, hvelocity, ← hvt b hb, (hi b hb).inverse_apply_self]
  obtain ⟨w, hw, hvw, hHw⟩ :=
    exists_ne_zero_orthogonal_fixed_of_finrank_three_det_neg_one H
      (by simp) hHdet hv hHv
  refine ⟨w, hw, ?_, ?_⟩
  · have he := congrArg (P b) hHw
    change P b ((P b).inverse (mfderiv (𝓡 3) (𝓡 3) F (q a) (P a w))) = P b w at he
    rw [(hi b hb).self_apply_inverse] at he
    exact he.symm
  · intro t ht
    refine ⟨(hP t ht w).1, (hP t ht w).2, ?_, ?_⟩
    · exact fun hz => hw ((hi t ht).injective (hz.trans (map_zero (P t)).symm))
    · rw [← hvt t ht, hp t ht, hvw]

end PoincareConjecture.Synge
