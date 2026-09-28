import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Frame.Negative
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Volume.Conjugate.Variation.Minimizing

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.Conjugate

open ConnectionAlongCurve ConnectionVariation

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem jacobi_ne_zero_of_minimizing
    (g : RiemannianMetric n M) (D : LeviCivitaData g) {γ : ℝ → M} {I : Set ℝ}
    {J : (t : ℝ) → TangentSpace (𝓡 n) (γ t)} {a b c C : ℝ}
    (ha : a < 0) (hb : 1 < b) (hc : c ∈ Ioo (0 : ℝ) 1)
    (hI : IsOpen I) (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ I)
    (hgeo : g.IsGeodesicOn γ I) (hsub : Icc a b ⊆ I)
    (hJ : ∀ t ∈ I, ContDiffAt ℝ ∞ (chartField γ (γ t) J) t)
    (hjac : ∀ t ∈ Icc (0 : ℝ) 1,
      manifoldCovDerivAlong g γ (manifoldCovDerivAlong g γ J 1) 1 t =
        -D.curvature (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1))
    (hJ0 : J 0 = 0) (hDJ0 : manifoldCovDerivAlong g γ J 1 0 ≠ 0)
    (hC : 0 < C)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = C)
    (hmin : g.edist (γ 0) (γ 1) = ENNReal.ofReal C) : J c ≠ 0 := by
  intro hJc
  obtain ⟨V₀, V₁, hV₀, hV₁, hleft, hright, hmatch, hneg⟩ :=
    ConjugateFrame.exists_negative_intrinsic_split D ha hb hc hI hγ hsub hJ hjac hJ0 hJc hDJ0
  have h01 : Icc (0 : ℝ) 1 ⊆ Ioo a b :=
    fun _ ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hb⟩
  have hn := Realization.index_nonneg_of_minimizing g D hc.1 hc.2 isOpen_Ioo h01
    (fun t ht => hgeo t (hsub (Ioo_subset_Icc_self ht))) hV₀ hV₁ hmatch hleft hright
    hC hspeed (by simpa using hmin)
  exact (not_lt_of_ge hn) hneg

end PoincareConjecture.Conjugate
