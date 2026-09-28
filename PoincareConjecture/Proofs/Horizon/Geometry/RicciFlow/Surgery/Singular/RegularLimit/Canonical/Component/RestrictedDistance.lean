import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Spacetime.RegularBox
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Metric.Distance.IntrinsicIsometry

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set TopologicalSpace
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.SingularRegularLimit

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]

theorem pathELength_subtypeVal (U : Opens M) (g : RiemannianMetric 3 M)
    (gU : RiemannianMetric 3 U)
    (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      g.inner (x : M) (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x w) = gU.inner x v w)
    {γ : ℝ → U} (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc (0 : ℝ) 1)) :
    g.pathELength (Subtype.val ∘ γ) 0 1 = gU.pathELength γ 0 1 :=
  MetricSurgery.pathELength_comp_eq_of_pullback gU g
    (U := univ) (fun _ _ => contMDiff_subtype_val.contMDiffAt)
    (fun x _ v w => hmetric x v w) hγ (subset_univ _)

private theorem pathELength_eq_of_eqOn (g : RiemannianMetric 3 M)
    {γ δ : ℝ → M} (h : EqOn γ δ (Icc (0 : ℝ) 1)) :
    g.pathELength γ 0 1 = g.pathELength δ 0 1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.pathELength_congr h

theorem intrinsicEDist_restrictToOpen (U : Opens M) (g : RiemannianMetric 3 M)
    (gU : RiemannianMetric 3 U)
    (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      g.inner (x : M) (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x w) = gU.inner x v w)
    (K : Set M) (hKU : K ⊆ U) (x y : U) :
    intrinsicEDist gU ((Subtype.val : U → M) ⁻¹' K) x y =
      intrinsicEDist g K (x : M) (y : M) := by
  unfold intrinsicEDist
  congr 1
  ext L
  constructor
  · rintro ⟨γ, hγ, h0, h1, hK, rfl⟩
    refine ⟨Subtype.val ∘ γ,
      contMDiff_subtype_val.comp_contMDiffOn hγ,
      by simp [h0], by simp [h1], ?_, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      exact hK ⟨t, ht, rfl⟩
    · exact (pathELength_subtypeVal U g gU hmetric hγ).symm
  · rintro ⟨γ, hγ, h0, h1, hK, rfl⟩
    let δ : ℝ → U := openRetraction U x ∘ γ
    have hδval : EqOn (Subtype.val ∘ δ) γ (Icc (0 : ℝ) 1) := by
      intro t ht
      exact openRetraction_val U x (hKU (hK ⟨t, ht, rfl⟩))
    have hδ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 δ (Icc (0 : ℝ) 1) := by
      apply MetricSurgery.path_contMDiffOn_comp_at (U := U) _ hγ
        (fun z hz => hKU (hK hz))
      intro z hz
      have hk : ContMDiffWithinAt (𝓡 3) (𝓡 3) ∞ (openRetraction U x) U z := by
        rw [← ContMDiffWithinAt.subtypeVal_comp_iff U]
        exact contMDiffWithinAt_id.congr_of_mem
          (fun w hw => openRetraction_val U x hw) hz
      exact hk.contMDiffAt (U.isOpen.mem_nhds hz)
    refine ⟨δ, hδ, ?_, ?_, ?_, ?_⟩
    · apply Subtype.ext
      exact (hδval (by norm_num)).trans h0
    · apply Subtype.ext
      exact (hδval (by norm_num)).trans h1
    · rintro _ ⟨t, ht, rfl⟩
      change (Subtype.val ∘ δ) t ∈ K
      rw [hδval ht]
      exact hK ⟨t, ht, rfl⟩
    · exact (pathELength_eq_of_eqOn g hδval).symm.trans
        (pathELength_subtypeVal U g gU hmetric hδ)

theorem intrinsicDiameter_restrictToOpen (U : Opens M) (g : RiemannianMetric 3 M)
    (gU : RiemannianMetric 3 U)
    (hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x),
      g.inner (x : M) (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → M) x w) = gU.inner x v w)
    (K : Set M) (hKU : K ⊆ U) :
    intrinsicDiameter gU ((Subtype.val : U → M) ⁻¹' K) = intrinsicDiameter g K := by
  unfold intrinsicDiameter
  congr 1
  ext L
  constructor
  · rintro ⟨⟨x, y⟩, rfl⟩
    exact ⟨(⟨x.val.val, x.property⟩, ⟨y.val.val, y.property⟩),
      (intrinsicEDist_restrictToOpen U g gU hmetric K hKU x.val y.val).symm⟩
  · rintro ⟨⟨x, y⟩, rfl⟩
    refine ⟨(⟨⟨x.val, hKU x.property⟩, x.property⟩,
      ⟨⟨y.val, hKU y.property⟩, y.property⟩), ?_⟩
    exact intrinsicEDist_restrictToOpen U g gU hmetric K hKU
      ⟨x.val, hKU x.property⟩ ⟨y.val, hKU y.property⟩

end PoincareConjecture.SingularRegularLimit
