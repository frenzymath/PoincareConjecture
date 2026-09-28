import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.DerivativeLipschitz
import Mathlib.Geometry.Manifold.Diffeomorph









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric

section Contraction

variable {m n : ℕ} {M N : Type*}
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin m)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 m) ∞ M] [IsManifold (𝓡 n) ∞ N]


theorem edist_le_of_tangentNorm_mfderiv_le
    (g : RiemannianMetric m M) (h : RiemannianMetric n N)
    {F : M → N} (hF : ContMDiff (𝓡 m) (𝓡 n) 1 F)
    (hbound : ∀ x v, h.tangentNorm (F x) (mfderiv (𝓡 m) (𝓡 n) F x v) ≤
      g.tangentNorm x v) (x y : M) : h.edist (F x) (F y) ≤ g.edist x y := by
  let : RiemannianBundle (TangentSpace (𝓡 m) : M → Type _) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) := ⟨h.toRiemannianMetric⟩
  change riemannianEDist (𝓡 n) (F x) (F y) ≤ riemannianEDist (𝓡 m) x y
  simp only [riemannianEDist, le_iInf_iff]
  intro γ hγ
  let η : Path (F x) (F y) := γ.map hF.continuous
  have hη : ContMDiff (𝓡∂ 1) (𝓡 n) 1 η := hF.comp hγ
  refine (biInf_le _ hη).trans ?_
  apply lintegral_mono
  intro t
  change ‖mfderiv (𝓡∂ 1) (𝓡 n) (F ∘ γ) t 1‖ₑ ≤ _
  rw [mfderiv_comp t (hF.mdifferentiable one_ne_zero (γ t))
    (hγ.mdifferentiable one_ne_zero t)]
  dsimp only
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (hbound (γ t) _)

end Contraction

section Product

variable {n : ℕ} {M N : Type*}
  [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin (n + 1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 (n + 1)) ∞ M] [IsManifold (𝓡 n) ∞ N]
  (g : RiemannianMetric (n + 1) M) (h : RiemannianMetric n N)
  (e : (N × ℝ) ≃ₘ⟮(𝓡 n).prod 𝓘(ℝ, ℝ), 𝓡 (n + 1)⟯ M)
  (hinner : ∀ (z : N × ℝ) (v w : TangentSpace ((𝓡 n).prod 𝓘(ℝ, ℝ)) z),
    g.inner (e z) (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z v)
      (mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e z w) =
      h.inner z.1 v.1 w.1 + v.2 * w.2)

include hinner

private theorem productIsometry_inner_symm (x : M)
    (v w : TangentSpace (𝓡 (n + 1)) x) :
    g.inner x v w =
      h.inner (e.symm x).1
        (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm x v).1
        (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm x w).1 +
      (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm x v).2 *
        (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm x w).2 := by
  have hcomp : e ∘ e.symm = id := by funext x; simp
  have hd := mfderiv_comp x (e.mdifferentiable (by simp) (e.symm x))
    (e.symm.mdifferentiable (by simp) x)
  rw [hcomp, mfderiv_id] at hd
  have hv := congrArg (fun A => A v) hd.symm
  have hw := congrArg (fun A => A w) hd.symm
  change mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e (e.symm x)
    (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm x v) = v at hv
  change mfderiv ((𝓡 n).prod 𝓘(ℝ, ℝ)) (𝓡 (n + 1)) e (e.symm x)
    (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm x w) = w at hw
  have hh := hinner (e.symm x)
    (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm x v)
    (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm x w)
  rw [hv, hw] at hh
  convert hh using 1
  rw [e.apply_symm_apply]


theorem productIsometry_fst_tangentNorm_le (x : M)
    (v : TangentSpace (𝓡 (n + 1)) x) :
    h.tangentNorm (e.symm x).1
      (mfderiv (𝓡 (n + 1)) (𝓡 n) (fun x => (e.symm x).1) x v) ≤
      g.tangentNorm x v := by
  have hd := mfderiv_comp x
    (mdifferentiable_fst (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) (e.symm x))
    (e.symm.mdifferentiable (by simp) x)
  change mfderiv (𝓡 (n + 1)) (𝓡 n) (fun x => (e.symm x).1) x = _ at hd
  rw [mfderiv_fst] at hd
  unfold tangentNorm
  rw [hd]
  apply Real.sqrt_le_sqrt
  have hh := productIsometry_inner_symm g h e hinner x v v
  rw [hh]
  change _ ≤ _ + _
  exact le_add_of_nonneg_right (mul_self_nonneg _)


theorem productIsometry_fst_edist_le (x y : M) :
    h.edist (e.symm x).1 (e.symm y).1 ≤ g.edist x y := by
  apply edist_le_of_tangentNorm_mfderiv_le g h
    ((contMDiff_fst.comp e.symm.contMDiff).of_le (by simp))
  exact productIsometry_fst_tangentNorm_le g h e hinner


theorem productIsometry_snd_tangentNorm_le (x : M)
    (v : TangentSpace (𝓡 (n + 1)) x) :
    |mvfderiv (𝓡 (n + 1)) (fun x => (e.symm x).2) x v| ≤
      g.tangentNorm x v := by
  have hd := mfderiv_comp x
    (mdifferentiable_snd (I := 𝓡 n) (I' := 𝓘(ℝ, ℝ)) (e.symm x))
    (e.symm.mdifferentiable (by simp) x)
  change mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ) (fun x => (e.symm x).2) x = _ at hd
  rw [mfderiv_snd] at hd
  change |(show ℝ from mfderiv (𝓡 (n + 1)) 𝓘(ℝ, ℝ)
    (fun x => (e.symm x).2) x v)| ≤ _
  rw [hd]
  change |(mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm x v).2| ≤ _
  rw [← Real.sqrt_mul_self_eq_abs]
  unfold tangentNorm
  apply Real.sqrt_le_sqrt
  rw [productIsometry_inner_symm g h e hinner x v v]
  apply le_add_of_nonneg_left
  by_cases hv : (mfderiv (𝓡 (n + 1)) ((𝓡 n).prod 𝓘(ℝ, ℝ)) e.symm x v).1 = 0
  · rw [hv]
    simp
  · exact (h.pos _ _ hv).le


theorem productIsometry_snd_edist_le (x y : M) :
    EDist.edist (e.symm x).2 (e.symm y).2 ≤ g.edist x y := by
  have he := g.edist_le_mul_edist_of_derivative_bound
    (f := fun x => (e.symm x).2)
    ((contMDiff_snd.comp e.symm.contMDiff).of_le (by simp))
    (K := 1) (by simp)
    (by simpa only [NNReal.coe_one, one_mul] using
      productIsometry_snd_tangentNorm_le g h e hinner) x y
  simpa only [ENNReal.coe_one, one_mul, Function.comp_apply] using he



theorem productIsometry_preimage_ball_subset (y : N) (r : ℝ) (hr : 0 < r) :
    e ⁻¹' g.ball (e (y, 0)) r ⊆ h.ball y r ×ˢ Ioo (-r) r := by
  intro z hz
  change g.edist (e (y, 0)) (e z) < ENNReal.ofReal r at hz
  have hf := (productIsometry_fst_edist_le g h e hinner (e (y, 0)) (e z)).trans_lt hz
  have hs := (productIsometry_snd_edist_le g h e hinner (e (y, 0)) (e z)).trans_lt hz
  simp only [e.symm_apply_apply] at hf hs
  refine ⟨hf, ?_⟩
  rw [edist_dist] at hs
  have hd : dist (0 : ℝ) z.2 < r := (ENNReal.ofReal_lt_ofReal_iff hr).mp hs
  simpa only [Real.dist_eq, zero_sub, abs_neg, abs_lt, mem_Ioo] using hd

end Product

end PoincareConjecture.RiemannianMetric
