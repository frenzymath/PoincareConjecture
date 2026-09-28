import PoincareConjecture.Proofs.M32.Claim11_34.SurfaceEuler
import PoincareConjecture.Proofs.M04.ScalarEvolution
import PoincareConjecture.Proofs.M04.ScalarStrongMaximum
import Mathlib.Topology.Order.Compact

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.M32

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [CompactSpace M] [ConnectedSpace M]

theorem compact_surface_scalar_positive_on_Ioc
    {a b : ℝ} (hab : a < b) (H : RicciFlow 2 M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x, (H.connection t).NonnegativeCurvatureOperator x)
    (p : M) (hp : 0 < (H.connection b).scalarCurvature p) :
    ∀ t ∈ Ioc a b, ∀ x, 0 < (H.connection t).scalarCurvature x := by
  classical
  obtain ⟨chi, hchi, hintegral⟩ := compact_surface_total_scalar_euler_alternative
    (H.metric b) (H.connection b) (hoperator b ⟨hab.le, le_rfl⟩) p hp
  have hchiPos : 0 < (chi : ℝ) := by
    rcases hchi with rfl | rfl <;> norm_num
  have hintegralPos (s : ℝ) :
      0 < ∫ x, (H.connection s).scalarCurvature x ∂(H.metric s).volumeMeasure := by
    rw [hintegral (H.metric s) (H.connection s)]
    positivity
  have hseed (s : ℝ) : ∃ q : M, 0 < (H.connection s).scalarCurvature q := by
    by_contra h
    push Not at h
    exact (not_le_of_gt (hintegralPos s)) (integral_nonpos h)
  let f : ℝ → M → ℝ := fun t x => (H.connection t).scalarCurvature x
  let v : ℝ → M → ℝ := fun t x =>
    (H.connection t).laplacian (H.connection t).scalarCurvature x +
      2 * (H.connection t).ricciNormSq x
  have hf : ContinuousOn (Function.uncurry f) (Icc a b ×ˢ univ) :=
    H.contMDiffOn_scalarCurvature.continuousOn
  have hnonneg (t : ℝ) (ht : t ∈ Icc a b) (x : M) : 0 ≤ f t x := by
    dsimp only [f]
    unfold LeviCivitaData.scalarCurvature LeviCivitaData.ricci
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      (H.connection t).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
        x (hoperator t ht x) _ _
  have hevol (t : ℝ) (x : M) : (H.connection t).laplacian (f t) x ≤ v t x := by
    have hnorm : 0 ≤ (H.connection t).ricciNormSq x :=
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
    dsimp only [f, v]
    linarith
  intro t ht x
  let s := (a + t) / 2
  have has : a ≤ s := by dsimp only [s]; linarith [ht.1]
  have hst : s < t := by dsimp only [s]; linarith [ht.1]
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc has ht.2
  obtain ⟨q, hq⟩ := hseed s
  exact M04.ricciFlow_supersolution_positive_at_later_time hst H hsub f v
    (hf.mono (prod_mono hsub Subset.rfl))
    (fun tau htau y => (H.hasDerivWithinAt_scalarCurvature tau (hsub htau) y).mono hsub)
    (fun tau htau => H.contMDiff_scalarCurvature tau (hsub htau))
    (fun tau htau y => hnonneg tau (hsub htau) y)
    (fun tau _ y => hevol tau y) q hq x

theorem compact_surface_scalar_uniform_lower_on_Icc
    {a b : ℝ} (hab : a < b) (H : RicciFlow 2 M (Icc a b))
    (hoperator : ∀ t ∈ Icc a b, ∀ x, (H.connection t).NonnegativeCurvatureOperator x)
    (p : M) (hp : 0 < (H.connection b).scalarCurvature p)
    {c : ℝ} (hac : a < c) (_hcb : c ≤ b) :
    ∃ r : ℝ, 0 < r ∧ ∀ t ∈ Icc c b, ∀ x, r ≤ (H.connection t).scalarCurvature x := by
  let f : ℝ × M → ℝ := fun z => (H.connection z.1).scalarCurvature z.2
  have hpositive : ∀ z ∈ Icc c b ×ˢ (univ : Set M), 0 < f z := by
    intro z hz
    exact compact_surface_scalar_positive_on_Ioc hab H hoperator p hp z.1
      ⟨hac.trans_le hz.1.1, hz.1.2⟩ z.2
  have hsub : Icc c b ⊆ Icc a b := Icc_subset_Icc hac.le le_rfl
  have hc : IsCompact (Icc c b ×ˢ (univ : Set M)) := isCompact_Icc.prod isCompact_univ
  have hfFull : ContinuousOn f (Icc a b ×ˢ univ) :=
    H.contMDiffOn_scalarCurvature.continuousOn
  have hf : ContinuousOn f (Icc c b ×ˢ univ) :=
    hfFull.mono (prod_mono hsub Subset.rfl)
  obtain ⟨r, hr, hbound⟩ := hc.exists_forall_le' (f := f) hf hpositive
  refine ⟨r, hr, ?_⟩
  intro t ht x
  exact hbound (t, x) ⟨ht, mem_univ x⟩

end PoincareConjecture.M32
