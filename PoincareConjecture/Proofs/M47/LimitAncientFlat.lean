import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.SlabBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.Comparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarEvolution












set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]



theorem limitAncient_scalar_reaction_bound [T2Space M]
    (h04 : RicciFlowCurvatureTheory.{u}) {T : ℝ} (F : RicciFlow 3 M (Icc 0 T))
    (hoperator : ∀ t ∈ Icc 0 T, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {B : ℝ} (hbound : ∀ t ∈ Icc 0 T, ∀ x, (F.connection t).scalarCurvature x ≤ B)
    (t : ℝ) (ht : t ∈ Icc 0 T) (x : M) :
    2 * (F.connection t).ricciNormSq x ≤
      (2 * B) * (F.connection t).scalarCurvature x := by
  have hD := h04.tensor_calculus 3 M (F.metric t) (F.connection t)
  have hRic (v : TangentSpace (𝓡 3) x) : 0 ≤ (F.connection t).ricci x v v :=
    ((F.connection t).ricci_bounds_of_nonnegative_curvatureOperator hD x
      (hoperator t ht x) v).1
  have hscalar : 0 ≤ (F.connection t).scalarCurvature x :=
    Finset.sum_nonneg (fun _ _ => hRic _)
  have hsq := (F.connection t).ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg hD x hRic
  have hlinear := mul_le_mul_of_nonneg_right (hbound t ht x) hscalar
  nlinarith



theorem limitAncient_scalar_nonpos_of_compact [T2Space M] [CompactSpace M]
    (h04 : RicciFlowCurvatureTheory.{u}) {T : ℝ} (F : RicciFlow 3 M (Icc 0 T))
    (hoperator : ∀ t ∈ Icc 0 T, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {B : ℝ} (hbound : ∀ t ∈ Icc 0 T, ∀ x, (F.connection t).scalarCurvature x ≤ B)
    (hinit : ∀ x, (F.connection 0).scalarCurvature x ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → (F.connection t).scalarCurvature x ≤ 0 := by
  apply Poincare.Parabolic.nonpos_of_deriv_le_mul_at_max
    (F := fun x t => (F.connection t).scalarCurvature x)
    (F' := fun x t => (F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x) (K := 2 * B)
  · exact (h04.scalar_regular 3 M (Icc 0 T) F).continuousOn.comp
      (f := fun z : M × ℝ => (z.2, z.1))
      (continuous_snd.prodMk continuous_fst).continuousOn (fun z hz => ⟨hz.2, hz.1⟩)
  · intro x t ht
    exact h04.scalar_evolution 3 M (Icc 0 T) F t ⟨ht.1.le, ht.2⟩ x
  · intro x t ht _ hmax
    have ht' : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have hlap := (F.connection t).laplacian_nonpos_of_isLocalMax
      (Poincare.RicciFlow.Harnack.scalarCurvature_contMDiff_slice h04 _ F t ht')
      (Filter.Eventually.of_forall hmax)
    linarith [limitAncient_scalar_reaction_bound h04 F hoperator hbound t ht' x]
  · exact hinit



theorem limitAncient_scalar_nonpos_of_exhaustion [T2Space M]
    (h04 : RicciFlowCurvatureTheory.{u}) {T : ℝ} (F : RicciFlow 3 M (Icc 0 T))
    {O : M} (S : RicciFlow.SmoothExhaustion F O)
    (hproper : ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r})
    (hoperator : ∀ t ∈ Icc 0 T, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Icc 0 T, ∀ x, (F.connection t).scalarCurvature x ≤ B)
    (hinit : ∀ x, (F.connection 0).scalarCurvature x ≤ 0) :
    ∀ x t, t ∈ Icc 0 T → (F.connection t).scalarCurvature x ≤ 0 := by
  apply S.nonpos_of_heat_le_mul hproper
    (u := fun x t => (F.connection t).scalarCurvature x)
    (du := fun x t => (F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x) (C := 2 * B) (B := B)
    (by positivity) Subset.rfl
  · exact (h04.scalar_regular 3 M (Icc 0 T) F).continuousOn.comp
      (f := fun z : M × ℝ => (z.2, z.1))
      (continuous_snd.prodMk continuous_fst).continuousOn (fun z hz => ⟨hz.2, hz.1⟩)
  · intro t ht
    exact Poincare.RicciFlow.Harnack.scalarCurvature_contMDiff_slice h04 _ F t ht
  · intro x t ht
    exact h04.scalar_evolution 3 M (Icc 0 T) F t ⟨ht.1.le, ht.2⟩ x
  · intro x t ht
    exact hbound t ht x
  · intro x t ht
    simpa only [add_sub_cancel_left] using
      limitAncient_scalar_reaction_bound h04 F hoperator hbound t ⟨ht.1.le, ht.2⟩ x
  · exact hinit




theorem limitAncient_forward_flat_on_buffered_slab
    [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (h04 : RicciFlowCurvatureTheory.{u}) (F : RicciFlow 3 M (Iic 0)) (O : M)
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hoperator : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (a K : ℝ) (ha : a < 0) (hK : 0 ≤ K)
    (hbound : ∀ t ∈ Icc (a - 1) 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hflat : ∀ x, (F.connection a).curvatureTensorNorm x = 0) :
    ∀ t ∈ Icc a 0, ∀ x, (F.connection t).curvatureTensorNorm x = 0 := by
  classical
  have hshift : (fun t : ℝ => t + a) '' Icc 0 (-a) ⊆ Iic 0 := by
    rintro _ ⟨t, ht, rfl⟩
    change t + a ≤ 0
    linarith [ht.2]
  have hne : (Icc 0 (-a)).Nontrivial := by
    refine ⟨0, ⟨le_rfl, by linarith⟩, -a, ⟨by linarith, le_rfl⟩, ?_⟩
    linarith
  let G := F.translate a hshift ordConnected_Icc hne
  have hzero : (0 : ℝ) ∈ Icc 0 (-a) := ⟨le_rfl, by linarith⟩
  have hcurv (s : ℝ) (hs : s ∈ Icc 0 (-a)) (x : M) :
      (G.connection s).curvatureTensorNorm x ≤ K :=
    hbound (s + a) (by constructor <;> linarith [hs.1, hs.2]) x
  have hoperatorG (s : ℝ) (hs : s ∈ Icc 0 (-a)) (x : M) :
      (G.connection s).NonnegativeCurvatureOperator x :=
    hoperator (s + a) (by linarith [hs.2]) x
  have hscalar_bound (s : ℝ) (hs : s ∈ Icc 0 (-a)) (x : M) :
      (G.connection s).scalarCurvature x ≤ (3 : ℝ) ^ 2 * K :=
    (le_abs_self _).trans (((G.connection s).abs_scalarCurvature_le_curvatureTensorNorm x).trans
      (mul_le_mul_of_nonneg_left (hcurv s hs x) (sq_nonneg _)))
  have hinit (x : M) : (G.connection 0).scalarCurvature x ≤ 0 := by
    have h := (F.connection a).abs_scalarCurvature_le_curvatureTensorNorm x
    rw [hflat x, mul_zero] at h
    change (F.connection (0 + a)).scalarCurvature x ≤ 0
    exact (congrArg (fun s => (F.connection s).scalarCurvature x ≤ 0) (zero_add a)).mpr
      ((le_abs_self _).trans h)
  have hscalar : ∀ x s, s ∈ Icc 0 (-a) → (G.connection s).scalarCurvature x ≤ 0 := by
    by_cases hc : IsCompact (univ : Set M)
    · let : CompactSpace M := ⟨hc⟩
      exact limitAncient_scalar_nonpos_of_compact h04 G hoperatorG hscalar_bound hinit
    · let : NoncompactSpace M := ⟨hc⟩
      obtain ⟨D, _, hderiv⟩ := F.exists_curvatureDerivativeNorm_bound_on_buffered_slab h04
        (a := a - 1) (b := 0) (δ := 1) (K := K)
        (by linarith) (fun _ ht => ht.2) (by norm_num)
        (hcomplete (a - 1) (by linarith)) hbound 1
      let K₁ := max K (3 * D)
      have hK₁ : 0 ≤ K₁ := hK.trans (le_max_left _ _)
      have hRicDeriv : ∀ s ∈ Icc 0 (-a), ∀ x (v w z : TangentSpace (𝓡 3) x),
          |(G.connection s).covariantTensorDerivative (G.connection s).ricciEvaluation
            x ![v, w, z]| ≤ K₁ * (G.metric s).tangentNorm x v *
              (G.metric s).tangentNorm x w * (G.metric s).tangentNorm x z := by
        intro s hs x v w z
        apply ((G.connection s).abs_covariantTensorDerivative_ricci_le_curvatureDerivativeNorm
          (h04.tensor_calculus 3 M (G.metric s) (G.connection s)) x v w z).trans
        have hd : (G.connection s).curvatureDerivativeNorm 1 x ≤ D :=
          hderiv (s + a) (by constructor <;> linarith [hs.1, hs.2]) x
        have hnorm (v : TangentSpace (𝓡 3) x) : 0 ≤ (G.metric s).tangentNorm x v :=
          Real.sqrt_nonneg _
        have hcoeff : (3 : ℝ) * (G.connection s).curvatureDerivativeNorm 1 x ≤ K₁ :=
          (mul_le_mul_of_nonneg_left hd (by norm_num)).trans (le_max_right _ _)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoeff (hnorm v)) (hnorm w)) (hnorm z)
      obtain ⟨_, _, hS⟩ := G.exists_proper_smoothExhaustion_of_curvature_bound
        0 (-a) K₁ hzero
        (fun s hs => by simpa only [sub_zero, abs_of_nonneg hs.1] using hs.2)
        (fun s hs => hcomplete (s + a) (by linarith [hs.2])) hK₁
        (fun s hs x => (hcurv s hs x).trans (le_max_left _ _)) hRicDeriv
      obtain ⟨S, _, hproper⟩ := hS O
      exact limitAncient_scalar_nonpos_of_exhaustion h04 G S hproper hoperatorG
        (by positivity) hscalar_bound hinit
  have hzero_curv (s : ℝ) (hs : s ∈ Icc 0 (-a)) (x : M) :
      (G.connection s).curvatureTensorNorm x = 0 := by
    apply le_antisymm
    · exact ((G.connection s).curvatureTensorNorm_le_scalarCurvature
        (h04.tensor_calculus 3 M (G.metric s) (G.connection s)) x (hoperatorG s hs x)).trans
        (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (hscalar x s hs))
    · exact Real.sqrt_nonneg _
  intro t ht x
  have hs : t - a ∈ Icc 0 (-a) := by constructor <;> linarith [ht.1, ht.2]
  have h := hzero_curv (t - a) hs x
  change (F.connection (t - a + a)).curvatureTensorNorm x = 0 at h
  exact (congrArg (fun s => (F.connection s).curvatureTensorNorm x = 0)
    (sub_add_cancel t a)).mp h

end PoincareConjecture.M47
