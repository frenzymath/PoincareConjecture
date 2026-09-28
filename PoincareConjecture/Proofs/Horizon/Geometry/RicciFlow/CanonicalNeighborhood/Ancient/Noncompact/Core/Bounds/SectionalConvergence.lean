import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Stability.Scalar.Jets
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Curvature.MovingJets
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Terminal.StrictCurvature.Uniform
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometrySectional










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set Filter
open scoped Manifold ContDiff Bundle Topology BigOperators

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}


theorem sectionalCurvature_changeBasis (D : LeviCivitaData g) (x : M)
    (u v : TangentSpace (𝓡 n) x) (a b c d : ℝ) (hdet : a * d - b * c ≠ 0) :
    D.sectionalCurvature x (a • u + b • v) (c • u + d • v) =
      D.sectionalCurvature x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  have hnum : D.curvatureTensor x (a • u + b • v) (c • u + d • v)
      (a • u + b • v) (c • u + d • v) =
      (a * d - b * c) ^ 2 * D.curvatureTensor x u v u v := by
    simp only [curvatureTensor_add_first, curvatureTensor_add_second,
      curvatureTensor_add_third, curvatureTensor_add_last,
      curvatureTensor_smul_first, curvatureTensor_smul_second,
      curvatureTensor_smul_third, curvatureTensor_smul_last,
      curvatureTensor_zero_first, curvatureTensor_zero_last]
    rw [curvatureTensor_swap_first, curvatureTensor_swap_last,
      D.curvatureTensor_swap_first x v u u v]
    ring
  have hgram : g.inner x (a • u + b • v) (a • u + b • v) *
        g.inner x (c • u + d • v) (c • u + d • v) -
        (g.inner x (a • u + b • v) (c • u + d • v)) ^ 2 =
      (a * d - b * c) ^ 2 *
        (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
    change inner ℝ (a • u + b • v) (a • u + b • v) *
        inner ℝ (c • u + d • v) (c • u + d • v) -
        (inner ℝ (a • u + b • v) (c • u + d • v)) ^ 2 = _
    change _ = (a * d - b * c) ^ 2 *
      (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2)
    simp only [inner_add_left, inner_add_right, real_inner_smul_right, real_inner_comm]
    ring
  unfold sectionalCurvature
  rw [hnum, hgram]
  field_simp [hdet]


theorem sectionalCurvature_pos_of_independent (D : LeviCivitaData g) (x : M)
    (hsec : ∀ u v, g.inner x u u = 1 → g.inner x v v = 1 →
      g.inner x u v = 0 → 0 < D.sectionalCurvature x u v)
    {u v : TangentSpace (𝓡 n) x} (huv : LinearIndependent ℝ ![u, v]) :
    0 < D.sectionalCurvature x u v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨a, b, c, d, hdet, hp, hq, hpq⟩ := exists_orthonormal_changeBasis u v huv
  rw [← D.sectionalCurvature_changeBasis x u v a b c d hdet]
  exact hsec _ _ hp hq hpq


theorem gramDet_ne_zero_of_independent (_D : LeviCivitaData g) (x : M)
    {u v : TangentSpace (𝓡 n) x} (huv : LinearIndependent ℝ ![u, v]) :
    g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2 ≠ 0 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨a, b, c, d, _, hp, hq, hpq⟩ := exists_orthonormal_changeBasis u v huv
  have hgram : g.inner x (a • u + b • v) (a • u + b • v) *
        g.inner x (c • u + d • v) (c • u + d • v) -
        (g.inner x (a • u + b • v) (c • u + d • v)) ^ 2 =
      (a * d - b * c) ^ 2 *
        (g.inner x u u * g.inner x v v - (g.inner x u v) ^ 2) := by
    change inner ℝ (a • u + b • v) (a • u + b • v) *
        inner ℝ (c • u + d • v) (c • u + d • v) -
        (inner ℝ (a • u + b • v) (c • u + d • v)) ^ 2 = _
    change _ = (a * d - b * c) ^ 2 *
      (inner ℝ u u * inner ℝ v v - (inner ℝ u v) ^ 2)
    simp only [inner_add_left, inner_add_right, real_inner_smul_right, real_inner_comm]
    ring
  rw [show g.inner x (a • u + b • v) (a • u + b • v) = 1 from hp,
    show g.inner x (c • u + d • v) (c • u + d • v) = 1 from hq,
    show g.inner x (a • u + b • v) (c • u + d • v) = 0 from hpq] at hgram
  intro hz
  rw [hz] at hgram
  norm_num at hgram

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

private theorem exists_shifted_sectional_metric_germ
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    (φ : EuclideanSpace ℝ (Fin n) → M) (x : EuclideanSpace ℝ (Fin n))
    (hφ : ∀ᶠ y in 𝓝 x, ContMDiffAt (𝓡 n) (𝓡 n) ∞ φ y ∧
      Function.Injective (mfderiv (𝓡 n) (𝓡 n) φ y)) :
    ∃ gd : Σ h : RiemannianMetric n (EuclideanSpace ℝ (Fin n)), LeviCivitaData h,
      (gd.1.euclideanCoefficients =ᶠ[𝓝 0]
        fun y => g.pullbackCoefficients φ (y + x)) ∧
      ∀ u v : EuclideanSpace ℝ (Fin n), gd.2.sectionalCurvature 0 u v =
        D.sectionalCurvature (φ x)
          (mfderiv (𝓡 n) (𝓡 n) φ x u) (mfderiv (𝓡 n) (𝓡 n) φ x v) := by
  obtain ⟨V, hVφ, hVo, hxV⟩ := mem_nhds_iff.mp hφ
  let U := (fun y => y + x) ⁻¹' V
  have hU : IsOpen U := hVo.preimage (continuous_id.add continuous_const)
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) ∈ U := by
    simpa only [U, mem_preimage, zero_add] using hxV
  have hshift : ContMDiff (𝓡 n) (𝓡 n) ∞ (fun y : EuclideanSpace ℝ (Fin n) => y + x) :=
    (contDiff_id.add contDiff_const).contMDiff
  have hd (y) (hy : y ∈ U) :
      mfderiv (𝓡 n) (𝓡 n) (fun z => φ (z + x)) y = mfderiv (𝓡 n) (𝓡 n) φ (y + x) := by
    have hh := mfderiv_comp y ((hVφ hy).1.mdifferentiableAt (by simp))
      (hshift.mdifferentiable (by simp) y)
    change mfderiv (𝓡 n) (𝓡 n) (φ ∘ (fun z => z + x)) y = _
    rw [hh]
    ext v
    simp +instances [mfderiv_eq_fderiv, fderiv_add_const]
    rfl
  have hpos : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g.pullbackCoefficients φ (y + x) v v := by
    intro y hy v hv
    apply g.pos (φ (y + x))
    intro hz
    apply hv
    apply (hVφ hy).2
    rw [map_zero]
    convert! hz using 1
  obtain ⟨h, Dh, W, hWo, h0W, hWU, heq⟩ := RiemannianMetric.exists_local_realization hU h0
    (fun y => g.pullbackCoefficients φ (y + x))
    (fun y hy => ((g.contDiffAt_pullbackCoefficients (hVφ hy).1).comp y
      (contDiff_id.add contDiff_const).contDiffAt).contDiffWithinAt)
    (fun y _ v w => g.symm _ _ _) hpos
  refine ⟨⟨h, Dh⟩, Filter.Eventually.mono (hWo.mem_nhds h0W) heq, ?_⟩
  intro u v
  have hh := Dh.sectionalCurvature_eq_of_local_isometry D (f := fun y => φ (y + x)) hWo
    (fun y hy => ((hVφ (hWU hy)).1.comp y hshift.contMDiffAt).contMDiffWithinAt)
    (fun y hy a b => by
      change h.euclideanCoefficients y a b = _
      rw [heq y hy]
      simp +instances only [hd y (hWU hy)]
      rfl) h0W u v
  rw [hd 0 (hWU h0W)] at hh
  refine hh.trans ?_
  exact congrArg (fun y : EuclideanSpace ℝ (Fin n) =>
    D.sectionalCurvature (φ y) (mfderiv (𝓡 n) (𝓡 n) φ y u)
      (mfderiv (𝓡 n) (𝓡 n) φ y v)) (zero_add x)

end PoincareConjecture.LeviCivitaData

private theorem tendsto_multilinear_eval_of_components
    {α V ι κ : Type*} {l : Filter α}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [Fintype ι] [Fintype κ] [DecidableEq κ]
    (b : OrthonormalBasis ι ℝ V)
    (A : α → MultilinearMap ℝ (fun _ : κ => V) ℝ)
    (B : MultilinearMap ℝ (fun _ : κ => V) ℝ)
    {v : α → κ → V} {w : κ → V}
    (hA : ∀ p : κ → ι, Tendsto (fun k => A k (fun j => b (p j))) l
      (𝓝 (B (fun j => b (p j)))))
    (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun k => A k (v k)) l (𝓝 (B w)) := by
  classical
  have heq (C : MultilinearMap ℝ (fun _ : κ => V) ℝ) (z : κ → V) :
      C z = ∑ p : κ → ι, (∏ j, b.repr (z j) (p j)) * C (fun j => b (p j)) := by
    conv_lhs => rw [show z = (fun j => ∑ i, b.repr (z j) i • b i) by
      funext j
      exact (b.sum_repr (z j)).symm]
    rw [C.map_sum]
    simp only [MultilinearMap.map_smul_univ, smul_eq_mul]
  rw [show (fun k => A k (v k)) = (fun k => ∑ p : κ → ι,
    (∏ j, b.repr (v k j) (p j)) * A k (fun j => b (p j))) by
      funext k; exact heq _ _, heq B w]
  apply tendsto_finsetSum
  intro p _
  apply Tendsto.mul _ (hA p)
  apply tendsto_finsetProd
  intro j _
  simp only [b.repr_apply_apply]
  exact tendsto_const_nhds.inner ((continuous_apply j).tendsto _ |>.comp hv)

namespace PoincareConjecture.LeviCivitaData

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem tendsto_sectionalCurvature_of_scalar_metric_jets
    {α : Type*} {l : Filter α} {n : ℕ}
    {gseq : α → RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (x : EuclideanSpace ℝ (Fin n))
    {u v : α → EuclideanSpace ℝ (Fin n)} {a b : EuclideanSpace ℝ (Fin n)}
    (hu : Tendsto u l (𝓝 a)) (hv : Tendsto v l (𝓝 b))
    (hab : LinearIndependent ℝ ![a, b])
    (hjets : ∀ r : ℕ, r ≤ 2 → ∀ i j : Fin n,
      Tendsto (fun k => iteratedFDeriv ℝ r (fun y => (gseq k).inner y
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) x) l
        (𝓝 (iteratedFDeriv ℝ r (fun y => g.inner y
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) x))) :
    Tendsto (fun k => (Dseq k).sectionalCurvature x (u k) (v k)) l
      (𝓝 (D.sectionalCurvature x a b)) := by
  classical
  obtain ⟨hzero, hone, htwo⟩ := RiemannianMetric.tendsto_euclideanCoefficients_of_scalar_jets
    x (EuclideanSpace.basisFun (Fin n) ℝ).toBasis hjets
  choose A hA using fun k => (Dseq k).exists_multilinear_curvatureTensor x
  obtain ⟨B, hB⟩ := D.exists_multilinear_curvatureTensor x
  have hcomp (p : Fin 4 → Fin n) :
      Tendsto (fun k => A k (fun j => EuclideanSpace.basisFun (Fin n) ℝ (p j))) l
        (𝓝 (B (fun j => EuclideanSpace.basisFun (Fin n) ℝ (p j)))) := by
    simp only [← hA, ← hB]
    exact tendsto_curvatureTensor_of_metric_jets Dseq D x _ _ _ _ hzero hone htwo
  have htup : Tendsto (fun k => ![u k, v k, u k, v k]) l (𝓝 ![a, b, a, b]) := by
    apply tendsto_pi_nhds.mpr
    intro i
    fin_cases i <;> simpa using (by first | exact hu | exact hv)
  have hnum := tendsto_multilinear_eval_of_components
    (EuclideanSpace.basisFun (Fin n) ℝ) A B hcomp htup
  simp only [← hA, ← hB, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at hnum
  have hinner {u' v' : α → EuclideanSpace ℝ (Fin n)}
      {a' b' : EuclideanSpace ℝ (Fin n)}
      (hu' : Tendsto u' l (𝓝 a')) (hv' : Tendsto v' l (𝓝 b')) :
      Tendsto (fun k => (gseq k).inner x (u' k) (v' k)) l (𝓝 (g.inner x a' b')) := by
    have h1 := (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      (hzero.prodMk_nhds hu')
    exact (continuous_fst.clm_apply continuous_snd).continuousAt.tendsto.comp
      (h1.prodMk_nhds hv')
  exact hnum.div (((hinner hu hu).mul (hinner hv hv)).sub ((hinner hu hv).pow 2))
    (D.gramDet_ne_zero_of_independent x hab)



theorem tendsto_sectionalCurvature_of_moving_scalar_pullback_jets
    {α : Type*} {l : Filter α} [l.NeBot] {n : ℕ}
    {M : α → Type*} [∀ k, TopologicalSpace (M k)]
    [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin n)) (M k)]
    [∀ k, IsManifold (𝓡 n) ∞ (M k)]
    {g : ∀ k, RiemannianMetric n (M k)} (D : ∀ k, LeviCivitaData (g k))
    (φ : ∀ k, EuclideanSpace ℝ (Fin n) → M k)
    {h : RiemannianMetric n (EuclideanSpace ℝ (Fin n))} (Dh : LeviCivitaData h)
    (x : α → EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n))
    {u v : α → EuclideanSpace ℝ (Fin n)} {a b : EuclideanSpace ℝ (Fin n)}
    (hu : Tendsto u l (𝓝 a)) (hv : Tendsto v l (𝓝 b))
    (hab : LinearIndependent ℝ ![a, b])
    (hφ : ∀ᶠ k in l, ∀ᶠ z in 𝓝 (x k), ContMDiffAt (𝓡 n) (𝓡 n) ∞ (φ k) z ∧
      Function.Injective (mfderiv (𝓡 n) (𝓡 n) (φ k) z))
    (hjets : ∀ r : ℕ, r ≤ 2 → ∀ i j : Fin n,
      Tendsto (fun k => iteratedFDeriv ℝ r (fun z =>
        (g k).pullbackCoefficients (φ k) z (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) (x k)) l
        (𝓝 (iteratedFDeriv ℝ r (fun z => h.inner z (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) y))) :
    Tendsto (fun k => (D k).sectionalCurvature (φ k (x k))
      (mfderiv (𝓡 n) (𝓡 n) (φ k) (x k) (u k))
      (mfderiv (𝓡 n) (𝓡 n) (φ k) (x k) (v k))) l
      (𝓝 (Dh.sectionalCurvature y a b)) := by
  have hreal := hφ.mono fun k hk => exists_shifted_sectional_metric_germ (D k) (φ k) (x k) hk
  obtain ⟨gd, hgd⟩ := hreal.choice
  obtain ⟨hd, hhd, hsection⟩ := exists_shifted_sectional_metric_germ Dh id y
    (Eventually.of_forall (fun z => by
      refine ⟨contMDiffAt_id, ?_⟩
      rw [mfderiv_id]
      exact Function.injective_id))
  have hid : h.pullbackCoefficients id = h.euclideanCoefficients := by
    ext z v w
    simp +instances [RiemannianMetric.pullbackCoefficients, mfderiv_id,
      RiemannianMetric.euclideanCoefficients]
    rfl
  rw [hid] at hhd
  have hj (r : ℕ) (hr : r ≤ 2) (i j : Fin n) :
      Tendsto (fun k => iteratedFDeriv ℝ r (fun z => (gd k).1.euclideanCoefficients z
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) 0) l
        (𝓝 (iteratedFDeriv ℝ r (fun z => hd.1.euclideanCoefficients z
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) 0)) := by
    have heq : (fun z => hd.1.inner z (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᶠ[𝓝 0]
        (fun z => h.inner (z + y) (EuclideanSpace.basisFun (Fin n) ℝ i)
          (EuclideanSpace.basisFun (Fin n) ℝ j)) := hhd.mono (fun z hz => congrArg
            (fun B => B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) hz)
    have heq' := (heq.iteratedFDeriv ℝ r).self_of_nhds
    change iteratedFDeriv ℝ r (fun z => hd.1.euclideanCoefficients z
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) 0 =
      iteratedFDeriv ℝ r ((fun z => h.euclideanCoefficients z
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) ∘
          (fun z => z + y)) 0 at heq'
    have hs := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun z => h.euclideanCoefficients z
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) r y 0
    have heq'' := heq'.trans hs
    simp only [zero_add] at heq''
    rw [heq'']
    apply (hjets r hr i j).congr'
    filter_upwards [hgd] with k hk
    have hk' : (fun z => (gd k).1.inner z (EuclideanSpace.basisFun (Fin n) ℝ i)
        (EuclideanSpace.basisFun (Fin n) ℝ j)) =ᶠ[𝓝 0]
        (fun z => (g k).pullbackCoefficients (φ k) (z + x k)
          (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) :=
      hk.1.mono (fun z hz => congrArg
        (fun B => B (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) hz)
    have hkj := (hk'.iteratedFDeriv ℝ r).self_of_nhds
    change iteratedFDeriv ℝ r (fun z => (gd k).1.euclideanCoefficients z
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) 0 =
      iteratedFDeriv ℝ r ((fun z => (g k).pullbackCoefficients (φ k) z
        (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) ∘
          (fun z => z + x k)) 0 at hkj
    have hks := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun z => (g k).pullbackCoefficients (φ k) z
      (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j)) r (x k) 0
    simpa only [zero_add] using (hkj.trans hks).symm
  have ht := tendsto_sectionalCurvature_of_scalar_metric_jets
    (fun k => (gd k).2) hd.2 0 hu hv hab hj
  have htarget : hd.2.sectionalCurvature 0 a b = Dh.sectionalCurvature y a b := by
    simpa only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply] using hsection a b
  rw [htarget] at ht
  exact ht.congr' (hgd.mono fun k hk => hk.2 (u k) (v k))

end PoincareConjecture.LeviCivitaData

namespace PoincareConjecture

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable
  BasedKappaSolution.connectedSpace
  normedAddCommGroupTangentSpaceVectorSpace normedSpaceTangentSpaceVectorSpace

namespace M23TerminalMetricConvergence

variable {kappa : ℝ} {S : NormalizedKappaSolutionSequence kappa}
  {G : M23InteriorConvergence S}
  {e : ∀ j, NormalizedKappaSpacetimeEmbedding
    (source := S.term (G.subsequence j)) (target := G.limit) (Iic 0 ×ˢ G.exhaustion j)}

set_option maxHeartbeats 3000000 in


theorem tendsto_terminal_coordinate_sectionalCurvature
    (hconv : M23TerminalMetricConvergence G e)
    (hfixed : ∀ k (t : ℝ), t ≤ 0 → ∀ x ∈ G.exhaustion k,
      ((e k).toFun (t, x)).2 = ((e k).toFun (0, x)).2)
    {α : Type*} {l : Filter α} [l.NeBot]
    {k : α → ℕ} {x u v : α → EuclideanSpace ℝ (Fin 3)}
    {p a b : EuclideanSpace ℝ (Fin 3)}
    (hk : Tendsto k l atTop) (hx : Tendsto x l (𝓝 p))
    (hu : Tendsto u l (𝓝 a)) (hv : Tendsto v l (𝓝 b))
    (hab : LinearIndependent ℝ ![a, b])
    (q : G.limit.carrier.carrier) (hp : p ∈ (extChartAt (𝓡 3) q).target) :
    Tendsto (fun i =>
      let φ := fun y => ((e (k i)).toFun (0, (extChartAt (𝓡 3) q).symm y)).2
      ((S.term (G.subsequence (k i))).flow.flow.connection 0).sectionalCurvature
        (φ (x i)) (mfderiv (𝓡 3) (𝓡 3) φ (x i) (u i))
          (mfderiv (𝓡 3) (𝓡 3) φ (x i) (v i))) l
      (𝓝 ((G.limit.flow.flow.connection 0).sectionalCurvature
        ((extChartAt (𝓡 3) q).symm p)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p a)
        (mfderiv (𝓡 3) (𝓡 3) (extChartAt (𝓡 3) q).symm p b))) := by
  let c := extChartAt (𝓡 3) q
  obtain ⟨g, D, V, hVo, hpV, _, heq⟩ := G.limit.carrier.exists_local_coordinate_realization
    (G.limit.flow.flow.metric 0) q 0 p hp
  have hg := Filter.Eventually.mono (hVo.mem_nhds hpV) heq
  let φ := fun i y => ((e (k i)).toFun (0, c.symm y)).2
  have hφ : ∀ᶠ i in l, ∀ᶠ y in 𝓝 (x i),
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ (φ i) y ∧
        Function.Injective (mfderiv (𝓡 3) (𝓡 3) (φ i) y) := by
    filter_upwards [(hk.prodMk hx).eventually
      (eventually_terminal_chart_domain (G := G) q hp)] with i hi
    let W := c.target ∩ c.symm ⁻¹' G.exhaustion (k i)
    have hW : IsOpen W := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
      (isOpen_extChartAt_target q) (G.exhaustion_open (k i))
    filter_upwards [hW.mem_nhds hi] with y hy
    exact (e (k i)).terminal_chart_map_regular (G.exhaustion_open (k i)) q hy.1 hy.2
  have hjets (r : ℕ) (_hr : r ≤ 2) (i j : Fin 3) :
      Tendsto (fun m => iteratedFDeriv ℝ r (fun z =>
        ((S.term (G.subsequence (k m))).flow.flow.metric 0).pullbackCoefficients (φ m) z
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j)) (x m)) l
        (𝓝 (iteratedFDeriv ℝ r (fun z => g.inner z (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j)) p)) := by
    rw [G.limit.carrier.iteratedFDeriv_coordinateCoefficient_eq_of_eventuallyEq
      q _ 0 p g hg r i j]
    have hj := hconv.tendsto_terminal_spatialJet_prod hfixed q hp r i j
    have hmap : Tendsto (fun m => (k m, x m)) l (atTop ×ˢ 𝓝 p) := hk.prodMk hx
    have hj' := hj.comp hmap
    convert! hj' using 1
  have hs := LeviCivitaData.tendsto_sectionalCurvature_of_moving_scalar_pullback_jets
    (M := fun i : α => (S.term (G.subsequence (k i))).carrier.carrier)
    (g := fun i : α => (S.term (G.subsequence (k i))).flow.flow.metric 0)
    (l := l) (u := u) (v := v) (a := a) (b := b)
    (fun i => (S.term (G.subsequence (k i))).flow.flow.connection 0)
    φ D x p hu hv hab hφ hjets
  have heqsec : D.sectionalCurvature p a b =
      (G.limit.flow.flow.connection 0).sectionalCurvature (c.symm p)
        (mfderiv (𝓡 3) (𝓡 3) c.symm p a) (mfderiv (𝓡 3) (𝓡 3) c.symm p b) := by
    obtain ⟨W, hW, hWo, hpW⟩ := mem_nhds_iff.mp
      (inter_mem (extChartAt_target_mem_nhds' hp) hg)
    apply D.sectionalCurvature_eq_of_local_isometry (G.limit.flow.flow.connection 0) hWo
      (fun z hz => (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q
        (hW hz).1).contMDiffAt (extChartAt_target_mem_nhds' (hW hz).1)
          |>.contMDiffWithinAt) (x := p) (hx := hpW)
    intro z hz u v
    have hB : g.euclideanCoefficients z =
        (G.limit.flow.flow.metric 0).pullbackCoefficients c.symm z := by
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
      intro i
      apply ContinuousLinearMap.coe_injective
      apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
      exact (hW hz).2 i
    exact congrArg (fun B => B u v) hB
  rw [heqsec] at hs
  exact hs

end M23TerminalMetricConvergence
end PoincareConjecture
