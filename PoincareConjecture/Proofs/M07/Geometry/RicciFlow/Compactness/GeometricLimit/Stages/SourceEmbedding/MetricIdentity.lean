import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.SourceMetric









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Poincare.Gluing
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.ChartDistance

theorem contDiffAt_source_readout
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {i : ι} {e : Piece U i → M}
    (he : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ e)
    (hinj : Function.Injective e) (hopen : IsOpen (range e))
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x) (hx : f x ∈ range e) :
    ContDiffAt ℝ ∞ (fun y => (Function.invFun e (f y)).val) x := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  have hi := (contMDiffOn_invFun_of_localDiffeomorph he hinj).contMDiffAt
    (hopen.mem_nhds hx)
  have hv := contMDiff_isOpenEmbedding (I := 𝓡 n) (n := ∞)
    (hU i).isOpenEmbedding_subtypeVal
  exact ((hv _).comp _ (hi.comp _ hf)).contDiffAt

theorem source_readout_pullbackCoefficients
    {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {i : ι} {e : Piece U i → M}
    (he : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ e)
    (hinj : Function.Injective e) (hopen : IsOpen (range e))
    {f : EuclideanSpace ℝ (Fin n) → M} {x : EuclideanSpace ℝ (Fin n)}
    (hf : ContMDiffAt (𝓡 n) (𝓡 n) ∞ f x) (hx : f x ∈ range e) :
    let a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
      fun y => (Function.invFun e (f y)).val
    (g.pullbackCoefficients (chartParametrization U hU e) (a x)).bilinearComp
      (fderiv ℝ a x) (fderiv ℝ a x) = g.pullbackCoefficients f x := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := (hU i).isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 n) (n := ∞)
  let a : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun y => (Function.invFun e (f y)).val
  let q := chartParametrization U hU e
  have hnear : ∀ᶠ y in 𝓝 x, f y ∈ range e :=
    hf.continuousAt.preimage_mem_nhds (hopen.mem_nhds hx)
  have ha : ContDiffAt ℝ ∞ a x :=
    contDiffAt_source_readout U hU he hinj hopen hf hx
  have hq : ContMDiffAt (𝓡 n) (𝓡 n) ∞ q (a x) :=
    (contMDiffOn_chartParametrization U hU he.contMDiff).contMDiffAt
      ((hU i).mem_nhds (Function.invFun e (f x)).property)
  have heq : q ∘ a =ᶠ[𝓝 x] f := by
    filter_upwards [hnear] with y hy
    change chartParametrization U hU e (Subtype.val (Function.invFun e (f y))) = f y
    rw [chartParametrization_apply, Function.invFun_eq hy]
  have hd := mfderiv_comp x (hq.mdifferentiableAt (by simp))
    (ha.differentiableAt (by simp)).mdifferentiableAt
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hd
  ext v w
  change g.inner (q (a x))
      (mfderiv (𝓡 n) (𝓡 n) q (a x) (fderiv ℝ a x v))
      (mfderiv (𝓡 n) (𝓡 n) q (a x) (fderiv ℝ a x w)) =
    g.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) (mfderiv (𝓡 n) (𝓡 n) f x w)
  have hdv := congrArg (fun A => A v) hd
  have hdw := congrArg (fun A => A w) hd
  have hb := congrArg (fun z : M => g.inner z
    (mfderiv (𝓡 n) (𝓡 n) q (a x) (fderiv ℝ a x v))
    (mfderiv (𝓡 n) (𝓡 n) q (a x) (fderiv ℝ a x w))) heq.self_of_nhds
  exact hb.trans (congrArg₂ (fun v w : EuclideanSpace ℝ (Fin n) => g.inner (f x) v w)
    hdv.symm hdw.symm)

end PoincareConjecture.ChartDistance
