import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Smooth
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Coefficients









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Metric Poincare.Gluing
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.ChartDistance

variable {ι : Type*} {n : ℕ}
    (U : ι → Set (EuclideanSpace ℝ (Fin n))) (hU : ∀ i, IsOpen (U i))
    [∀ i, Nonempty (Piece U i)]

noncomputable def chartParametrization {M : Type*} {i : ι} (e : Piece U i → M) :
    EuclideanSpace ℝ (Fin n) → M :=
  e ∘ (hU i).isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph.symm

@[simp] theorem chartParametrization_apply {M : Type*} {i : ι}
    (e : Piece U i → M) (x : Piece U i) : chartParametrization U hU e x = e x := by
  simp [chartParametrization, Topology.IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

omit [IsManifold (𝓡 n) ∞ M] in
theorem contMDiffOn_chartParametrization {i : ι} {e : Piece U i → M}
    (he : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ContMDiff (𝓡 n) (𝓡 n) ∞ e) :
    ContMDiffOn (𝓡 n) (𝓡 n) ∞ (chartParametrization U hU e) (U i) := by
  let := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
  have hinv := contMDiffOn_isOpenEmbedding_symm (I := 𝓡 n) (n := ∞)
    (hU i).isOpenEmbedding_subtypeVal
  exact he.comp_contMDiffOn (hinv.mono (by rintro x hx; exact ⟨⟨x, hx⟩, rfl⟩))

theorem source_transition_pullbackCoefficients
    (g : RiemannianMetric n M) {i j : ι}
    {ei : Piece U i → M} {ej : Piece U j → M}
    (hei : letI := (hU i).isOpenEmbedding_subtypeVal.singletonChartedSpace
      ContMDiff (𝓡 n) (𝓡 n) ∞ ei)
    (hej : letI := (hU j).isOpenEmbedding_subtypeVal.singletonChartedSpace
      IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ ej)
    (hinj : Function.Injective ej) (hopen : IsOpen (range ej))
    (x : Piece U i) (hx : ei x ∈ range ej)
    (v w : EuclideanSpace ℝ (Fin n)) :
    let f := coordinateRepresentative U hU (fun y => Function.invFun ej (ei y))
    g.pullbackCoefficients (chartParametrization U hU ej) (f x)
        (fderiv ℝ f x v) (fderiv ℝ f x w) =
      g.pullbackCoefficients (chartParametrization U hU ei) x v w := by
  let : ∀ l, ChartedSpace (EuclideanSpace ℝ (Fin n)) (Piece U l) :=
    fun l => (hU l).isOpenEmbedding_subtypeVal.singletonChartedSpace
  let : ∀ l, IsManifold (𝓡 n) ∞ (Piece U l) :=
    fun l => (hU l).isOpenEmbedding_subtypeVal.isManifold_singleton
  let f := coordinateRepresentative U hU (fun y => Function.invFun ej (ei y))
  let p := chartParametrization U hU ei
  let q := chartParametrization U hU ej
  have hp : ContMDiffAt (𝓡 n) (𝓡 n) ∞ p x :=
    (contMDiffOn_chartParametrization U hU hei).contMDiffAt ((hU i).mem_nhds x.property)
  have hx' : p x ∈ range ej := by simpa [p] using hx
  have hnear : ∀ᶠ y in 𝓝 (x : EuclideanSpace ℝ (Fin n)), p y ∈ range ej :=
    hp.continuousAt.preimage_mem_nhds (hopen.mem_nhds hx')
  have hf : ContDiffAt ℝ ∞ f x := by
    have hi := (contMDiffOn_invFun_of_localDiffeomorph hej hinj).contMDiffAt
      (hopen.mem_nhds hx')
    have hv := contMDiff_isOpenEmbedding (I := 𝓡 n) (n := ∞)
      (hU j).isOpenEmbedding_subtypeVal
    exact ((hv _).comp _ (hi.comp _ hp)).contDiffAt
  have hfx : f x ∈ U j := by
    change Subtype.val (Function.invFun ej (ei _)) ∈ U j
    exact (Function.invFun ej (ei _)).property
  have hq : ContMDiffAt (𝓡 n) (𝓡 n) ∞ q (f x) :=
    (contMDiffOn_chartParametrization U hU hej.contMDiff).contMDiffAt ((hU j).mem_nhds hfx)
  have heq : q ∘ f =ᶠ[𝓝 (x : EuclideanSpace ℝ (Fin n))] p := by
    filter_upwards [hnear] with y hy
    change chartParametrization U hU ej (Subtype.val (Function.invFun ej (p y))) = p y
    rw [chartParametrization_apply, Function.invFun_eq hy]
  have hd := mfderiv_comp (x : EuclideanSpace ℝ (Fin n))
    (hq.mdifferentiableAt (by simp)) (hf.differentiableAt (by simp)).mdifferentiableAt
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hd
  change g.inner (q (f x))
      (mfderiv (𝓡 n) (𝓡 n) q (f x) (fderiv ℝ f x v))
      (mfderiv (𝓡 n) (𝓡 n) q (f x) (fderiv ℝ f x w)) =
    g.inner (p x) (mfderiv (𝓡 n) (𝓡 n) p x v) (mfderiv (𝓡 n) (𝓡 n) p x w)
  have hdv := congrArg (fun A => A v) hd
  have hdw := congrArg (fun A => A w) hd
  have hbase := congrArg (fun z : M => g.inner z
    (mfderiv (𝓡 n) (𝓡 n) q (f x) (fderiv ℝ f x v))
    (mfderiv (𝓡 n) (𝓡 n) q (f x) (fderiv ℝ f x w))) heq.self_of_nhds
  exact hbase.trans (congrArg₂ (fun a b : EuclideanSpace ℝ (Fin n) =>
    g.inner (p x) a b) hdv.symm hdw.symm)

end PoincareConjecture.ChartDistance
