import PoincareConjecture.Proofs.M10.RayEquality
import PoincareConjecture.Proofs.M10.PositiveJacobianInverse
import PoincareConjecture.Proofs.M10.OpenDenseInjectivity










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

variable [ConnectedSpace M]

set_option backward.isDefEq.respectTransparency false in

theorem exponentialSliceChart_surjective (hL : LGeodesicTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax) :
    Function.Surjective (exponentialSliceChart G τ) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  intro q
  obtain ⟨Z, hZ, _⟩ := exists_minimizing_lift hL G q τ hτ hmax
  refine ⟨(metricCoordinates (F.metric T) p).symm Z, ?_⟩
  rw [exponentialSliceChart_apply, LinearIsometryEquiv.apply_symm_apply, hZ]

set_option backward.isDefEq.respectTransparency false in

theorem exponentialSliceChart_source_eq_univ
    (hL : LGeodesicTheory F T τmax) (G : LExponentialGeometry F T τmax p)
    {τ : ℝ} (hτ : 0 < τ) (hmax : τ < τmax)
    (hinj : Function.Injective (exponentialSliceChart G τ))
    (hD : ∀ x, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) (exponentialSliceChart G τ) x)) :
    (exponentialSliceChart G τ).source = univ := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let β := metricCoordinates (F.metric T) p
  have hgamma : Function.Injective (fun Z ↦ G.gamma Z τ) := by
    intro Z W hZW
    apply β.symm.injective
    apply hinj
    simpa only [exponentialSliceChart_apply, β, LinearIsometryEquiv.apply_symm_apply] using hZW
  rw [exponentialSliceChart_source, eq_univ_iff_forall]
  intro x
  change G.toLExponentialFamily.uniqueMinimizing (β x) τ ∧
    Function.Bijective (G.toLExponentialFamily.sliceDifferential (β x) τ)
  obtain ⟨Z, hZ, hmin, _⟩ := exists_minimizing_lift hL G (G.gamma (β x) τ) τ hτ hmax
  have hZx : Z = β x := hgamma hZ
  rw [hZx] at hmin
  refine ⟨⟨hτ, hmax, hmin, ?_⟩, ?_⟩
  · intro q hq0 hqτ hqmin
    obtain ⟨W, hW, _⟩ := G.minimizers_lift τ hτ hmax q hq0 hqmin
    have hWx : W = β x := hgamma ((hW ⟨hτ.le, le_rfl⟩).symm.trans hqτ)
    simpa only [hWx] using hW
  · have hcomp : Function.Bijective (fun v : EuclideanSpace ℝ (Fin n) ↦
        G.toLExponentialFamily.sliceDifferential (β x) τ (β v)) := by
      constructor
      · intro a b hab
        apply (hD x).1
        rw [exponentialSliceChart_differential G hτ hmax,
          exponentialSliceChart_differential G hτ hmax]
        exact hab
      · intro w
        obtain ⟨a, ha⟩ := (hD x).2 w
        refine ⟨a, ?_⟩
        rw [exponentialSliceChart_differential G hτ hmax] at ha
        exact ha
    constructor
    · intro v w hvw
      obtain ⟨a, rfl⟩ := β.surjective v
      obtain ⟨b, rfl⟩ := β.surjective w
      exact congrArg β (hcomp.1 hvw)
    · intro w
      obtain ⟨v, hv⟩ := hcomp.2 w
      exact ⟨β v, hv⟩

variable [T3Space M] [MeasurableSpace M] [BorelSpace M]


theorem exponentialSliceChart_global_of_volume_eq
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {τ : ℝ} (hτ : 0 < τ) (hτmax : τ < τmax)
    (heq : reducedVolume F T p τ = euclideanReducedVolume n) :
    (exponentialSliceChart G τ).source = univ ∧
      (exponentialSliceChart G τ).target = univ := by
  have hae := regularWeightedJacobian_ae_eq_gaussian_of_volume_eq hL hDifferential G hmax
    hT hwindow hcurvature hτ hτmax heq
  have hgauss := weightedExponentialJacobian_eq_gaussian_of_ae G hτ hτmax hae
  have hD (x : EuclideanSpace ℝ (Fin n)) :
      Function.Bijective (mfderiv (𝓡 n) (𝓡 n) (exponentialSliceChart G τ) x) :=
    mfderiv_bijective_of_pullbackJacobian_pos (F.metric (T - τ))
      (exponentialSliceJacobian_pos_of_gaussian G hτ hgauss x)
  have hdense : Dense (exponentialSliceChart G τ).source :=
    Measure.dense_of_ae (μ := volume) (ae_mem_exponentialSlice_source_of_gaussian G hae)
  have hinj := injective_of_open_dense_injOn
    (exponentialSliceChart_contMDiff G hτ hτmax).continuous
    (isOpenMap_of_mfderiv_bijective (exponentialSliceChart_contMDiff G hτ hτmax) hD)
    (exponentialSliceChart G τ).open_source hdense (exponentialSliceChart G τ).injOn
  have hsource := exponentialSliceChart_source_eq_univ hL G hτ hτmax hinj hD
  refine ⟨hsource, eq_univ_iff_forall.mpr ?_⟩
  intro q
  obtain ⟨x, rfl⟩ := exponentialSliceChart_surjective hL G hτ hτmax q
  exact (exponentialSliceChart G τ).map_source (hsource.symm ▸ mem_univ x)

end PoincareConjecture.M10
