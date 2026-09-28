import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.RegularSets.EuclideanImageDistance
import PoincareConjecture.Proofs.M28.Mathlib.CanonicalDomainInclusion











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

namespace PoincareConjecture.M28

local notation "E" => EuclideanSpace ℝ (Fin 3)

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E N] [IsManifold (𝓡 3) ∞ N]




def canonicalImageMetric
    (g : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E N ∞)
    (V : TopologicalSpace.Opens E) [Nonempty V]
    (hsource : (V : Set E) ⊆ e.source) :
    letI := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := V.isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    RiemannianMetric 3 V := by
  let := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := V.isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  let W : TopologicalSpace.Opens N :=
    ⟨e '' (V : Set E), e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      V.isOpen hsource⟩
  let D := e.diffeomorphOnCanonicalSource V W hsource rfl
  exact g.pullbackOfLocalDiffeomorph ((Subtype.val : W → N) ∘ D)
    (diffeomorph_openImageMap_isLocalDiffeomorph W D)




theorem canonicalImageMetric_inner
    (g : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E N ∞)
    (V : TopologicalSpace.Opens E) [Nonempty V]
    (hsource : (V : Set E) ⊆ e.source) :
    letI := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := V.isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ (x : V) (v w : E),
      (canonicalImageMetric g e V hsource).inner x v w =
        g.pullbackCoefficients e x v w := by
  let := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := V.isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro x v w
  have hi : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : V → E) x :=
    (Poincare.isLocalDiffeomorph_subtypeVal
      (𝓡 3) (V : Set E) V.isOpen ∞ x).mdifferentiableAt (by simp)
  have he : MDifferentiableAt (𝓡 3) (𝓡 3) e (x : E) :=
    e.mdifferentiableAt (by simp) (hsource x.property)
  have hdval : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → E) x =
      ContinuousLinearMap.id ℝ E := mfderiv_extChartAt_self
  have hderiv (z : E) : mfderiv (𝓡 3) (𝓡 3) (e ∘ (Subtype.val : V → E)) x z =
      mfderiv (𝓡 3) (𝓡 3) e (x : E) z := by
    have hcomp := mfderiv_comp_apply x he hi z
    have hdz : mfderiv (𝓡 3) (𝓡 3) (Subtype.val : V → E) x z = z :=
      congrArg (fun L : E →L[ℝ] E => L z) hdval
    exact hcomp.trans (congrArg (mfderiv (𝓡 3) (𝓡 3) e (x : E)) hdz)
  change g.inner (e (x : E))
    (mfderiv (𝓡 3) (𝓡 3) (e ∘ (Subtype.val : V → E)) x v)
    (mfderiv (𝓡 3) (𝓡 3) (e ∘ (Subtype.val : V → E)) x w) =
      g.inner (e (x : E)) (mfderiv (𝓡 3) (𝓡 3) e (x : E) v)
        (mfderiv (𝓡 3) (𝓡 3) e (x : E) w)
  rw [hderiv v, hderiv w]





theorem canonicalImageMetric_originalOpen_edist
    [T2Space N] (g : RiemannianMetric 3 N)
    (e : PartialDiffeomorph (𝓡 3) (𝓡 3) E N ∞)
    (U : TopologicalSpace.Opens N) {a : ℝ} (ha : 0 < a)
    (hsource : Metric.ball (0 : E) a ⊆ e.source)
    (hinside : e '' Metric.ball (0 : E) a ⊆ (U : Set N))
    (hbound : ∀ z ∈ Metric.ball (0 : E) a, ∀ v : E,
      (1 / 8 : ℝ) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients e z v v ∧
        g.pullbackCoefficients e z v v ≤ (9 / 2 : ℝ) * ‖v‖ ^ 2) :
    let V : TopologicalSpace.Opens E := ⟨Metric.ball 0 a, Metric.isOpen_ball⟩
    letI : Nonempty V := ⟨⟨0, Metric.mem_ball_self ha⟩⟩
    letI := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
    letI := V.isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
    ∀ (x y : V), x.val ∈ Metric.closedBall (0 : E) (a / 64) →
      y.val ∈ Metric.closedBall (0 : E) (a / 64) →
      (intrinsicOpenMetric g U).edist
          ⟨e x, hinside ⟨x, x.property, rfl⟩⟩
          ⟨e y, hinside ⟨y, y.property, rfl⟩⟩ =
            (canonicalImageMetric g e V hsource).edist x y ∧
        (canonicalImageMetric g e V hsource).edist x y ≤
          ENNReal.ofReal (Real.sqrt (9 / 2 : ℝ)) * edist (x : E) (y : E) ∧
        (canonicalImageMetric g e V hsource).edist x y < ENNReal.ofReal (a / 8) := by
  intro V
  let : Nonempty V := ⟨⟨0, Metric.mem_ball_self ha⟩⟩
  let := V.isOpen.isOpenEmbedding_subtypeVal.singletonChartedSpace
  let := V.isOpen.isOpenEmbedding_subtypeVal.isManifold_singleton (I := 𝓡 3) (n := ∞)
  intro x y hx hy
  let W : TopologicalSpace.Opens N :=
    ⟨e '' (V : Set E), e.toOpenPartialHomeomorph.isOpen_image_of_subset_source
      V.isOpen hsource⟩
  let D := e.diffeomorphOnCanonicalSource V W hsource rfl
  exact originalOpen_edist_eq_openImagePullback_of_euclidean_bounds
    g e U W ha hsource rfl hinside
    (fun z hz v => (hbound z hz v).1) (fun z hz v => (hbound z hz v).2)
    D x y hx hy rfl rfl

end PoincareConjecture.M28
