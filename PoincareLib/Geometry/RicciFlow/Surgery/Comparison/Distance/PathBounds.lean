import PoincareLib.Geometry.RicciFlow.Surgery.Metric.Distance.MetricComparison
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Distance
import PoincareLib.Geometry.Riemannian.Normalization.Scaling.Geometry
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Distance.LengthLocalToGlobal
/-!
# Local path estimates for the comparison map

Morgan--Tian Proposition 15.12, p. 365, and Claim 18.22, p. 433. The
published local surgery path estimates are applied to a constant rescaling
of the source metric. No new local surgery result is chosen and no MetricSurgery
theorem service is assumed.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u v w

namespace PoincareMT.SurgeryComparison

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Y]
  [IsManifold (𝓡 3) ∞ X] [IsManifold (𝓡 3) ∞ Y]

/-- A confined C1 path on any ordered interval bounds intrinsic distance.
The affine reparametrization uses the exact path class in the frozen
definition, as required by the local collapse estimate of Theorem 13.2. -/
theorem intrinsicEDist_le_pathELength
    (g : RiemannianMetric 3 X) {U : Set X} {γ : ℝ → X}
    {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Set.Icc a b))
    (hU : Set.MapsTo γ (Set.Icc a b) U) :
    intrinsicEDist g U (γ a) (γ b) ≤ g.pathELength γ a b := by
  let r : ℝ →ᴬ[ℝ] ℝ := ContinuousAffineMap.lineMap a b
  have hrange : Set.MapsTo r (Set.Icc 0 1) (Set.Icc a b) := by
    rw [Set.mapsTo_iff_image_subset, show (r : ℝ → ℝ) = AffineMap.lineMap a b from rfl,
      ← segment_eq_image_lineMap, segment_eq_Icc hab]
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (γ ∘ r) (Set.Icc 0 1) :=
    hγ.comp r.contDiff.contMDiff.contMDiffOn hrange
  have hlength : g.pathELength (γ ∘ r) 0 1 = g.pathELength γ a b := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
      ⟨g.toRiemannianMetric⟩
    change Manifold.pathELength (𝓡 3) (γ ∘ r) 0 1 =
      Manifold.pathELength (𝓡 3) γ a b
    have h := Manifold.pathELength_comp_of_monotoneOn (I := 𝓡 3)
      (γ := γ) (f := r) zero_le_one
      ((AffineMap.lineMap_mono hab).monotoneOn (Set.Icc 0 1))
      r.differentiableOn
      (by simpa [r, ContinuousAffineMap.coe_lineMap_eq] using
        hγ.mdifferentiableOn one_ne_zero)
    simpa [r, ContinuousAffineMap.coe_lineMap_eq] using h
  apply sInf_le
  refine ⟨γ ∘ r, hcomp, ?_, ?_, Set.mapsTo_iff_image_subset.mp (hU.comp hrange),
    hlength.symm⟩
  · simp [r, ContinuousAffineMap.coe_lineMap_eq]
  · simp [r, ContinuousAffineMap.coe_lineMap_eq]

/-- A quadratic pullback bound compares the actual derivative-integral
lengths, including paths restricted to a neck (Theorem 13.2, pp. 331-334,
and Proposition 15.12, p. 365). -/
theorem pathELength_comp_le_mul
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    {f : X → Y} {U : Set X} {C : ℝ} (hC : 0 < C)
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hmetric : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ C ^ 2 * g.inner x v v)
    {γ : ℝ → X} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Set.Icc a b))
    (hU : Set.MapsTo γ (Set.Icc a b) U) :
    h.pathELength (f ∘ γ) a b ≤ ENNReal.ofReal C * g.pathELength γ a b := by
  have hb := MetricSurgery.pathELength_comp_le_of_pullback_bound
    (rescaledMetric g (C ^ 2) (sq_pos_of_pos hC)) h hf hmetric hγ
    (Set.mapsTo_iff_image_subset.mp hU)
  rwa [rescaledMetric_pathELength, Real.sqrt_sq hC.le] at hb

/-- A quadratic pullback estimate bounds the image endpoint distance by
the source path length, with the square-root factor required by Claim
18.22, Morgan--Tian p. 433. -/
theorem edist_comp_le_mul_pathELength
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    {f : X → Y} {U : Set X} {C : ℝ} (hC : 0 < C)
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hmetric : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ C ^ 2 * g.inner x v v)
    {γ : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Set.Icc a b))
    (hU : Set.MapsTo γ (Set.Icc a b) U) :
    h.edist (f (γ a)) (f (γ b)) ≤ ENNReal.ofReal C * g.pathELength γ a b := by
  have hb := MetricSurgery.edist_comp_le_pathELength_of_pullback_bound
    (rescaledMetric g (C ^ 2) (sq_pos_of_pos hC)) h hf hmetric hab hγ
    (Set.mapsTo_iff_image_subset.mp hU)
  rwa [rescaledMetric_pathELength, Real.sqrt_sq hC.le] at hb

/-- A static intrinsic-distance bound after a smooth coordinate map gives
a source path bound. The nonsmooth local collapse of Theorem 13.2 is
handled entirely by its distance inequality; Proposition 15.12, p. 365. -/
theorem edist_comp_le_mul_pathELength_of_intrinsic_bound
    {Z : Type w} [TopologicalSpace Z]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) Z] [IsManifold (𝓡 3) ∞ Z]
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    (k : RiemannianMetric 3 Z) {f : X → Y} {c : Y → Z}
    {U : Set X} {V : Set Y} {C : ℝ} (hC : 0 < C)
    (hf : ∀ x ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f x)
    (hmetric : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ C ^ 2 * g.inner x v v)
    (hfV : Set.MapsTo f U V)
    (hstatic : ∀ x ∈ V, ∀ y ∈ V,
      k.edist (c x) (c y) ≤ intrinsicEDist h V x y)
    {γ : ℝ → X} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Set.Icc a b))
    (hU : Set.MapsTo γ (Set.Icc a b) U) :
    k.edist (c (f (γ a))) (c (f (γ b))) ≤
      ENNReal.ofReal C * g.pathELength γ a b := by
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (f ∘ γ) (Set.Icc a b) := by
    intro t ht
    exact ((hf (γ t) (hU ht)).of_le (by simp)).comp_contMDiffWithinAt t (hγ t ht)
  exact (hstatic _ (hfV (hU ⟨le_rfl, hab⟩)) _ (hfV (hU ⟨hab, le_rfl⟩))).trans
    ((intrinsicEDist_le_pathELength h hab hcomp (hfV.comp hU)).trans
      (pathELength_comp_le_mul g h hC hf hmetric hγ hU))

/-- A cover of local path bounds gives the global distance bound for the
explicit source and target metrics. The map can be nonsmooth on its
constant-tail boundary, as in Proposition 15.12, Morgan--Tian p. 365. -/
theorem metric_edist_le_mul_of_open_cover [RegularSpace Y]
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    {ι : Type*} (U : ι → Set X) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x, ∃ i, x ∈ U i) (f : X → Y)
    {C : ℝ} (hC : 0 < C)
    (hlocal : ∀ i, ∀ (γ : ℝ → X) (a b : ℝ), a ≤ b →
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Set.Icc a b) →
      Set.MapsTo γ (Set.Icc a b) (U i) →
      h.edist (f (γ a)) (f (γ b)) ≤ ENNReal.ofReal C * g.pathELength γ a b)
    (x y : X) : h.edist (f x) (f y) ≤ ENNReal.ofReal C * g.edist x y := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : X → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : Y → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : Y → Type _) :=
    ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : PseudoEMetricSpace Y := PseudoEMetricSpace.ofRiemannianMetric (𝓡 3) Y
  exact Manifold.edist_le_mul_riemannianEDist_of_open_cover U hU hcover f
    (ENNReal.ofReal_ne_zero_iff.mpr hC) ENNReal.ofReal_ne_top hlocal x y

/-- A globally smooth pullback bound implies an ambient distance bound.
Applied to the event's local embedding and child inverse, this transports
the same local collapse estimate into the actual child (Proposition 15.12). -/
theorem metric_edist_le_mul_of_pullback [RegularSpace Y]
    (g : RiemannianMetric 3 X) (h : RiemannianMetric 3 Y)
    {f : X → Y} {C : ℝ} (hC : 0 < C)
    (hf : ContMDiff (𝓡 3) (𝓡 3) ∞ f)
    (hmetric : ∀ x, ∀ v : TangentSpace (𝓡 3) x,
      h.inner (f x) (mfderiv (𝓡 3) (𝓡 3) f x v)
        (mfderiv (𝓡 3) (𝓡 3) f x v) ≤ C ^ 2 * g.inner x v v)
    (x y : X) : h.edist (f x) (f y) ≤ ENNReal.ofReal C * g.edist x y := by
  apply metric_edist_le_mul_of_open_cover g h (fun _ : Unit => Set.univ)
    (fun _ => isOpen_univ) (fun _ => ⟨(), Set.mem_univ _⟩) f hC
  intro _ γ a b hab hγ hU
  exact edist_comp_le_mul_pathELength g h hC (fun z _ => hf z)
    (fun z _ => hmetric z) hab hγ hU

end PoincareMT.SurgeryComparison
