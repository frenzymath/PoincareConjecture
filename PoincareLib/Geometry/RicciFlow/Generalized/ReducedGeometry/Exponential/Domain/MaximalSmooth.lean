import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Domain.SmoothPrefixPropagation
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.InitialValue.InitialSmooth

/-!
# Joint relative openness and smoothness of the actual maximal family

Morgan-Tian Definition 6.17 and Lemma 6.18, pp. 113-114.
Smooth-prefix propagation in the actual horizontal metric norm and
single-path continuation give a smooth relative tube near every
surviving positive pair. The zero-time results complete the frozen
joint relative openness, smoothness and continuity clauses.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareMT.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

/-- Every actual surviving positive prefix has a common open
initial-vector neighborhood on which survival and the contract's
joint smoothness hold through that closed time, Lemma 6.18,
pp. 113-114. -/
theorem initialValueCurve_smooth_prefix
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) {Z : G.Horizontal x} {s : ℝ}
    (hs : 0 < s) (hsurv : (Z, s) ∈ initialValueDomain G T x) :
    ∃ U : Set (G.Horizontal x), IsOpen U ∧ Z ∈ U ∧
      U ×ˢ Icc 0 s ⊆ initialValueDomain G T x ∧
      M14HorizontalFamilySmooth G (initialValueCurve G T x) (U ×ˢ Icc 0 s) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  have hprev : ∃ a ∈ I.domain, a < T :=
    ⟨T - s ^ 2, (initialValueDomain_admissible hbase hsurv).2,
      sub_lt_self T (sq_pos_of_pos hs)⟩
  obtain ⟨d, hd, U, hU, hZU, htube, hsm⟩ :=
    initialValueCurve_smooth_initial_tube hM04 hM12 hbase hprev Z
  obtain ⟨V, hV, hZV, hsurvV, hsmV⟩ := initialValueCurve_smooth_prefix_from_initial_tube
    hM04 hM12 hbase (fun V : G.Horizontal x => V) Z hs hsurv
    ⟨d, hd, U, hU, hZU, fun W hW => htube ⟨hW, hd.le, le_rfl⟩, hsm⟩
  exact ⟨V, hV, hZV, fun z hz => initialValueDomain_prefix
    (hsurvV z.1 hz.1) hz.2.1 hz.2.2, hsmV⟩

/-- Every positive surviving pair lies in a jointly smooth actual
survival tube that is a relative neighborhood in the full physically
admissible parameter set, including physical boundary times,
Lemma 6.18, pp. 113-114. -/
theorem initialValueCurve_smooth_neighborhood_positive
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) {Z : G.Horizontal x} {s : ℝ}
    (hs : 0 < s) (hsurv : (Z, s) ∈ initialValueDomain G T x) :
    ∃ r : ℝ, s ≤ r ∧ ∃ U : Set (G.Horizontal x), IsOpen U ∧ Z ∈ U ∧
      U ×ˢ Icc 0 r ∈ 𝓝[M14AdmissibleParameter G T x] (Z, s) ∧
      U ×ˢ Icc 0 r ⊆ initialValueDomain G T x ∧
      M14HorizontalFamilySmooth G (initialValueCurve G T x) (U ×ˢ Icc 0 r) := by
  obtain ⟨y, ⟨P⟩⟩ := (initialValueDomain_positive_iff hs).mp hsurv
  obtain ⟨r, hsr, hnear, z, Q, _⟩ :=
    exists_initialValuePath_extension_neighborhood hM04 hM12 P
  rw [Real.sqrt_sq hs.le] at hsr hnear
  have hr : 0 < r := hs.trans_le hsr
  obtain ⟨U, hU, hZU, htube, hsm⟩ :=
    initialValueCurve_smooth_prefix hM04 hM12 hbase hr (Or.inr ⟨hr, z, ⟨Q⟩⟩)
  refine ⟨r, hsr, U, hU, hZU, ?_, htube, hsm⟩
  have hprod : M14AdmissibleParameter G T x =
      (univ : Set (G.Horizontal x)) ×ˢ {r | 0 ≤ r ∧ T - r ^ 2 ∈ I.domain} := by
    ext w
    simp only [M14AdmissibleParameter, mem_ofPred_eq, mem_prod, mem_univ, true_and]
  rw [hprod, nhdsWithin_prod_eq, nhdsWithin_univ]
  exact prod_mem_prod (hU.mem_nhds hZU) hnear

/-- The actual maximal survival domain is relatively open in the
frozen admissible parameter set at every pair, Definition 6.17 and
Lemma 6.18, pp. 113-114. -/
theorem initialValueDomain_relative_open
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) :
    ∀ z ∈ initialValueDomain G T x, ∃ U : Set (G.Horizontal x × ℝ),
      IsOpen U ∧ z ∈ U ∧ U ∩ M14AdmissibleParameter G T x ⊆ initialValueDomain G T x := by
  rintro ⟨Z, s⟩ hz
  rcases eq_or_lt_of_le (initialValueDomain_nonneg hz) with hs | hs
  · subst s
    exact initialValueDomain_zero_relative_open hM04 hM12 hbase Z
  · obtain ⟨_, _, _, _, _, hnear, hsub, _⟩ :=
      initialValueCurve_smooth_neighborhood_positive hM04 hM12 hbase hs hz
    obtain ⟨U, hU, hzU, hUsub⟩ := mem_nhdsWithin.mp hnear
    exact ⟨U, hU, hzU, hUsub.trans hsub⟩

/-- The actual selected maximal family has precisely the frozen
joint within smoothness on its whole survival domain, including
zero and physical closed endpoints, Lemma 6.18, pp. 113-114. -/
theorem initialValueCurve_family_smooth
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) :
    M14HorizontalFamilySmooth G (initialValueCurve G T x) (initialValueDomain G T x) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  rintro ⟨Z, s⟩ hz
  rcases eq_or_lt_of_le (initialValueDomain_nonneg hz) with hs | hs
  · subst s
    exact initialValueCurve_contMDiffWithinAt_zero hM04 hM12 hbase Z
  · obtain ⟨r, hsr, U, _, hZU, hnear, _, hsm⟩ :=
      initialValueCurve_smooth_neighborhood_positive hM04 hM12 hbase hs hz
    exact (hsm (Z, s) ⟨hZU, hs.le, hsr⟩).mono_of_mem_nhdsWithin
      (nhdsWithin_mono (Z, s) (initialValueDomain_admissible hbase) hnear)

/-- The actual selected family is jointly continuous on its whole
maximal survival domain, the continuity clause of Lemma 6.18,
pp. 113-114. -/
theorem initialValueCurve_joint_continuous
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hbase : G.spacetime.timeFunction x = T) :
    ContinuousOn (fun z : G.Horizontal x × ℝ => initialValueCurve G T x z.1 z.2)
      (initialValueDomain G T x) := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  exact (initialValueCurve_family_smooth hM04 hM12 hbase).continuousOn

end PoincareMT.M14
