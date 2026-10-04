import PoincareLib.Geometry.RicciFlow.Compactness.Ancient.CompactEmbedding
import PoincareLib.Geometry.Manifold.InverseFunction.SmoothInverse
import PoincareLib.Geometry.Manifold.OpenEmbedding

/-!
# Actual partial charts for the retained ancient embeddings

An injective local diffeomorphism on an open set gives an actual partial
diffeomorphism with that exact source and map. Applied to the retained
spatial embedding composed with a reference chart, this supplies chart
pullbacks before any bounded ancient-solution package is constructed.

Reference: Morgan--Tian, Theorem 9.64, pp. 225-229.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareMT.AncientCompactness

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N] [Nonempty M]

/-- Package the actual map of an injective local diffeomorphism, with its
prescribed open source and its exact image as target. -/
noncomputable def partialDiffeomorphOfInjOn
    {U : Set M} (hU : IsOpen U) (f : M → N) (hinj : InjOn f U)
    (hf : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ f U) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) M N ∞ := by
  classical
  let e := hinj.toPartialEquiv f U
  have hopen : IsOpen (f '' U) := by
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨d, hxd, hfd⟩ := hf.isLocalHomeomorphOn x hx
    have hdopen : IsOpen (d '' (d.source ∩ U)) :=
      d.isOpen_image_of_subset_source (d.open_source.inter hU) inter_subset_left
    rw [hfd]
    exact mem_of_superset (hdopen.mem_nhds (mem_image_of_mem d ⟨hxd, hx⟩))
      (image_mono inter_subset_right)
  refine
    { toPartialEquiv := e
      open_source := hU
      open_target := hopen
      contMDiffOn_toFun := hf.contMDiffOn
      contMDiffOn_invFun := ?_ }
  rintro _ ⟨x, hx, rfl⟩
  apply ContMDiffAt.contMDiffWithinAt
  apply Poincare.contMDiffAt_of_local_left_inverse (hf ⟨x, hx⟩).contMDiffAt
    ((hf ⟨x, hx⟩).mfderivToContinuousLinearEquiv (by simp)).bijective
  filter_upwards [hU.mem_nhds hx] with z hz
  exact e.left_inv hz

@[simp] theorem partialDiffeomorphOfInjOn_source
    {U : Set M} (hU : IsOpen U) (f : M → N) (hinj : InjOn f U)
    (hf : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ f U) :
    (partialDiffeomorphOfInjOn hU f hinj hf).source = U := rfl

@[simp] theorem partialDiffeomorphOfInjOn_coe
    {U : Set M} (hU : IsOpen U) (f : M → N) (hinj : InjOn f U)
    (hf : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ f U) :
    (partialDiffeomorphOfInjOn hU f hinj hf : M → N) = f := rfl

@[simp] theorem partialDiffeomorphOfInjOn_target
    {U : Set M} (hU : IsOpen U) (f : M → N) (hinj : InjOn f U)
    (hf : IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞ f U) :
    (partialDiffeomorphOfInjOn hU f hinj hf).target = f '' U := rfl

end PoincareMT.AncientCompactness

namespace PoincareMT.AncientPointedGeometricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t2Space

variable {n : ℕ} {C : ℕ → FlowCarrier.{0} n}
  {g : ∀ k, ℝ → (C k).metric} {p : ∀ k, (C k).carrier} {T : ℝ}
  (G : AncientPointedGeometricConvergence C g p T)

/-- The exact coordinate domain on which the retained spatial embedding
is used at the specified exhaustion stage. -/
def embeddingChartSource (q : G.limitCarrier.carrier) (k : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  (extChartAt (𝓡 n) q).target ∩ (extChartAt (𝓡 n) q).symm ⁻¹' G.exhaustion k

theorem embeddingChartSource_open (q : G.limitCarrier.carrier) (k : ℕ) :
    IsOpen (G.embeddingChartSource q k) :=
  (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.isOpen_inter_preimage
    (isOpen_extChartAt_target (I := 𝓡 n) q) (G.exhaustion_open k)

private theorem partialChart_reference_isLocalDiffeomorphAt
    (q : G.limitCarrier.carrier) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (extChartAt (𝓡 n) q).target) :
    IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ (extChartAt (𝓡 n) q).symm x := by
  let d : PartialDiffeomorph (𝓡 n) (𝓡 n) G.limitCarrier.carrier
      (EuclideanSpace ℝ (Fin n)) ∞ :=
    { toPartialEquiv := (chartAt (EuclideanSpace ℝ (Fin n)) q).toPartialEquiv
      open_source := (chartAt (EuclideanSpace ℝ (Fin n)) q).open_source
      open_target := (chartAt (EuclideanSpace ℝ (Fin n)) q).open_target
      contMDiffOn_toFun := contMDiffOn_chart
      contMDiffOn_invFun := contMDiffOn_chart_symm }
  have hx' : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q).target := by
    simpa only [extChartAt_target, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, preimage_id, range_id, inter_univ] using hx
  exact d.symm.isLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞ hx'

theorem embeddingChart_injOn (q : G.limitCarrier.carrier) (k : ℕ) :
    InjOn (G.embedding k ∘ (extChartAt (𝓡 n) q).symm) (G.embeddingChartSource q k) := by
  intro x hx y hy hxy
  apply (extChartAt (𝓡 n) q).symm.injOn hx.1 hy.1
  have hsub : (⟨(extChartAt (𝓡 n) q).symm x, hx.2⟩ : G.exhaustion k) =
      ⟨(extChartAt (𝓡 n) q).symm y, hy.2⟩ := (G.embedding_open k).injective hxy
  exact congrArg Subtype.val hsub

theorem embeddingChart_isLocalDiffeomorphOn (q : G.limitCarrier.carrier) (k : ℕ) :
    IsLocalDiffeomorphOn (𝓡 n) (𝓡 n) ∞
      (G.embedding k ∘ (extChartAt (𝓡 n) q).symm) (G.embeddingChartSource q k) := by
  intro x
  exact (G.partialChart_reference_isLocalDiffeomorphAt q x.property.1).comp
    (𝓡 n) (C (G.subsequence k)).carrier (G.embedding_smooth k ⟨_, x.property.2⟩)

/-- The stored embedding composed with the reference chart, as an actual
partial diffeomorphism on its exact valid coordinate domain. -/
noncomputable def embeddingChartPartialDiffeomorph (q : G.limitCarrier.carrier) (k : ℕ) :
    PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n))
      (C (G.subsequence k)).carrier ∞ :=
  AncientCompactness.partialDiffeomorphOfInjOn (G.embeddingChartSource_open q k)
    (G.embedding k ∘ (extChartAt (𝓡 n) q).symm)
    (G.embeddingChart_injOn q k) (G.embeddingChart_isLocalDiffeomorphOn q k)

@[simp] theorem embeddingChartPartialDiffeomorph_source (q : G.limitCarrier.carrier) (k : ℕ) :
    (G.embeddingChartPartialDiffeomorph q k).source = G.embeddingChartSource q k := rfl

@[simp] theorem embeddingChartPartialDiffeomorph_coe (q : G.limitCarrier.carrier) (k : ℕ) :
    (G.embeddingChartPartialDiffeomorph q k :
      EuclideanSpace ℝ (Fin n) → (C (G.subsequence k)).carrier) =
      G.embedding k ∘ (extChartAt (𝓡 n) q).symm := rfl

/-- Each compact coordinate test is contained in the actual partial-chart
source after one threshold, with no further subsequence extraction. -/
theorem eventually_subset_embeddingChartPartialDiffeomorph_source
    (q : G.limitCarrier.carrier) {K : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hKc : K ⊆ (extChartAt (𝓡 n) q).target) :
    ∀ᶠ k : ℕ in atTop, K ⊆ (G.embeddingChartPartialDiffeomorph q k).source := by
  have hc : ContinuousOn (extChartAt (𝓡 n) q).symm K :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).continuousOn.mono hKc
  obtain ⟨j, hj⟩ := G.exists_exhaustion_superset (hK.image_of_continuousOn hc)
  have hmono : Monotone G.exhaustion := monotone_nat_of_le_succ G.exhaustion_increasing
  filter_upwards [eventually_ge_atTop j] with k hk x hx
  exact ⟨hKc hx, hmono hk (hj (mem_image_of_mem _ hx))⟩

/-- An open reference-coordinate ball, centered at the coordinates of its
specified carrier point. -/
def referenceChartBall (q : G.limitCarrier.carrier) (r : ℝ) :
    TopologicalSpace.Opens (EuclideanSpace ℝ (Fin n)) :=
  ⟨Metric.ball (extChartAt (𝓡 n) q q) r, Metric.isOpen_ball⟩

/-- The inverse reference chart on the specified coordinate ball. -/
noncomputable def referenceChartBallMap (q : G.limitCarrier.carrier) (r : ℝ) :
    G.referenceChartBall q r → G.limitCarrier.carrier :=
  fun x => (extChartAt (𝓡 n) q).symm x

/-- Every carrier point admits a reference ball whose doubled closed ball
remains in the original chart target. -/
theorem exists_pos_referenceChartBall_radius (q : G.limitCarrier.carrier) :
    ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (extChartAt (𝓡 n) q q) (2 * r) ⊆ (extChartAt (𝓡 n) q).target := by
  obtain ⟨ε, hε, hεc⟩ := Metric.mem_nhds_iff.mp
    ((isOpen_extChartAt_target (I := 𝓡 n) q).mem_nhds (mem_extChartAt_target q))
  refine ⟨ε / 4, by positivity, ?_⟩
  exact (Metric.closedBall_subset_ball (by linarith : 2 * (ε / 4) < ε)).trans hεc

/-- The reference ball map is an actual local diffeomorphism whenever that
ball lies in the original chart target. -/
theorem referenceChartBallMap_isLocalDiffeomorph
    (q : G.limitCarrier.carrier) (r : ℝ)
    (hsource : Metric.ball (extChartAt (𝓡 n) q q) r ⊆ (extChartAt (𝓡 n) q).target) :
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (G.referenceChartBallMap q r) := by
  intro x
  exact (Poincare.isLocalDiffeomorph_opensSubtypeVal
    (𝓡 n) (G.referenceChartBall q r) x).comp (𝓡 n) G.limitCarrier.carrier
      (G.partialChart_reference_isLocalDiffeomorphAt q (hsource x.property))

/-- Positive reference balls indexed by their carrier points cover that
same carrier through the original inverse charts. -/
theorem referenceChartBallMap_covers
    (r : G.limitCarrier.carrier → ℝ) (hr : ∀ q, 0 < r q) :
    ∀ y : G.limitCarrier.carrier, ∃ q : G.limitCarrier.carrier,
      ∃ x : G.referenceChartBall q (r q),
      G.referenceChartBallMap q (r q) x = y := by
  intro y
  refine ⟨y, ⟨extChartAt (𝓡 n) y y, Metric.mem_ball_self (hr y)⟩, ?_⟩
  exact (extChartAt (𝓡 n) y).left_inv (mem_extChartAt_source y)

end PoincareMT.AncientPointedGeometricConvergence
