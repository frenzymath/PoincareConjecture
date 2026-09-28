import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_HorizontalDisk
import PoincareConjecture.Proofs.M14.Sec6_3_FamilyDensity
import PoincareConjecture.Proofs.M14.Sec6_3_InitialVector
import PoincareConjecture.Proofs.M14.Sec6_3_SquareRootComparison

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

noncomputable def exponentialPhase (E : M14ExponentialFamily G T x)
    (Z : G.Horizontal x) (s : ℝ) : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal :=
  TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (E := G.Horizontal)
    (E.gamma Z s) (M14.projectedCurveVelocityWithin G (E.gamma Z) (Icc 0 s) s)

theorem exponentialPhase_eq_squarePath (E : M14ExponentialFamily G T x)
    {Z : G.Horizontal x} {s : ℝ} (hZ : (Z, s) ∈ E.domain) (hs : 0 < s) :
    exponentialPhase E Z s = TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
      (E := G.Horizontal) ((E.square_path Z s hZ hs).curve s)
      ((E.square_path Z s hZ hs).horizontal_velocity s) := by
  let R := E.square_path Z s hZ hs
  have hC : M14SqrtParameterInterval 0 (s ^ 2) = Icc 0 s := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hs.le]
  have hpoint : EqOn (E.gamma Z) R.curve (Icc 0 s) := by
    intro r hr
    exact (M14.exponential_square_curve_eq E Z hZ hs (hC ▸ hr)).symm
  have hsC : s ∈ Icc 0 s := ⟨hs.le, le_rfl⟩
  have hvel := M14.projectedCurveVelocityWithin_congrOn (G := G) hpoint hsC
  rw [M14.squareRoot_projectedVelocityWithin_subset R (by rw [hC]) hsC
    (uniqueDiffOn_Icc hs s hsC)] at hvel
  exact TotalSpace.ext (hpoint hsC) hvel

theorem exponentialPhase_continuousOn (E : M14ExponentialFamily G T x)
    {s : ℝ} (hs : 0 < s) :
    ContinuousOn (fun Z => exponentialPhase E Z s) {Z | (Z, s) ∈ E.domain} := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : RiemannianBundle G.Horizontal := ⟨metric⟩
  intro Z hZ
  obtain ⟨O, hO, hZO, hsub⟩ := E.domain_relative_open (Z, s) hZ
  let U : Set (G.Horizontal x) := {W | (W, s) ∈ O}
  have hU : IsOpen U := hO.preimage (continuous_id.prodMk continuous_const)
  have hZU : Z ∈ U := hZO
  have hprefix : U ×ˢ Icc 0 s ⊆ E.domain := by
    intro z hz
    have hend : (z.1, s) ∈ E.domain :=
      hsub ⟨hz.1, (E.domain_admissible hZ).1, (E.domain_admissible hZ).2⟩
    exact (E.maximal_lifetime z.1).out (E.domain_zero z.1) hend hz.2
  have hgamma₀ : ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ)))
      (spacetimeModel n) ∞ (fun z : G.Horizontal x × ℝ => E.gamma z.1 z.2)
      (U ×ˢ Icc 0 s) := E.family_smooth.mono hprefix
  have hgamma : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓘(ℝ, G.Horizontal x)))
      (spacetimeModel n) ∞ (fun z : ℝ × G.Horizontal x => E.gamma z.2 z.1)
      (Icc 0 s ×ˢ U) :=
    hgamma₀.comp (contMDiff_snd.prodMk contMDiff_fst).contMDiffOn
      (fun _ hz => ⟨hz.2, hz.1⟩)
  have hphase := M14.squareFamilyVelocity_contMDiffOn (uniqueDiffOn_Icc hs) hU hgamma
  have hfixed : ContinuousOn (fun W => exponentialPhase E W s) U :=
    hphase.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun _ hW => ⟨⟨hs.le, le_rfl⟩, hW⟩)
  exact (hfixed.continuousAt (hU.mem_nhds hZU)).continuousWithinAt

theorem exponentialPhase_mem_compactDisk_of_tendsto
    (E : M14ExponentialFamily G T x) {K : Set G.Point} (hK : IsCompact K)
    (C : ℝ) {Zk : ℕ → G.Horizontal x} {Z : G.Horizontal x}
    (hZk : Tendsto Zk atTop (𝓝 Z)) {s : ℝ} (hs : 0 < s)
    (hZ : (Z, s) ∈ E.domain) (hsurv : ∀ k, (Zk k, s) ∈ E.domain)
    (hphase : ∀ k, (exponentialPhase E (Zk k) s).proj ∈ K ∧
      G.spacetime.horizontalMetric.inner (exponentialPhase E (Zk k) s).proj
        (exponentialPhase E (Zk k) s).2 (exponentialPhase E (Zk k) s).2 ≤ C) :
    (exponentialPhase E Z s).proj ∈ K ∧
      G.spacetime.horizontalMetric.inner (exponentialPhase E Z s).proj
        (exponentialPhase E Z s).2 (exponentialPhase E Z s).2 ≤ C := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : ∀ q, NormedAddCommGroup (G.Horizontal q) := fun q =>
    (metric.toCore q).toNormedAddCommGroupOfTopology
      (metric.continuousAt q) (metric.isVonNBounded q)
  let : ∀ q, InnerProductSpace ℝ (G.Horizontal q) := fun q =>
    .ofCoreOfTopology (metric.toCore q) (metric.continuousAt q) (metric.isVonNBounded q)
  let : RiemannianBundle G.Horizontal := ⟨metric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n)) G.Horizontal :=
    ⟨⟨G.spacetime.horizontalMetric.inner,
      G.spacetime.horizontalMetric.toContinuousRiemannianMetric.continuous,
      fun _ _ _ => rfl⟩⟩
  have hi : Continuous
      (fun z : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal =>
        G.spacetime.horizontalMetric.inner z.proj z.2 z.2) :=
    Continuous.inner_bundle
      (b := fun z : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal => z.proj)
      (v := fun z => z.2) (w := fun z => z.2) continuous_id continuous_id
  have hclosed : IsClosed {z : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal |
      z.proj ∈ K ∧ G.spacetime.horizontalMetric.inner z.proj z.2 z.2 ≤ C} :=
    (hK.isClosed.preimage (FiberBundle.continuous_proj _ _)).inter
      (isClosed_le hi continuous_const)
  have hwithin : Tendsto Zk atTop (𝓝[{W | (W, s) ∈ E.domain}] Z) :=
    tendsto_nhdsWithin_iff.mpr ⟨hZk, Eventually.of_forall hsurv⟩
  have ht : Tendsto (fun W => exponentialPhase E W s)
      (𝓝[{W | (W, s) ∈ E.domain}] Z) (𝓝 (exponentialPhase E Z s)) :=
    exponentialPhase_continuousOn E hs Z hZ
  exact hclosed.mem_of_tendsto (ht.comp hwithin)
    (Eventually.of_forall hphase)

end PoincareConjecture.Proofs.M46
