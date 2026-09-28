import PoincareConjecture.Proofs.M47.SeedNormalizedPath
import PoincareConjecture.Proofs.M47.JointSeedOrdinary
import PoincareConjecture.Proofs.M09.PathComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [ConnectedSpace M]

theorem seed_reducedLength_normalized_le
    {J K : Set ℝ} {F : RicciFlow 3 M J} {G : RicciFlow 3 M K}
    {T U d sigma oldMax newMax : ℝ} (hd : 0 < d) (hsigma : 0 < sigma)
    (hOld : LGeodesicTheory F T oldMax) (hNew : LGeodesicTheory G U newMax)
    (hold : d * sigma ≤ oldMax) (hnew : sigma ≤ newMax)
    (hwindow : Icc (U - sigma) U ⊆ K)
    (hmetric : ∀ s ∈ Icc (0 : ℝ) sigma, ∀ x (v w : TangentSpace (𝓡 3) x),
      (G.metric (U - s)).inner x v w = d⁻¹ * (F.metric (T - d * s)).inner x v w)
    (hscalar : ∀ s ∈ Icc (0 : ℝ) sigma, ∀ x,
      (G.connection (U - s)).scalarCurvature x =
        d * (F.connection (T - d * s)).scalarCurvature x)
    (x y : M) :
    reducedLength G U x y sigma ≤ reducedLength F T x y (d * sigma) := by
  obtain ⟨p, hp0, hpEnd, _hpMin, hpValue⟩ :=
    hOld.reduced_length_attained (d * sigma) (mul_pos hd hsigma) hold x y
  let q := seedNormalizedPath hd hsigma hwindow hmetric hscalar p
  have hq0 : q.curve 0 = x := by simpa only [q, seedNormalizedPath, mul_zero] using hp0
  have hqEnd : q.curve sigma = y := hpEnd
  have hbound := M09.reducedLength_le_path hNew hsigma hnew q hq0 hqEnd
  refine hbound.trans_eq ?_
  rw [hpValue, seedNormalizedPath_length hd hsigma hwindow hmetric hscalar p,
    Real.sqrt_mul hd.le]
  ring

theorem seed_compact_normalized_access
    (P : M14OrdinaryProviders.{u} 3)
    [T3Space M] [SecondCountableTopology M] [CompactSpace M]
    {b T sigma : ℝ} (hbt : b < T) (hsigma : 0 < sigma) (hsigmaOne : sigma ≤ 1)
    (F : RicciFlow 3 M (Icc b T)) (G : RicciFlow 3 M (Icc 0 1))
    (hmetric : ∀ s ∈ Icc (0 : ℝ) sigma, ∀ x (v w : TangentSpace (𝓡 3) x),
      (G.metric (1 - s)).inner x v w =
        (T - b)⁻¹ * (F.metric (T - (T - b) * s)).inner x v w)
    (hscalar : ∀ s ∈ Icc (0 : ℝ) sigma, ∀ x,
      (G.connection (1 - s)).scalarCurvature x =
        (T - b) * (F.connection (T - (T - b) * s)).scalarCurvature x)
    (x y : M) :
    reducedLength G 1 x y sigma ≤ reducedLength F T x y ((T - b) * sigma) := by
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  have hd : 0 < T - b := sub_pos.mpr hbt
  have hT : T ∈ Icc b T := ⟨hbt.le, le_rfl⟩
  have hOldWindow : Icc (T - (T - b)) T ⊆ Icc b T := by rw [sub_sub_cancel]
  have hOldBounded : CompleteBoundedCurvatureOn F (Icc (T - (T - b)) T) := by
    simpa only [sub_sub_cancel] using PoincareConjecture.M47.jointSeed_completeBoundedCurvatureOn F
  obtain ⟨hOld⟩ := P.m08 M (Icc b T) F T (T - b) hT hd hOldWindow hOldBounded
  have hNewWindow : Icc ((1 : ℝ) - 1) 1 ⊆ Icc 0 1 := by norm_num
  have hNewBounded : CompleteBoundedCurvatureOn G (Icc ((1 : ℝ) - 1) 1) := by
    simpa only [sub_self] using PoincareConjecture.M47.jointSeed_completeBoundedCurvatureOn G
  obtain ⟨hNew⟩ := P.m08 M (Icc 0 1) G 1 1 (by norm_num) (by norm_num)
    hNewWindow hNewBounded
  apply seed_reducedLength_normalized_le hd hsigma hOld hNew
    (by nlinarith) hsigmaOne _ hmetric hscalar x y
  intro s hs
  exact ⟨by linarith [hs.1], hs.2⟩

end PoincareConjecture.Proofs.M47
