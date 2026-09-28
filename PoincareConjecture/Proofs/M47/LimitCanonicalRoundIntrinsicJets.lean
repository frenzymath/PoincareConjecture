import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Cor16_7_IntrinsicJetConvergence
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma11_2_RoundPullback

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M47

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Bilin" => E3 →L[ℝ] E3 →L[ℝ] ℝ

noncomputable local instance roundIntrinsicDualGroup : NormedAddCommGroup (E3 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance roundIntrinsicDualSpace : NormedSpace ℝ (E3 →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

noncomputable local instance roundIntrinsicBilinearGroup : NormedAddCommGroup Bilin :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance roundIntrinsicBilinearSpace : NormedSpace ℝ Bilin :=
  ContinuousLinearMap.toNormedSpace

theorem limitCanonical_round_intrinsic_difference_bound
    (g : RiemannianMetric 3 E3) (D : LeviCivitaData g)
    {B : ℕ → E3 → Bilin} {C : E3 → Bilin} {U K : Set E3}
    (h : CompactSmoothConvergenceOn B C atTop U)
    (hK : IsCompact K) (hKU : K ⊆ U) (m : ℕ) {eta : ℝ} (heta : 0 < eta) :
    ∃ bound : ℝ, bound < eta ∧ ∀ᶠ k in atTop, ∀ x ∈ K,
      (∑ j ∈ Finset.range (m + 1), g.tensorNorm
        (D.iteratedCovariantTensorDerivative
          (fun y (v : Fin 2 → E3) => B k y (v 0) (v 1) - C y (v 0) (v 1)) j) x ^ 2) ≤ bound := by
  have hg : CompactSmoothConvergenceOn (fun _ : ℕ => g.euclideanCoefficients)
      g.euclideanCoefficients atTop U :=
    CompactSmoothConvergenceOn.constant h.isOpen
      (fun x _ => (g.contDiffAt_euclideanCoefficients x).contDiffWithinAt)
  have hC : CompactSmoothConvergenceOn (fun _ : ℕ => C) C atTop U :=
    CompactSmoothConvergenceOn.constant h.isOpen h.smooth
  have hadd : ContDiff ℝ ∞ (fun z : Bilin × (Bilin × Bilin) => z.1 + (z.2.1 - z.2.2)) :=
    contDiff_fst.add (contDiff_snd.fst.sub contDiff_snd.snd)
  have hshift := (hg.prodMk (h.prodMk hC)).comp_smooth
    isOpen_univ hadd.contDiffOn (fun _ _ => mem_univ _)
  simp only [Function.comp_def, sub_self, add_zero] at hshift
  obtain ⟨bound, hbound, htail⟩ :=
    M44.eventually_intrinsic_jet_error_bound g D hshift hK hKU m heta
  refine ⟨bound, hbound, ?_⟩
  filter_upwards [htail] with k hk x hx
  have heq : (fun y (v : Fin 2 → E3) =>
      (g.euclideanCoefficients y + (B k y - C y)) (v 0) (v 1) -
        g.inner y (v 0) (v 1)) =
      (fun y v => B k y (v 0) (v 1) - C y (v 0) (v 1)) := by
    funext y v
    change g.inner y (v 0) (v 1) + (B k y (v 0) (v 1) - C y (v 0) (v 1)) -
      g.inner y (v 0) (v 1) = _
    ring
  have hxbound := hk x hx
  change (∑ j ∈ Finset.range (m + 1), g.tensorNorm
    (D.iteratedCovariantTensorDerivative
      (fun y (v : Fin 2 → E3) =>
        (g.euclideanCoefficients y + (B k y - C y)) (v 0) (v 1) -
          g.inner y (v 0) (v 1)) j) x ^ 2) ≤ bound at hxbound
  rw [heq] at hxbound
  exact hxbound

theorem limitCanonical_round_local_difference_energy
    {X : Type*} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold (𝓡 3) ∞ X]
    (g : RiemannianMetric 3 E3) (D : LeviCivitaData g)
    (gR : RiemannianMetric 3 X) (DR : LeviCivitaData gR)
    {f : E3 → X} {U : Set E3} (hU : IsOpen U)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f U)
    (hinv : ∀ y ∈ U, (mfderiv (𝓡 3) (𝓡 3) f y).IsInvertible)
    (hmetric : ∀ y ∈ U, ∀ u v : E3,
      g.inner y u v = gR.inner (f y) (mfderiv (𝓡 3) (𝓡 3) f y u)
        (mfderiv (𝓡 3) (𝓡 3) f y v))
    {B C : E3 → Bilin} (hB : ContDiffOn ℝ ∞ B U) (hC : ContDiffOn ℝ ∞ C U)
    (T : CovariantTensorEvaluation 3 X 2) (hT : IsSmoothCovariantTensor T)
    (hread : ∀ y ∈ U, ∀ v : Fin 2 → E3,
      B y (v 0) (v 1) - C y (v 0) (v 1) =
        T (f y) (fun i => mfderiv (𝓡 3) (𝓡 3) f y (v i)))
    (m : ℕ) {x : E3} (hx : x ∈ U) :
    (∑ j ∈ Finset.range (m + 1), g.tensorNorm
      (D.iteratedCovariantTensorDerivative
        (fun y (v : Fin 2 → E3) => B y (v 0) (v 1) - C y (v 0) (v 1)) j) x ^ 2) =
      ∑ j ∈ Finset.range (m + 1),
        gR.tensorNorm (DR.iteratedCovariantTensorDerivative T j) (f x) ^ 2 := by
  obtain ⟨A, hA, heq⟩ := M36.exists_comparison_smooth_germ hU (hB.sub hC) hx
  obtain ⟨W, hWsub, hW, hxW⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hx) heq)
  have hWU : W ⊆ U := fun y hy => (hWsub hy).1
  have hAT : ∀ᶠ y in 𝓝 x,
      (fun v : Fin 2 → E3 => A y (v 0) (v 1)) =
        (fun v => B y (v 0) (v 1) - C y (v 0) (v 1)) := by
    filter_upwards [heq] with y hy
    funext v
    rw [hy]
    rfl
  apply Finset.sum_congr rfl
  intro j _hj
  congr 1
  have hpoint :=
    (M36.comparison_iteratedCovariantTensorDerivative_eventuallyEq D hAT j).self_of_nhds
  have hnorm := M44.tensorNorm_iterated_eq_of_metric_pullback D DR hW (hf.mono hWU)
    (fun y hy => hinv y (hWU hy)) (fun y hy => hmetric y (hWU hy))
    (M36.comparison_bilinear_isSmooth hA) hT (fun y hy v => by
      rw [(hWsub hy).2]
      exact hread y (hWU hy) v) j hxW
  apply Eq.trans ?_ hnorm
  unfold RiemannianMetric.tensorNorm
  apply congrArg Real.sqrt
  apply Finset.sum_congr rfl
  intro a _ha
  exact congrArg (fun T => (T (fun i => g.orthonormalBasis x (a i))) ^ 2) hpoint.symm

end PoincareConjecture.M47
