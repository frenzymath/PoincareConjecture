import PoincareConjecture.Definitions.Ch01.TensorOperators
import PoincareConjecture.Definitions.Ch03.RicciFlow
import PoincareConjecture.Proofs.M04.ScalarEvolution
import PoincareConjecture.Proofs.M04.ScalarStrongMaximum
import PoincareConjecture.Proofs.M04.PointwiseFlatness
import PoincareConjecture.Proofs.M04.CompactRicciPreservation
import PoincareConjecture.Proofs.M04.CompactSectionalPreservation

set_option autoImplicit false

open scoped Manifold ContDiff Bundle
open Set Topology Filter

universe u

namespace PoincareConjecture.RicciFlow

variable {N : Type u} [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
  [T2Space N] [SecondCountableTopology N]

theorem nonnegativeSectionalCurvature_preserved [CompactSpace N]
    {T : ℝ} (hT : 0 < T) (F : RicciFlow 3 N (Set.Icc 0 T))
    (hinit : (F.connection 0).NonnegativeSectionalCurvature) :
    ∀ t ∈ Set.Icc 0 T, (F.connection t).NonnegativeSectionalCurvature := by
  exact M04.nonnegativeSectionalCurvature_preserved_compact hT F hinit

theorem nonnegativeRicciCurvature_preserved [CompactSpace N]
    {T : ℝ} (hT : 0 < T) (F : RicciFlow 3 N (Set.Icc 0 T))
    (hinit : (F.connection 0).NonnegativeRicciCurvature) :
    ∀ t ∈ Set.Icc 0 T, (F.connection t).NonnegativeRicciCurvature := by
  exact M04.nonnegativeRicciCurvature_preserved_compact hT F hinit

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in

theorem flat_of_scalarCurvature_eq_zero [ConnectedSpace N]
    {T : ℝ} (hT : 0 < T) (F : RicciFlow 3 N (Set.Icc 0 T))
    (hsec : ∀ t ∈ Set.Icc 0 T, (F.connection t).NonnegativeSectionalCurvature)
    (p : N) (hzero : (F.connection T).scalarCurvature p = 0) :
    ∀ t ∈ Set.Icc 0 T, ∀ x : N, (F.connection t).curvatureTensorNorm x = 0 := by
  let f : ℝ → N → ℝ := fun t x ↦ (F.connection t).scalarCurvature x
  let v : ℝ → N → ℝ := fun t x ↦
    (F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x
  have hc : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ univ) :=
    F.contMDiffOn_scalarCurvature.continuousOn
  have hd (t : ℝ) (ht : t ∈ Icc 0 T) (x : N) :
      HasDerivWithinAt (fun s ↦ f s x) (v t x) (Icc 0 T) t :=
    F.hasDerivWithinAt_scalarCurvature t ht x
  have hsmooth (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (f t) := F.contMDiff_scalarCurvature t ht
  have hnonneg (t : ℝ) (ht : t ∈ Icc 0 T) (x : N) : 0 ≤ f t x :=
    M04.nonneg_scalar_of_nonnegativeSectionalAt (F.connection t) x (hsec t ht x)
  have hevol (t : ℝ) (x : N) : (F.connection t).laplacian (f t) x ≤ v t x := by
    have hnorm : 0 ≤ (F.connection t).ricciNormSq x := by
      exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _
    dsimp [f, v]
    linarith
  have hbefore (s : ℝ) (hs : s ∈ Ico 0 T) (x : N) : f s x = 0 := by
    apply le_antisymm ?_ (hnonneg s ⟨hs.1, hs.2.le⟩ x)
    by_contra hnot
    have hpositive : 0 < f s x := lt_of_not_ge hnot
    have hsub : Icc s T ⊆ Icc 0 T := Icc_subset_Icc hs.1 le_rfl
    have hterminal := M04.ricciFlow_supersolution_positive_at_later_time hs.2 F hsub f v
      (hc.mono (prod_mono hsub Subset.rfl))
      (fun t ht y ↦ (hd t (hsub ht) y).mono hsub)
      (fun t ht ↦ hsmooth t (hsub ht))
      (fun t ht y ↦ hnonneg t (hsub ht) y)
      (fun t _ y ↦ hevol t y) x hpositive p
    change 0 < (F.connection T).scalarCurvature p at hterminal
    rw [hzero] at hterminal
    exact (lt_irrefl 0) hterminal
  intro t ht x
  have hzeroBefore : EqOn (fun s ↦ f s x) (fun _ ↦ (0 : ℝ)) (Ico 0 T) :=
    fun s hs ↦ hbefore s hs x
  have hcTime : ContinuousOn (fun s ↦ f s x) (Icc 0 T) :=
    (F.contDiffOn_scalarCurvature_timeSlice x).continuousOn
  have hzeroAll : EqOn (fun s ↦ f s x) (fun _ ↦ (0 : ℝ)) (Icc 0 T) :=
    hzeroBefore.of_subset_closure hcTime continuousOn_const Ico_subset_Icc_self
      (by rw [closure_Ico hT.ne])
  exact M04.curvatureTensorNorm_eq_zero_of_nonnegativeSectionalAt_scalar_zero
    (F.connection t) x (hsec t ht x) (hzeroAll ht)

end PoincareConjecture.RicciFlow
