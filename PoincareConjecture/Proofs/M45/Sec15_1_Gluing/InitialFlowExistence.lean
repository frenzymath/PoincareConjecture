import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.InitialContinuation
import PoincareConjecture.Proofs.M45.Sec15_1_Gluing.InitialCurvature
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Uniqueness
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Harnack.Regularity










set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M45

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem curvatureNorm_eq_of_metric_eq {g h : RiemannianMetric n M}
    (D : LeviCivitaData g) (E : LeviCivitaData h) (hgh : g = h) (x : M) :
    D.curvatureTensorNorm x = E.curvatureTensorNorm x := by
  subst h
  exact D.curvatureTensorNorm_eq E x



theorem ricci_eq_of_same_metric {g : RiemannianMetric n M}
    (D E : LeviCivitaData g) (x : M) (v w : TangentSpace (𝓡 n) x) :
    D.ricci x v w = E.ricci x v w := by
  simp only [LeviCivitaData.ricci, D.curvatureTensor_eq E]



theorem compact_curvature_le_two_Ico [CompactSpace M]
    {T : ℝ} (hT : 0 < T) (hTle : T ≤ 1 / 16)
    (F : RicciFlow n M (Ico 0 T))
    (hinit : ∀ x : M, (F.connection 0).curvatureTensorNorm x ≤ 1) :
    ∀ t ∈ Ico 0 T, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ 2 := by
  intro t ht x
  let b := (t + T) / 2
  have hb : 0 < b := by dsimp [b]; linarith [ht.1]
  have hbT : b < T := by dsimp [b]; linarith [ht.2]
  have hsub : Icc 0 b ⊆ Ico 0 T := fun _ hs => ⟨hs.1, hs.2.trans_lt hbT⟩
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F hsub
    ordConnected_Icc ⟨0, ⟨le_rfl, hb.le⟩, b, ⟨hb.le, le_rfl⟩, hb.ne⟩
  exact compact_curvature_le_two_of_initial_bound hb G hinit t
    ⟨ht.1, le_min (by dsimp [b]; linarith [ht.2]) (ht.2.le.trans hTle)⟩ x



noncomputable def withInitialConnection {J : Set ℝ} (F : RicciFlow n M J)
    (D₀ : LeviCivitaData (F.metric 0)) : RicciFlow n M J := by
  classical
  let D (t : ℝ) : LeviCivitaData (F.metric t) :=
    if ht : t = 0 then ht.symm ▸ D₀ else F.connection t
  exact
    { metric := F.metric
      connection := D
      interval := F.interval
      nontrivial := F.nontrivial
      smooth := F.smooth
      equation := by
        intro t ht x v w
        rw [ricci_eq_of_same_metric (D t) (F.connection t)]
        exact F.equation t ht x v w }



theorem exists_initial_flow_with_curvature [CompactSpace M]
    (hlocal : RicciFlowLocalTheory n M)
    (g₀ : RiemannianMetric n M) (D₀ : LeviCivitaData g₀)
    (hinit : ∀ x : M, D₀.curvatureTensorNorm x ≤ 1) :
    ∃ F : RicciFlow n M (Icc 0 (1 / 16 : ℝ)),
      F.metric 0 = g₀ ∧ HEq (F.connection 0) D₀ ∧
      ∀ t ∈ Icc 0 (1 / 16 : ℝ), ∀ x : M,
        (F.connection t).curvatureTensorNorm x ≤ 2 := by
  classical
  obtain ⟨T, hTB, _hT, F, hF⟩ := exists_long_flow_of_uniform_curvature
    hlocal g₀ (B := 1 / 16) (C := 2) (by
      intro T hT hTle F hF
      apply compact_curvature_le_two_Ico hT hTle F
      intro x
      rw [curvatureNorm_eq_of_metric_eq (F.connection 0) D₀ hF]
      exact hinit x)
  let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F
    (show Icc 0 (1 / 16 : ℝ) ⊆ Ico 0 T from
      fun _ ht => ⟨ht.1, ht.2.trans_lt hTB⟩)
    ordConnected_Icc ⟨0, by norm_num, 1 / 16, by norm_num, by norm_num⟩
  let D : LeviCivitaData (G.metric 0) := hF.symm ▸ D₀
  let H := withInitialConnection G D
  have hH0 : HEq (H.connection 0) D₀ := by
    simp only [H, withInitialConnection]
    exact eqRec_heq _ _
  refine ⟨H, hF, hH0, ?_⟩
  have hHinit (x : M) : (H.connection 0).curvatureTensorNorm x ≤ 1 := by
    rw [curvatureNorm_eq_of_metric_eq (H.connection 0) D₀ hF]
    exact hinit x
  intro t ht x
  exact compact_curvature_le_two_of_initial_bound (by norm_num) H hHinit t
    (by simpa only [min_self] using ht) x

end PoincareConjecture.M45
