import PoincareConjecture.Proofs.M47.ScalarPersistenceProof
import PoincareConjecture.Statements.M13Rescaling
import PoincareConjecture.Proofs.M13.ContractionTransport
import PoincareConjecture.Proofs.M13.Length










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47



theorem exists_physical_scalar_persistence
    (P : M47ScalarPersistencePredecessors.{u})
    (rescale : GeneralizedParabolicRescalingTheory.{u} 3)
    (K a : ℝ) (hK : 0 < K) (ha : 0 < a) :
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [T2Space M] [SecondCountableTopology M],
      ∀ (s t H : ℝ), s < t → 0 < H →
      ∀ (F : RicciFlow 3 M (Icc s t)) (p : M),
        IsCompact (closure ((F.metric s).ball p (a / Real.sqrt H))) →
        (∀ u ∈ Icc s t, ∀ x ∈ (F.metric s).ball p (a / Real.sqrt H),
          (F.connection u).curvatureTensorNorm x ≤ K * H) →
        (∀ u ∈ Icc s t, ∀ x ∈ (F.metric s).ball p (a / Real.sqrt H),
          -H ≤ (F.connection u).scalarCurvature x) →
        (∀ x ∈ (F.metric s).ball p (a / Real.sqrt H),
          3 * H / 4 ≤ (F.connection s).scalarCurvature x) →
        H * (t - s) ≤ tau → H / 4 ≤ (F.connection t).scalarCurvature p := by
  obtain ⟨tau, htau, htau1, hpersist⟩ := localScalarPersistence P K a hK ha
  refine ⟨tau, htau, htau1, ?_⟩
  intro M _ _ _ _ _ s t H hst hH F p hcompact hcurvature hfloor hinitial hshort
  let I : SpacetimeInterval := {
    domain := Icc s t
    ordConnected := ordConnected_Icc
    nontrivial := F.nontrivial
  }
  obtain ⟨R⟩ := rescale.ordinary_flow M I F H hH s
  let T := H * (t - s)
  have hT : 0 < T := mul_pos hH (sub_pos.mpr hst)
  have hclock (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) :
      parabolicTimeInv H s u ∈ Icc s t := by
    dsimp only [parabolicTimeInv]
    constructor
    · linarith [div_nonneg hu.1 hH.le]
    · have hd : u / H ≤ t - s := (div_le_iff₀ hH).2 (by
        have h := hu.2
        dsimp only [T] at h
        nlinarith)
      linarith
  have hsub : Icc (0 : ℝ) T ⊆ (parabolicInterval H hH s I).domain := by
    intro u hu
    exact (mem_parabolicInterval_iff H hH s I u).2 (hclock u hu)
  let G : RicciFlow 3 M (Icc 0 T) := {
    metric := R.flow.metric
    connection := R.flow.connection
    interval := ordConnected_Icc
    nontrivial := ⟨0, ⟨le_rfl, hT.le⟩, T, ⟨hT.le, le_rfl⟩, hT.ne⟩
    smooth := R.flow.smooth.mono (Set.prod_mono hsub Subset.rfl)
    equation := fun u hu x v w => (R.flow.equation u (hsub hu) x v w).mono hsub
  }
  have hscalar (u : ℝ) (x : M) :
      (G.connection u).scalarCurvature x =
        (F.connection (parabolicTimeInv H s u)).scalarCurvature x / H := by
    simpa only [Diffeomorph.coe_refl, id_eq] using
      M13.homothety_scalarCurvature_eq _ _ (Diffeomorph.refl (𝓡 3) M ∞)
        H hH (R.metric_homothety u) (F.connection _) (R.flow.connection u) x
  have hnorm (u : ℝ) (x : M) :
      (G.connection u).curvatureTensorNorm x =
        (F.connection (parabolicTimeInv H s u)).curvatureTensorNorm x / H := by
    simpa only [Diffeomorph.coe_refl, id_eq] using
      M13.homothety_curvatureTensorNorm_eq _ _ (Diffeomorph.refl (𝓡 3) M ∞)
        H hH (R.metric_homothety u) (F.connection _) (R.flow.connection u) x
  have hradius : Real.sqrt H * (a / Real.sqrt H) = a := by
    field_simp [ne_of_gt (Real.sqrt_pos.mpr hH)]
  have hball : (G.metric 0).ball p a = (F.metric s).ball p (a / Real.sqrt H) := by
    have hb := M13.homothety_ball_image _ _ (Diffeomorph.refl (𝓡 3) M ∞)
      H hH (R.metric_homothety 0) p (a / Real.sqrt H)
    simpa only [Diffeomorph.coe_refl, Set.image_id', id_eq,
      parabolicTimeInv, zero_div, add_zero, hradius] using hb.symm
  have hcompactG : IsCompact (closure ((G.metric 0).ball p a)) := by
    rw [hball]
    exact hcompact
  have hcurvatureG : ∀ u ∈ Icc 0 T, ∀ x ∈ (G.metric 0).ball p a,
      (G.connection u).curvatureTensorNorm x ≤ K := by
    intro u hu x hx
    rw [hnorm]
    exact (div_le_iff₀ hH).2 (hcurvature _ (hclock u hu) x (hball ▸ hx))
  have hfloorG : ∀ u ∈ Icc 0 T, ∀ x ∈ (G.metric 0).ball p a,
      -1 ≤ (G.connection u).scalarCurvature x := by
    intro u hu x hx
    rw [hscalar]
    apply (le_div_iff₀ hH).2
    simpa only [neg_one_mul] using hfloor _ (hclock u hu) x (hball ▸ hx)
  have hinitialG : ∀ x ∈ (G.metric 0).ball p a,
      3 / 4 ≤ (G.connection 0).scalarCurvature x := by
    intro x hx
    rw [hscalar, show parabolicTimeInv H s 0 = s from by simp [parabolicTimeInv]]
    apply (le_div_iff₀ hH).2
    linarith [hinitial x (hball ▸ hx)]
  have hfinal := hpersist M T hT G p hcompactG hcurvatureG hfloorG hinitialG T
    ⟨hT.le, le_min le_rfl hshort⟩
  rw [hscalar] at hfinal
  have hend : parabolicTimeInv H s T = t := by
    dsimp only [T, parabolicTimeInv]
    field_simp
    ring
  rw [hend] at hfinal
  have := (le_div_iff₀ hH).1 hfinal
  linarith

end PoincareConjecture.M47
