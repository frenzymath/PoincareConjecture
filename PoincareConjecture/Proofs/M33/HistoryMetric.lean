import PoincareConjecture.Definitions.M33RegularHistory

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

private theorem history_length_formula {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (γ : ℝ → M) :
    g.pathELength γ 0 1 = ∫⁻ s in Icc (0 : ℝ) 1,
      ENNReal.ofReal (g.tangentNorm (γ s)
        (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc 0 1) s 1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength (𝓡 n) γ 0 1 = _
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro s _
  dsimp only
  rw [← ofReal_norm, norm_eq_sqrt_real_inner]
  rfl

private theorem history_edist_le_length {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b)) (hab : a ≤ b) :
    g.edist (γ a) (γ b) ≤ g.pathELength γ a b := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab

variable {G : GeneralizedRicciFlowData.{u}} {F : SurgeryFlowData.{u}}
  (H : M33RegularHistoryRealization G F) (t : ℝ) (ht : t ∈ G.interval)

theorem M33RegularHistoryRealization.pathELength_forward
    (γ : ℝ → (G.slice t).carrier)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc 0 1)) :
    (F.metric t).pathELength (H.forward t ht ∘ γ) 0 1 =
      (G.metric t).pathELength γ 0 1 := by
  rw [history_length_formula, history_length_formula]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro s hs
  dsimp only
  have hderiv := mfderiv_comp_mfderivWithin s
    ((H.forward_smooth t ht).mdifferentiable (by simp) (γ s))
    (hγ.mdifferentiableOn one_ne_zero s hs)
    ((uniqueDiffOn_Icc zero_lt_one).uniqueMDiffOn s hs)
  rw [hderiv]
  congr 1
  exact congrArg Real.sqrt (H.metric_pullback t ht (γ s) _ _)

theorem M33RegularHistoryRealization.edist_forward_le
    (x y : (G.slice t).carrier) :
    (F.metric t).edist (H.forward t ht x) (H.forward t ht y) ≤
      (G.metric t).edist x y := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro L hL
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (G.slice t).carrier → Type _) :=
    ⟨(G.metric t).toRiemannianMetric⟩
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hL
  have hcomp : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 (H.forward t ht ∘ γ) (Icc 0 1) :=
    (H.forward_smooth t ht).of_le (by simp) |>.comp_contMDiffOn hγ
  have h := history_edist_le_length (F.metric t) hcomp zero_le_one
  rw [H.pathELength_forward t ht γ hγ] at h
  simpa only [Function.comp_apply, h0, h1] using h.trans hlen.le

theorem M33RegularHistoryRealization.ball_image_subset
    (x : (G.slice t).carrier) (r : ℝ) :
    H.forward t ht '' (G.metric t).ball x r ⊆
      (F.metric t).ball (H.forward t ht x) r := by
  rintro _ ⟨y, hy, rfl⟩
  exact (H.edist_forward_le t ht x y).trans_lt hy

theorem M33RegularHistoryRealization.ball_image_of_subset
    (x : (G.slice t).carrier) (r : ℝ)
    (hball : (F.metric t).ball (H.forward t ht x) r ⊆ Set.range (H.forward t ht)) :
    H.forward t ht '' (G.metric t).ball x r =
      (F.metric t).ball (H.forward t ht x) r := by
  apply Set.Subset.antisymm (H.ball_image_subset t ht x r)
  intro y hy
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice t).carrier → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := Manifold.exists_lt_of_riemannianEDist_lt hy
  have hretain : MapsTo γ (Icc (0 : ℝ) 1) (Set.range (H.forward t ht)) := by
    intro s hs
    apply hball
    have hd := history_edist_le_length (F.metric t)
      (hγ.mono (Icc_subset_Icc le_rfl hs.2)) hs.1
    have hmono : (F.metric t).pathELength γ 0 s ≤ (F.metric t).pathELength γ 0 1 :=
      Manifold.pathELength_mono le_rfl hs.2
    simpa only [RiemannianMetric.ball, mem_ofPred_eq, h0] using
      hd.trans_lt (hmono.trans_lt hlen)
  let β := H.inverse t ht ∘ γ
  have hβ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 β (Icc 0 1) :=
    ((H.inverse_smooth t ht).of_le (by simp)).comp hγ hretain
  have hlength : (G.metric t).pathELength β 0 1 = (F.metric t).pathELength γ 0 1 := by
    rw [← H.pathELength_forward t ht β hβ]
    exact Manifold.pathELength_congr (fun s hs => H.right_inverse t ht (hretain hs))
  refine ⟨H.inverse t ht y, ?_, H.right_inverse t ht (hball hy)⟩
  have hd := history_edist_le_length (G.metric t) hβ zero_le_one
  rw [hlength] at hd
  simpa only [RiemannianMetric.ball, mem_ofPred_eq, β, Function.comp_apply,
    h0, h1, H.left_inverse t ht x] using
    hd.trans_lt hlen

theorem M33RegularHistoryData.ball_volume_of_subset
    {W : M33RegularHistoryWindow F} (D : M33RegularHistoryData W)
    (t : ℝ) (ht : t ∈ D.generalized.interval) (x : (D.generalized.slice t).carrier) (r : ℝ)
    (hball : (F.metric t).ball (D.history.forward t ht x) r ⊆ m33RegularRegion F t) :
    calibratedMetricVolume (D.generalized.metric t) ((D.generalized.metric t).ball x r) =
      calibratedMetricVolume (F.metric t) ((F.metric t).ball (D.history.forward t ht x) r) := by
  rw [← D.volume_image t ht, D.history.ball_image_of_subset t ht x r]
  simpa only [D.regular_range] using hball

end PoincareConjecture
