import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.SlabBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Ancient









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators ENNReal

universe u

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M]

private theorem exists_smoothDistanceLike_of_compact [CompactSpace M]
    (g : RiemannianMetric n M) (D : LeviCivitaData g) (O : M) :
    Nonempty (SmoothDistanceLike g D O) := by
  obtain ⟨B, hB⟩ := (isCompact_univ.image (g.continuous_toReal_edist O)).bddAbove
  let C := max B 0 + 1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨⟨fun _ => C, contMDiff_const, C, hC, ?_, ?_, ?_, ?_⟩⟩
  · intro x
    have hx := hB (mem_image_of_mem _ (mem_univ x))
    dsimp only [C]
    linarith [le_max_left B 0]
  · intro x
    nlinarith [ENNReal.toReal_nonneg (a := g.edist O x)]
  · intro x v
    simpa only [mvfderiv_const, zero_apply, abs_zero, tangentNorm] using
      mul_nonneg hC (Real.sqrt_nonneg (g.inner x v v))
  · intro x v
    have hq : 0 ≤ g.inner x v v := by
      by_cases hv : v = 0
      · subst v; simp
      · exact (g.pos x v hv).le
    simpa only [LeviCivitaData.hessian, LeviCivitaData.hessianOnFields,
      mvfderiv_const, zero_apply, sub_zero] using mul_nonneg hC hq

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RicciFlow

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [PreconnectedSpace M] {J : Set ℝ}

private theorem exists_proper_smoothExhaustion_of_bounded_geometry
    (F : RicciFlow n M J) (O : M) (t₀ T K : ℝ) (ht₀ : t₀ ∈ J)
    (hT : ∀ t ∈ J, |t - t₀| ≤ T)
    (hcomplete : ∀ t ∈ J, MetricComplete (F.metric t))
    (hK : 0 ≤ K)
    (hRm : ∀ t ∈ J, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hRicDeriv : ∀ t ∈ J, ∀ x (u v w : TangentSpace (𝓡 n) x),
      |(F.connection t).covariantTensorDerivative (F.connection t).ricciEvaluation
        x ![u, v, w]| ≤ K * (F.metric t).tangentNorm x u *
          (F.metric t).tangentNorm x v * (F.metric t).tangentNorm x w) :
    ∃ S : SmoothExhaustion F O, ∀ r : ℝ, IsCompact {x | S.toFun x ≤ r} := by
  classical
  by_cases hc : CompactSpace M
  · let := hc
    obtain ⟨S₀⟩ := (F.metric t₀).exists_smoothDistanceLike_of_compact (F.connection t₀) O
    let S := F.smoothExhaustionOfInitialOfCurvatureBound O t₀ ht₀ S₀ K K T
      hK hK hT hRm hRicDeriv
    exact ⟨S, fun r => S.isCompact_sublevel_of_metricComplete ht₀ (hcomplete t₀ ht₀) r⟩
  · let : NoncompactSpace M := ⟨fun h => hc ⟨h⟩⟩
    obtain ⟨C, _, hS⟩ := F.exists_proper_smoothExhaustion_of_curvature_bound
      t₀ T K ht₀ hT hcomplete hK hRm hRicDeriv
    obtain ⟨S, _, hproper⟩ := hS O
    exact ⟨S, hproper⟩

end PoincareConjecture.RicciFlow

namespace Poincare.RicciFlow.Harnack

open PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
  [SecondCountableTopology M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem hamiltonBlockPos_on_bounded_slab
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁)) {a b K : ℝ}
    (hab : a < b) (hJ : Icc a b ⊆ Ioo T₀ T₁)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hbound : ∀ t ∈ Icc a b, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hcurv : ∀ t ∈ Icc a b, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x) :
    ∀ t ∈ Ioo a b, ∀ x, HamiltonBlockPos F t x (t - a) := by
  intro t ht x
  apply hamiltonBlockPos_of_time_origin_limit F t x ht.1
  intro c hc
  obtain ⟨d, had, hdc⟩ := exists_between hc.1
  have hdb : d < b := hdc.trans (hc.2.trans ht.2)
  have hsub : Ioo d b ⊆ Icc a b := fun s hs => ⟨had.le.trans hs.1.le, hs.2.le⟩
  have hmap : (fun s : ℝ => s + 0) '' Ioo d b ⊆ Ioo T₀ T₁ := by
    rintro _ ⟨s, hs, rfl⟩
    simpa only [add_zero] using hJ (hsub hs)
  have hne : (Ioo d b).Nontrivial := by
    obtain ⟨e, hde, heb⟩ := exists_between hdb
    obtain ⟨f, hef, hfb⟩ := exists_between heb
    exact ⟨e, ⟨hde, heb⟩, f, ⟨hde.trans hef, hfb⟩, hef.ne⟩
  let G := F.translate 0 hmap ordConnected_Ioo hne
  obtain ⟨D, hD, hderiv⟩ := F.exists_curvatureDerivativeNorm_two_bound_on_buffered_slab
    hC hab hJ (sub_pos.mpr had) (hcomplete a ⟨le_rfl, hab.le⟩) hbound
  have hd (s : ℝ) (hs : s ∈ Ioo d b) (y : M) (j : ℕ) (hj : j ≤ 2) :
      (G.connection s).curvatureDerivativeNorm j y ≤ D := by
    change (F.connection (s + 0)).curvatureDerivativeNorm j y ≤ D
    rw [add_zero]
    exact hderiv s ⟨by linarith [hs.1], hs.2.le⟩ y j hj
  let K' := max K ((n : ℝ) * D)
  have hK' : 0 ≤ K' := (mul_nonneg (Nat.cast_nonneg n) hD.le).trans (le_max_right _ _)
  have hRm (s : ℝ) (hs : s ∈ Ioo d b) (y : M) :
      (G.connection s).curvatureTensorNorm y ≤ K' := by
    change (F.connection (s + 0)).curvatureTensorNorm y ≤ K'
    rw [add_zero]
    exact (hbound s (hsub hs) y).trans (le_max_left K ((n : ℝ) * D))
  have hRicDeriv (s : ℝ) (hs : s ∈ Ioo d b) (y : M)
      (u v w : TangentSpace (𝓡 n) y) :
      |(G.connection s).covariantTensorDerivative (G.connection s).ricciEvaluation
        y ![u, v, w]| ≤ K' * (G.metric s).tangentNorm y u *
          (G.metric s).tangentNorm y v * (G.metric s).tangentNorm y w := by
    apply ((G.connection s).abs_covariantTensorDerivative_ricci_le_curvatureDerivativeNorm
      (hC.tensor_calculus n M (G.metric s) (G.connection s)) y u v w).trans
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact (mul_le_mul_of_nonneg_left (hd s hs y 1 (by norm_num))
      (Nat.cast_nonneg n)).trans (le_max_right _ _)
  have hcG : c ∈ Ioo d b := ⟨hdc, hc.2.trans ht.2⟩
  have hcompleteG : ∀ s ∈ Ioo d b, MetricComplete (G.metric s) := by
    intro s hs
    simpa only [G, RicciFlow.translate, add_zero] using hcomplete s (hsub hs)
  obtain ⟨S, hproper⟩ := G.exists_proper_smoothExhaustion_of_bounded_geometry
    x c (b - a) K' hcG (fun s hs => abs_le.mpr
      ⟨by linarith [hs.1, hc.2, ht.2], by linarith [hs.2, hc.1]⟩)
    hcompleteG hK' hRm hRicDeriv
  have hsmall : Ioc c t ⊆ Ioo d b := fun s hs =>
    ⟨hdc.trans hs.1, hs.2.trans_lt ht.2⟩
  have hpos := hamiltonBlockPos_of_smoothExhaustion_time_origin hC G x S hproper
    hc.2 hsmall hD.le (fun s hs y j hj => hd s (hsmall hs) y j hj)
    (fun s hs y => by
      change (F.connection (s + 0)).NonnegativeCurvatureOperator y
      rw [add_zero]
      exact hcurv s (hsub (hsmall hs)) y)
    t ⟨hc.2, le_rfl⟩ x
  simpa only [G, hamiltonBlockPos_translate, add_zero] using hpos



theorem scalar_harnack_on_bounded_slab
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁)) {a b K : ℝ}
    (hab : a < b) (hJ : Icc a b ⊆ Ioo T₀ T₁)
    (hcomplete : ∀ t ∈ Icc a b, MetricComplete (F.metric t))
    (hbound : ∀ t ∈ Icc a b, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (hcurv : ∀ t ∈ Icc a b, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x) :
    ∀ t ∈ Ioo a b, ∀ x,
      0 ≤ (F.connection t).laplacian (F.connection t).scalarCurvature x +
        2 * (F.connection t).ricciNormSq x +
        (F.connection t).scalarCurvature x / (t - a) := by
  intro t ht x
  exact scalar_harnack_nonneg_of_hamiltonBlockPos hC F (hJ ⟨ht.1.le, ht.2.le⟩) x (t - a)
    (hamiltonBlockPos_on_bounded_slab hC F hab hJ hcomplete hbound hcurv t ht x)



theorem hamiltonBlockPos_of_curvature_slab_bounds
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁))
    (hcomplete : ∀ t ∈ Ioo T₀ T₁, MetricComplete (F.metric t))
    (hcurv : ∀ t ∈ Ioo T₀ T₁, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hbound : ∀ a b : ℝ, a < b → Icc a b ⊆ Ioo T₀ T₁ →
      ∃ K : ℝ, ∀ s ∈ Icc a b, ∀ x, (F.connection s).curvatureTensorNorm x ≤ K) :
    ∀ t ∈ Ioo T₀ T₁, ∀ x, HamiltonBlockPos F t x (t - T₀) := by
  intro t ht x
  apply hamiltonBlockPos_of_time_origin_limit F t x ht.1
  intro a ha
  obtain ⟨b, htb, hbT⟩ := exists_between ht.2
  have hab : a < b := ha.2.trans htb
  have hJ : Icc a b ⊆ Ioo T₀ T₁ := fun s hs =>
    ⟨ha.1.trans_le hs.1, hs.2.trans_lt hbT⟩
  obtain ⟨K, hK⟩ := hbound a b hab hJ
  exact hamiltonBlockPos_on_bounded_slab hC F hab hJ
    (fun s hs => hcomplete s (hJ hs)) hK (fun s hs => hcurv s (hJ hs))
    t ⟨ha.2, htb⟩ x



theorem finite_differential_of_curvature_slab_bounds
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁))
    (hcomplete : ∀ t ∈ Ioo T₀ T₁, MetricComplete (F.metric t))
    (hcurv : ∀ t ∈ Ioo T₀ T₁, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hbound : ∀ a b : ℝ, a < b → Icc a b ⊆ Ioo T₀ T₁ →
      ∃ K : ℝ, ∀ s ∈ Icc a b, ∀ x, (F.connection s).curvatureTensorNorm x ≤ K) :
    ∀ t ∈ Ioo T₀ T₁, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s => (F.connection s).scalarCurvature x) dR
          (Ioo T₀ T₁) t ∧
        0 ≤ dR + (F.connection t).scalarCurvature x / (t - T₀) +
          2 * mvfderiv (𝓡 n) (fun y => (F.connection t).scalarCurvature y) x v +
          2 * (F.connection t).ricci x v v := by
  exact finite_differential_of_hamilton_block hC T₀ T₁ F
    (hamiltonBlockPos_of_curvature_slab_bounds hC F hcomplete hcurv hbound)



theorem finite_differential_of_bounded_curvature
    (hC : RicciFlowCurvatureTheory.{u}) {T₀ T₁ K : ℝ}
    (F : RicciFlow n M (Ioo T₀ T₁))
    (hcomplete : ∀ t ∈ Ioo T₀ T₁, MetricComplete (F.metric t))
    (hcurv : ∀ t ∈ Ioo T₀ T₁, ∀ x,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hbound : ∀ t ∈ Ioo T₀ T₁, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ t ∈ Ioo T₀ T₁, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s => (F.connection s).scalarCurvature x) dR
          (Ioo T₀ T₁) t ∧
        0 ≤ dR + (F.connection t).scalarCurvature x / (t - T₀) +
          2 * mvfderiv (𝓡 n) (fun y => (F.connection t).scalarCurvature y) x v +
          2 * (F.connection t).ricci x v v := by
  exact finite_differential_of_curvature_slab_bounds hC F hcomplete hcurv
    (fun _ _ _ hJ => ⟨K, fun s hs => hbound s (hJ hs)⟩)



theorem ancient_differential_of_bounded_curvature
    (hC : RicciFlowCurvatureTheory.{u}) {K : ℝ}
    (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hcurv : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K) :
    ∀ t ≤ 0, ∀ x : M, ∀ v : TangentSpace (𝓡 n) x,
      ∃ dR : ℝ,
        HasDerivWithinAt (fun s => (F.connection s).scalarCurvature x) dR (Iic 0) t ∧
        0 ≤ dR + 2 * mvfderiv (𝓡 n)
          (fun y => (F.connection t).scalarCurvature y) x v +
          2 * (F.connection t).ricci x v v := by
  intro t ht x v
  let d : ℝ → ℝ := fun s =>
    (F.connection s).laplacian (F.connection s).scalarCurvature x +
      2 * (F.connection s).ricciNormSq x
  let q : ℝ → ℝ := fun s => d s +
    2 * mvfderiv (𝓡 n) (fun y => (F.connection s).scalarCurvature y) x v +
    2 * (F.connection s).ricci x v v
  refine ⟨d t, hC.scalar_evolution n M (Iic 0) F t ht x, ?_⟩
  have hnegative : ∀ s < 0, 0 ≤ q s := by
    intro s hs
    apply Poincare.Asymptotics.nonneg_of_eventually_add_div_nonneg
      (R := (F.connection s).scalarCurvature x) (t := s)
    filter_upwards [eventually_lt_atBot s] with T hT
    have hT0 : T < 0 := hT.trans hs
    have hsub : Ioo T 0 ⊆ Iic (0 : ℝ) := fun _ h => h.2.le
    have hne : (Ioo T (0 : ℝ)).Nontrivial := by
      refine ⟨T / 2, ⟨by linarith, by linarith⟩, T / 3,
        ⟨by linarith, by linarith⟩, ?_⟩
      linarith
    let G := Poincare.Geometry.RicciFlow.Harnack.restrictFlow F hsub inferInstance hne
    obtain ⟨dR, hdR, hineq⟩ := finite_differential_of_bounded_curvature hC G
      (fun r hr => hcomplete r hr.2.le) (fun r hr => hcurv r hr.2.le)
      (fun r hr => hbound r hr.2.le) s ⟨hT, hs⟩ x v
    have hid : dR = d s :=
      (hdR.hasDerivAt (Ioo_mem_nhds hT hs)).unique
        ((hC.scalar_evolution n M (Iic 0) F s hs.le x).hasDerivAt (Iic_mem_nhds hs))
    change 0 ≤ dR + (F.connection s).scalarCurvature x / (s - T) +
      2 * mvfderiv (𝓡 n) (fun y => (F.connection s).scalarCurvature y) x v +
      2 * (F.connection s).ricci x v v at hineq
    dsimp only [q]
    linarith
  rcases lt_or_eq_of_le ht with hlt | rfl
  · exact hnegative t hlt
  · have hq : ContinuousOn q (Iic 0) :=
      ((Poincare.Geometry.RicciFlow.Harnack.scalarEvolution_continuousOn_ancient hC F x).add
        ((Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_mvfderiv_continuousOn_time
          hC (Iic 0) F x v).const_mul 2)).add
        ((Poincare.Geometry.RicciFlow.Harnack.ricci_continuousOn_ancient F x v v).const_mul 2)
    exact Poincare.Asymptotics.nonneg_at_zero_of_nonneg_neg (hq 0 self_mem_Iic) hnegative



theorem scalarCurvature_monotoneOn_of_bounded_ancient_curvature
    (hC : RicciFlowCurvatureTheory.{u}) {K : ℝ}
    (F : RicciFlow n M (Iic 0))
    (hcomplete : ∀ t ≤ 0, MetricComplete (F.metric t))
    (hcurv : ∀ t ≤ 0, ∀ x, (F.connection t).NonnegativeCurvatureOperator x)
    (hbound : ∀ t ≤ 0, ∀ x, (F.connection t).curvatureTensorNorm x ≤ K)
    (x : M) : MonotoneOn (fun t => (F.connection t).scalarCurvature x) (Iic 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Iic (0 : ℝ))
    (Poincare.Geometry.RicciFlow.Harnack.scalarCurvature_continuousOn_time hC (Iic 0) F x)
    (f' := fun t => (F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x)
  · intro t ht
    exact (hC.scalar_evolution n M (Iic 0) F t (interior_subset ht) x).mono interior_subset
  · intro t ht
    rw [interior_Iic] at ht
    change t < 0 at ht
    obtain ⟨dR, hdR, hineq⟩ := ancient_differential_of_bounded_curvature hC F
      hcomplete hcurv hbound t ht.le x 0
    have hid := (hdR.hasDerivAt (Iic_mem_nhds ht)).unique
      ((hC.scalar_evolution n M (Iic 0) F t ht.le x).hasDerivAt (Iic_mem_nhds ht))
    have hzero : (F.connection t).ricci x 0 0 = 0 := by
      have h := (F.connection t).abs_ricci_le_curvatureDerivativeNorm_zero
        (hC.tensor_calculus n M (F.metric t) (F.connection t)) x 0 0
      simpa [RiemannianMetric.tangentNorm] using h
    simpa only [map_zero, mul_zero, add_zero, hid, hzero] using hineq

end Poincare.RicciFlow.Harnack
