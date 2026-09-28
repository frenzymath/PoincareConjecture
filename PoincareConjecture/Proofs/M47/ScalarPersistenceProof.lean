import PoincareConjecture.Statements.M47ScalarPersistence
import PoincareConjecture.Proofs.M04.ShiGeometricCutoff
import PoincareConjecture.Proofs.M04.ShiBallRetention
import PoincareConjecture.Proofs.M04.LocalScalarBarrier
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Scaling











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology
open Set Filter

universe u

namespace PoincareConjecture.M47

set_option maxHeartbeats 1600000 in

set_option backward.isDefEq.respectTransparency false in
private theorem scalar_cutoff_comparison
    (P : M47ScalarPersistencePredecessors.{u})
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {T L G : ℝ} (hT : 0 < T) (hL : 0 ≤ L)
    (F : RicciFlow 3 M (Icc 0 T)) {C : Set M} (hC : IsCompact C)
    (eta : ℝ → M → ℝ)
    (heta : ContinuousOn (Function.uncurry eta) (Icc 0 T ×ˢ C))
    (heta1 : ∀ t ∈ Icc 0 T, ∀ x ∈ C, eta t x ≤ 1)
    (hboundary : ∀ t ∈ Icc 0 T, ∀ x ∈ C \ interior C, eta t x = 0)
    (hsupport : M04.shiPhysicalCutoffSupports F.metric F.connection T C eta L G)
    (hlower : ∀ t ∈ Icc 0 T, ∀ x ∈ C, -1 ≤ (F.connection t).scalarCurvature x)
    (hinitial : ∀ x ∈ C, 3 / 4 ≤ (F.connection 0).scalarCurvature x) :
    ∀ t ∈ Icc 0 T, ∀ x ∈ C,
      7 / 4 * eta t x - 1 - 7 / 4 * L * t ≤
        (F.connection t).scalarCurvature x := by
  let f : ℝ → M → ℝ := fun t x =>
    (F.connection t).scalarCurvature x + 1 - 7 / 4 * eta t x + 7 / 4 * L * t
  have hR := P.scalar_regular M (Icc 0 T) F
  have hRspace (t : ℝ) (ht : t ∈ Icc 0 T) :
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (F.connection t).scalarCurvature := by
    have hslice : ContMDiff (𝓡 3) (𝓘(ℝ, ℝ).prod (𝓡 3)) ∞
        (fun x : M => (t, x)) := contMDiff_const.prodMk contMDiff_id
    exact ContMDiffOn.comp_contMDiff (I := 𝓡 3) (I' := 𝓘(ℝ, ℝ).prod (𝓡 3))
      (I'' := 𝓘(ℝ, ℝ)) (f := fun x : M => (t, x))
      (g := fun z : ℝ × M => (F.connection z.1).scalarCurvature z.2)
      hR hslice (fun x => ⟨ht, mem_univ x⟩)
  have hf : ContinuousOn (Function.uncurry f) (Icc 0 T ×ˢ C) := by
    exact (((hR.continuousOn.mono (prod_mono Subset.rfl (subset_univ C))).add
      continuousOn_const).sub (continuousOn_const.mul heta)).add
        (continuous_const.mul continuous_fst).continuousOn
  have hinit : ∀ x ∈ C, 0 ≤ f 0 x := by
    intro x hx
    have hR0 := hinitial x hx
    have he := heta1 0 ⟨le_rfl, hT.le⟩ x hx
    dsimp only [f]
    nlinarith
  have hbnd : ∀ t ∈ Icc 0 T, ∀ x ∈ C \ interior C, 0 ≤ f t x := by
    intro t ht x hx
    have hR0 := hlower t ht x hx.1
    have hLt := mul_nonneg hL ht.1
    dsimp only [f]
    rw [hboundary t ht x hx]
    nlinarith
  have hs : ∀ t ∈ Ioc 0 T, ∀ x ∈ interior C,
      (∀ y ∈ C, f t x ≤ f t y) → f t x < 0 →
      ∀ delta > 0, ∃ psi : ℝ → ℝ, ∃ v : ℝ,
        psi t = f t x ∧
        (∀ᶠ s in 𝓝[Icc 0 t] t, f s x ≤ psi s) ∧
        HasDerivWithinAt psi v (Icc 0 t) t ∧ -0 * f t x - delta ≤ v := by
    intro t ht x hx hmin hneg delta hdelta
    have htT : t ∈ Icc 0 T := ⟨ht.1.le, ht.2⟩
    have hxC : x ∈ C := interior_subset hx
    have hepos : 0 < eta t x := by
      have hR0 := hlower t htT x hxC
      have hLt := mul_nonneg hL ht.1.le
      dsimp only [f] at hneg
      nlinarith
    obtain ⟨e, ed, U, hU, hxU, he, heq, heSpace, heTime, hed, _, heHeat⟩ :=
      hsupport t ht x hx hepos (delta / (7 / 4)) (by positivity)
    have hlocal : IsLocalMin
        (fun y => (F.connection t).scalarCurvature y - 7 / 4 * e t y) x := by
      filter_upwards [heSpace, isOpen_interior.mem_nhds hx] with y hey hy
      have hxy := hmin y (interior_subset hy)
      dsimp only [f] at hxy
      rw [heq]
      linarith
    have hsmooth : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
        (fun y => (F.connection t).scalarCurvature y - 7 / 4 * e t y) x :=
      (hRspace t htT x).sub (contMDiffAt_const.mul
        (he.contMDiffAt (hU.mem_nhds hxU)))
    have hLap := (F.connection t).laplacian_nonneg_of_isLocalMin hsmooth hlocal
    have heScaled : ContMDiffOn (𝓡 3) 𝓘(ℝ, ℝ) ∞
        (fun y => (7 / 4 : ℝ) * e t y) U := contMDiffOn_const.mul he
    rw [M04.laplacian_sub_of_contMDiffOn (F.connection t) hU
      (hRspace t htT).contMDiffOn heScaled hxU,
      (F.connection t).laplacian_const_mul] at hLap
    let v := (F.connection t).laplacian (F.connection t).scalarCurvature x +
      2 * (F.connection t).ricciNormSq x - 7 / 4 * ed + 7 / 4 * L
    let psi : ℝ → ℝ := fun s =>
      (F.connection s).scalarCurvature x + 1 - 7 / 4 * e s x + 7 / 4 * L * s
    refine ⟨psi, v, ?_, ?_, ?_, ?_⟩
    · dsimp only [psi, f]
      rw [heq]
    · filter_upwards [heTime] with s hes
      dsimp only [f, psi]
      linarith
    · have hRd := (P.scalar_evolution M (Icc 0 T) F t htT x).mono
        (show Icc 0 t ⊆ Icc 0 T from fun s hs => ⟨hs.1, hs.2.trans ht.2⟩)
      have htd : HasDerivWithinAt (fun s : ℝ => 7 / 4 * L * s)
          (7 / 4 * L) (Icc 0 t) t := by
        simpa only [id_eq, mul_one] using
          (((hasDerivAt_id t).const_mul (7 / 4 * L)).hasDerivWithinAt)
      exact ((hRd.add_const 1).sub (hed.const_mul (7 / 4))).add htd
    · have hRic : 0 ≤ (F.connection t).ricciNormSq x :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      dsimp only [v]
      norm_num only [neg_zero, zero_mul, zero_sub]
      linarith
  have hresult := M04.compact_subset_min_velocity_nonnegative_of_upper_support
    hC hT f hinit hbnd hf hs
  intro t ht x hx
  have h := hresult t ht x hx
  dsimp only [f] at h
  linarith




theorem localScalarPersistence (P : M47ScalarPersistencePredecessors.{u}) :
    M47LocalScalarPersistenceStatement.{u} := by
  intro K a hK ha
  obtain ⟨L, G, hL, _, hcutoff⟩ := M04.exists_shi_geometric_cutoff 3 K 1 a hK ha
  let tau : ℝ := min 1 (min (1 / K) (1 / (4 * (L + 1))))
  have htau : 0 < tau := by
    dsimp only [tau]
    exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  refine ⟨tau, htau, min_le_left _ _, ?_⟩
  intro M _ _ _ _ _ T hT F p hcompact hRm hlower hinitial
  let S : ℝ := min T tau
  have hS : 0 < S := lt_min hT htau
  have hST : S ≤ T := min_le_left _ _
  have hSK : S ≤ 1 / K :=
    (min_le_right T tau).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hSJ : Icc 0 S ⊆ Icc 0 T := fun _ hs => ⟨hs.1, hs.2.trans hST⟩
  let F' : RicciFlow 3 M (Icc 0 S) := {
    metric := F.metric
    connection := F.connection
    interval := ordConnected_Icc
    nontrivial := ⟨0, ⟨le_rfl, hS.le⟩, S, ⟨hS.le, le_rfl⟩, ne_of_lt hS⟩
    smooth := F.smooth.mono (prod_mono hSJ Subset.rfl)
    equation t ht x v w := (F.equation t (hSJ ht) x v w).mono hSJ
  }
  have hRm' : ∀ t ∈ Icc 0 S, ∀ x ∈ (F'.metric 0).ball p a,
      (F'.connection t).curvatureTensorNorm x ≤ K :=
    fun t ht x hx => hRm t (hSJ ht) x hx
  have hpball : p ∈ (F'.metric 0).ball p (a / 2) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
      ⟨(F'.metric 0).toRiemannianMetric⟩
    change Manifold.riemannianEDist (𝓡 3) p p < ENNReal.ofReal (a / 2)
    rw [Manifold.riemannianEDist_self]
    exact ENNReal.ofReal_pos.mpr (half_pos ha)
  obtain ⟨Rc, _, _, hC, hCball, hflow⟩ :=
    M04.exists_compact_carrier_for_flow_balls F' hK ha hS.le hSK p
      hcompact hRm' p hpball
  let C : Set M := {x | (F'.metric 0).edist p x ≤ ENNReal.ofReal Rc}
  have hCouter : C ⊆ (F'.metric 0).ball p a := by
    intro x hx
    exact (hCball hx).trans_le (ENNReal.ofReal_le_ofReal (by linarith : 3 * a / 4 ≤ a))
  have hretain : ∀ t ∈ Icc 0 S,
      closure ((F'.metric t).ball p (M04.shiRetainedFlowRadius 3 1 a)) ⊆ C :=
    hflow
  obtain ⟨hpC, eta, heta, _, heta1, hboundary, hcenter, hsupport⟩ :=
    hcutoff M S hS.le hSK F' p C hC hretain
      (fun t ht x hx => hRm' t ht x (hCouter hx))
  have hcompare := scalar_cutoff_comparison P hS hL F' hC eta heta heta1
    hboundary hsupport
    (fun t ht x hx => hlower t (hSJ ht) x (hCouter hx))
    (fun x hx => hinitial x (hCouter hx))
  intro t ht
  have htS : t ∈ Icc 0 S := ht
  have hbound := hcompare t htS p hpC
  rw [hcenter t htS] at hbound
  have htlimit : t ≤ 1 / (4 * (L + 1)) :=
    ht.2.trans ((min_le_right T tau).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  have hden : 0 < 4 * (L + 1) := by positivity
  have htime := (le_div_iff₀ hden).mp htlimit
  change 7 / 4 * 1 - 1 - 7 / 4 * L * t ≤ (F.connection t).scalarCurvature p at hbound
  nlinarith [ht.1]

end PoincareConjecture.M47
