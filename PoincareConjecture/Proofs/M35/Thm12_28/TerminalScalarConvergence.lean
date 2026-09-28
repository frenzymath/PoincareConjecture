import PoincareConjecture.Proofs.M35.Thm12_28.TerminalMetricConvergence
import PoincareConjecture.Proofs.M35.Thm12_28.ScalarMetricJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.M13.OrdinaryFlow









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

private theorem exists_scaled_scalar_realization
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] (g : RiemannianMetric 3 M) (D : LeviCivitaData g)
    (Q : ℝ) (hQ : 0 < Q) (f : EuclideanSpace ℝ (Fin 3) → M)
    {U : Set (EuclideanSpace ℝ (Fin 3))} (hU : IsOpen U)
    {p : EuclideanSpace ℝ (Fin 3)} (hp : p ∈ U)
    (hf : ∀ z ∈ U, ContMDiffAt (𝓡 3) (𝓡 3) ∞ f z)
    (hi : ∀ z ∈ U, (mfderiv (𝓡 3) (𝓡 3) f z).IsInvertible) :
    ∃ (g' : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (D' : LeviCivitaData g'),
      (∀ᶠ z in 𝓝 p, g'.euclideanCoefficients z = Q • g.pullbackCoefficients f z) ∧
      D'.scalarCurvature p = D.scalarCurvature (f p) / Q := by
  let G : RiemannianMetric 3 M := M13.scaleSmoothMetric g Q hQ
  let DG := M13.scaleLeviCivitaData D Q hQ
  obtain ⟨g', D', V, hVo, hpV, _, hcoeff⟩ :=
    RiemannianMetric.exists_local_realization hU hp (G.pullbackCoefficients f)
      (fun z hz => (G.contDiffAt_pullbackCoefficients (hf z hz)).contDiffWithinAt)
      (fun z _ v w => G.symm (f z) _ _)
      (fun z hz v hv => by
        apply G.pos (f z)
        intro heq
        apply hv
        apply (hi z hz).injective
        exact heq.trans (map_zero (mfderiv (𝓡 3) (𝓡 3) f z)).symm)
  have hmetric : ∀ᶠ z in 𝓝 p, ∀ v w : EuclideanSpace ℝ (Fin 3),
      g'.inner z v w = G.inner (f z) (mfderiv (𝓡 3) (𝓡 3) f z v)
        (mfderiv (𝓡 3) (𝓡 3) f z w) := by
    filter_upwards [hVo.mem_nhds hpV] with z hz v w
    exact congrArg (fun B : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => B v w) (hcoeff z hz)
  refine ⟨g', D', ?_, ?_⟩
  · filter_upwards [hVo.mem_nhds hpV] with z hz
    exact hcoeff z hz
  · have hscalar := scalarCurvature_eq_pullback_euclidean D' DG (hf p hp)
      (Filter.mem_of_superset (hU.mem_nhds hp) (fun z hz => hi z hz)) hmetric
    have hscale := M13.homothety_scalarCurvature_eq g G
      (Diffeomorph.refl (𝓡 3) M ∞) Q hQ (M13.identity_metricHomothety g Q hQ) D DG (f p)
    exact hscalar.trans hscale

private theorem exists_cylinder_scalar_realization {J : Set ℝ}
    (F : RicciFlow 3 StandardCapSpace J)
    {C : GeneralizedSliceCarrier} {a Q : ℝ} {I : Set ℝ} {U : Set C.carrier}
    (e : GeneralizedFlowCylinder (generalizedFlow F) C a Q I U)
    (hU : IsOpen U) (hzero : (0 : ℝ) ∈ I) (htime : a + 0 / Q ∈ J)
    (q : C.carrier) {p : EuclideanSpace ℝ (Fin 3)}
    (hp : p ∈ (extChartAt (𝓡 3) q).target)
    (hpU : (extChartAt (𝓡 3) q).symm p ∈ U) :
    let f : C.carrier → StandardCapSpace := fun z => (e.forward 0 hzero z).val
    ∃ (g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (D : LeviCivitaData g),
      (∀ᶠ z in 𝓝 p, ∀ i j : Fin 3,
        g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin 3) ℝ i)
          (EuclideanSpace.basisFun (Fin 3) ℝ j) =
            fixedCylinderMetricCoefficient F C a Q f q i j (0, z)) ∧
      D.scalarCurvature p = (F.connection a).scalarCurvature
        (f ((extChartAt (𝓡 3) q).symm p)) / Q := by
  let c := extChartAt (𝓡 3) q
  let f : C.carrier → StandardCapSpace := fun z => (e.forward 0 hzero z).val
  let phi := cylinderSpatialCoordinates F e hU 0 hzero htime
  let V := c.target ∩ c.symm ⁻¹' U
  have hV : IsOpen V := (continuousOn_extChartAt_symm q).isOpen_inter_preimage
    (isOpen_extChartAt_target q) hU
  have hf (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ V) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ f (c.symm z) :=
    phi.contMDiffOn_toFun.contMDiffAt (hU.mem_nhds hz.2)
  have hc (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ V) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm z :=
    (contMDiffOn_extChartAt_symm (n := ∞) q).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 3) q).mem_nhds hz.1)
  have hi (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ V) :
      (mfderiv (𝓡 3) (𝓡 3) (f ∘ c.symm) z).IsInvertible := by
    have hfi : (mfderiv (𝓡 3) (𝓡 3) f (c.symm z)).IsInvertible :=
      let hlocal : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ f (c.symm z) :=
        ⟨phi, hz.2, fun _ _ => rfl⟩
      ⟨hlocal.mfderivToContinuousLinearEquiv (by simp), rfl⟩
    have hci : (mfderiv (𝓡 3) (𝓡 3) c.symm z).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm hz.1
    rw [mfderiv_comp z ((hf z hz).mdifferentiableAt (by simp))
      ((hc z hz).mdifferentiableAt (by simp))]
    exact hfi.comp hci
  obtain ⟨g, D, hcoeff, hscalar⟩ := exists_scaled_scalar_realization
    (F.metric a) (F.connection a) Q e.scale_pos (f ∘ c.symm) hV ⟨hp, hpU⟩
    (fun z hz => (hf z hz).comp z (hc z hz)) hi
  refine ⟨g, D, ?_, hscalar⟩
  filter_upwards [hcoeff, hV.mem_nhds ⟨hp, hpU⟩] with z hz hzV i j
  have heq := congrArg (fun B : EuclideanSpace ℝ (Fin 3) →L[ℝ]
    EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => B (EuclideanSpace.basisFun (Fin 3) ℝ i)
      (EuclideanSpace.basisFun (Fin 3) ℝ j)) hz
  have hfixed := fixedCylinderMetricCoefficient_eq_pullback F C a Q f q i j
    (0, z) hzV.1 (hf z hzV)
  simp only [zero_div, add_zero] at hfixed
  exact heq.trans hfixed.symm

private theorem exists_shifted_scalar_realization
    (g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (D : LeviCivitaData g)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ∃ gd : Σ g' : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)), LeviCivitaData g',
      gd.2.scalarCurvature 0 = D.scalarCurvature p ∧
      ∀ (r : ℕ) (a b : Fin 3),
        iteratedFDeriv ℝ r (fun z => gd.1.inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) 0 =
        iteratedFDeriv ℝ r (fun z => g.inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) p := by
  let f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := fun z => z + p
  have hd (z : EuclideanSpace ℝ (Fin 3)) :
      mfderiv (𝓡 3) (𝓡 3) f z = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [mfderiv_eq_fderiv]
    exact ((hasFDerivAt_id z).add_const p).fderiv
  obtain ⟨g', D', hcoeff, hscalar⟩ := exists_scaled_scalar_realization g D 1 zero_lt_one f
    isOpen_univ (mem_univ (0 : EuclideanSpace ℝ (Fin 3)))
    (fun z _ => (contDiffAt_id.add contDiffAt_const).contMDiffAt)
    (fun z _ => by rw [hd]; exact ⟨ContinuousLinearEquiv.refl ℝ _, rfl⟩)
  refine ⟨⟨g', D'⟩, ?_, ?_⟩
  · simpa only [f, zero_add, div_one] using hscalar
  · intro r a b
    have heq : (fun z => g'.inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 0]
        (fun z => g.inner (z + p) (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) := by
      filter_upwards [hcoeff] with z hz
      have he := congrArg (fun B : EuclideanSpace ℝ (Fin 3) →L[ℝ]
        EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => B (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) hz
      change g'.inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b) = 1 * g.inner (f z)
          (mfderiv (𝓡 3) (𝓡 3) f z (EuclideanSpace.basisFun (Fin 3) ℝ a))
          (mfderiv (𝓡 3) (𝓡 3) f z (EuclideanSpace.basisFun (Fin 3) ℝ b)) at he
      rw [one_mul] at he
      exact he.trans (congrArg₂ (fun v w : EuclideanSpace ℝ (Fin 3) => g.inner (z + p) v w)
        (congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) =>
          A (EuclideanSpace.basisFun (Fin 3) ℝ a)) (hd z))
        (congrArg (fun A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) =>
          A (EuclideanSpace.basisFun (Fin 3) ℝ b)) (hd z)))
    exact ((heq.iteratedFDeriv ℝ r).self_of_nhds).trans
      (by simpa only [zero_add] using (iteratedFDeriv_comp_add_right (𝕜 := ℝ)
        (f := fun z => g.inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) r p 0))

private theorem scalar_tendsto_of_moving_metric_jets
    {gseq : ℕ → RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    {g : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))}
    (Dseq : ∀ k, LeviCivitaData (gseq k)) (D : LeviCivitaData g)
    (pseq : ℕ → EuclideanSpace ℝ (Fin 3)) (p : EuclideanSpace ℝ (Fin 3))
    (hjet : ∀ r : ℕ, r ≤ 2 → ∀ a b : Fin 3,
      Tendsto (fun k => iteratedFDeriv ℝ r
        (fun z => (gseq k).inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) (pseq k)) atTop
        (𝓝 (iteratedFDeriv ℝ r (fun z => g.inner z
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) p))) :
    Tendsto (fun k => (Dseq k).scalarCurvature (pseq k)) atTop (𝓝 (D.scalarCurvature p)) := by
  choose gs hgs hjs using fun k => exists_shifted_scalar_realization (gseq k) (Dseq k) (pseq k)
  obtain ⟨gd, hgd, hjd⟩ := exists_shifted_scalar_realization g D p
  have h := scalarCurvature_tendsto_of_metric_jets (fun k => (gs k).2) gd.2 0
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (by
      intro r hr a b
      simp only [OrthonormalBasis.coe_toBasis, hjs, hjd]
      exact hjet r hr a b)
  simpa only [hgs, hgd] using h




theorem blowupSequence_terminal_scalar_tendsto (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) (y : L.limit.sliceCarrier.carrier) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    Tendsto (fun k => (E.flow.connection (t (L.subsequence k))).scalarCurvature
      (((L.embedding k).forward 0
        ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val) /
          (blowupSequence P E t x ht hR).scale (L.subsequence k))
      atTop (𝓝 ((L.limit.flow.connection 0).scalarCurvature y)) := by
  classical
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  let c := extChartAt (𝓡 3) (show L.limit.carrier.carrier from y)
  let p := c y
  have hp : p ∈ c.target := mem_extChartAt_target y
  have hcp : c.symm p = y := c.left_inv (mem_extChartAt_source y)
  have hc (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ c.target) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm z :=
    (contMDiffOn_extChartAt_symm (n := ∞)
      (show L.limit.carrier.carrier from y)).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3)
          (show L.limit.carrier.carrier from y)).mem_nhds hz)
  obtain ⟨g, D, hcoeff, hscalar⟩ := exists_scaled_scalar_realization
    (L.limit.flow.metric 0) (L.limit.flow.connection 0) 1 zero_lt_one c.symm
    (isOpen_extChartAt_target y) hp hc (fun z hz => by
      have hi := isInvertible_mfderivWithin_extChartAt_symm
        (x := (show L.limit.carrier.carrier from y)) hz
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using hi)
  have hcover : y ∈ ⋃ j, L.exhaustion.space j :=
    (congrArg (fun U : Set L.limit.sliceCarrier.carrier => y ∈ U)
      L.exhaustion.space_covers).mpr (mem_univ y)
  obtain ⟨j, hyj⟩ := mem_iUnion.mp hcover
  let B (k : ℕ) (a b : Fin 3) (z : EuclideanSpace ℝ (Fin 3)) :=
    fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
      (t (L.subsequence k)) ((blowupSequence P E t x ht hR).scale (L.subsequence k))
      (fun w => ((L.embedding k).forward 0
        ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ w).val) y a b (0, z)
  let H (a b : Fin 3) (z : EuclideanSpace ℝ (Fin 3)) :=
    FlowCarrier.coordinateCoefficient L.limit.carrier y
      (fun s w v u => (L.limit.flow.metric s).inner w v u) a b (0, z)
  have hreal : ∀ᶠ k : ℕ in atTop,
      ∃ gd : Σ g' : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)), LeviCivitaData g',
        (∀ᶠ z in 𝓝 p, ∀ a b : Fin 3,
          gd.1.euclideanCoefficients z (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b) = B k a b z) ∧
        gd.2.scalarCurvature p = (E.flow.connection (t (L.subsequence k))).scalarCurvature
          (((L.embedding k).forward 0
            ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ y).val) /
              (blowupSequence P E t x ht hR).scale (L.subsequence k) := by
    filter_upwards [eventually_ge_atTop j] with k hk
    have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time k) 0 :=
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩
    obtain ⟨gk, Dk, hco, hsc⟩ := exists_cylinder_scalar_realization E.flow.base.flow
      (L.embedding k) (L.exhaustion.space_open k) hzero
      ((L.embedding k).forward 0 hzero L.limit.base).property y hp
      (hcp.symm ▸ L.exhaustion.space_increasing hk hyj)
    refine ⟨⟨gk, Dk⟩, hco, ?_⟩
    exact hsc.trans (congrArg (fun z : L.limit.sliceCarrier.carrier =>
      (E.flow.connection (t (L.subsequence k))).scalarCurvature
        (((L.embedding k).forward 0 hzero z).val) /
          (blowupSequence P E t x ht hR).scale (L.subsequence k)) hcp)
  obtain ⟨gd, hgd⟩ := hreal.choice
  have hlimcoeff (a b : Fin 3) :
      (fun z => g.inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 p] H a b := by
    filter_upwards [hcoeff] with z hz
    have heq := congrArg (fun B : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => B (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) hz
    change g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin 3) ℝ a)
      (EuclideanSpace.basisFun (Fin 3) ℝ b) =
        (L.limit.flow.metric 0).pullbackCoefficients c.symm z
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)
    simpa only [one_smul] using heq
  have hsc := scalarCurvature_tendsto_of_metric_jets (fun k => (gd k).2) D p
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis (by
      intro r _ a b
      simp only [OrthonormalBasis.coe_toBasis]
      rw [(hlimcoeff a b).iteratedFDeriv ℝ r |>.self_of_nhds]
      have hjet : Tendsto (fun k => iteratedFDeriv ℝ r (B k a b) p) atTop
          (𝓝 (iteratedFDeriv ℝ r (H a b) p)) := by
        apply Metric.tendsto_atTop.mpr
        intro eta heta
        obtain ⟨N, _, hN⟩ := blowupSequence_terminal_spatial_CInfinity P E t x ht hR L y
          j r {p} isCompact_singleton (fun z hz => by
            have hzp : z = p := hz
            subst z
            exact ⟨hp, hcp.symm ▸ hyj⟩) eta heta
        exact ⟨N, fun k hk => by
          simpa only [dist_eq_norm] using hN k hk a b p (mem_singleton p)⟩
      apply hjet.congr'
      filter_upwards [hgd] with k hk
      have heq : (fun z => (gd k).1.inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
          (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 p] B k a b :=
        hk.1.mono (fun z hz => hz a b)
      exact ((heq.iteratedFDeriv ℝ r).self_of_nhds).symm)
  have hscalar' : D.scalarCurvature p = (L.limit.flow.connection 0).scalarCurvature y := by
    simpa only [div_one, hcp] using hscalar
  rw [hscalar'] at hsc
  exact hsc.congr' (hgd.mono (fun _ hk => hk.2))




theorem blowupSequence_terminal_scalar_tendsto_chart (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (q : L.limit.sliceCarrier.carrier) (j : ℕ)
    (K : Set (EuclideanSpace ℝ (Fin 3))) (hK : IsCompact K)
    (hKU : K ⊆ {p | p ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm p ∈ L.exhaustion.space j})
    (sigma : ℕ → ℕ) (hsigma : Tendsto sigma atTop atTop)
    (pseq : ℕ → EuclideanSpace ℝ (Fin 3)) (hpseq : ∀ k, pseq k ∈ K)
    (p : EuclideanSpace ℝ (Fin 3)) (hp : p ∈ K) (hplim : Tendsto pseq atTop (𝓝 p)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
      L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    Tendsto (fun k => (E.flow.connection (t (L.subsequence (sigma k)))).scalarCurvature
      (((L.embedding (sigma k)).forward 0
        ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩
          ((extChartAt (𝓡 3) q).symm (pseq k))).val) /
            (blowupSequence P E t x ht hR).scale (L.subsequence (sigma k)))
      atTop (𝓝 ((L.limit.flow.connection 0).scalarCurvature
        ((extChartAt (𝓡 3) q).symm p))) := by
  classical
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.limit.carrier.carrier :=
    L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  let c := extChartAt (𝓡 3) (show L.limit.carrier.carrier from q)
  have hc (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ c.target) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm z :=
    (contMDiffOn_extChartAt_symm (n := ∞)
      (show L.limit.carrier.carrier from q)).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3)
          (show L.limit.carrier.carrier from q)).mem_nhds hz)
  have hpchart : p ∈ c.target := (hKU hp).1
  have hci (z : EuclideanSpace ℝ (Fin 3)) (hz : z ∈ c.target) :
      (mfderiv (𝓡 3) (𝓡 3) c.symm z).IsInvertible := by
      have hi := isInvertible_mfderivWithin_extChartAt_symm
        (I := 𝓡 3) (x := (show L.limit.carrier.carrier from q)) hz
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using hi
  obtain ⟨g, D, hcoeff, hscalar⟩ := exists_scaled_scalar_realization
    (L.limit.flow.metric 0) (L.limit.flow.connection 0) 1 zero_lt_one c.symm
    (isOpen_extChartAt_target (show L.limit.carrier.carrier from q)) hpchart hc hci
  let B (k : ℕ) (a b : Fin 3) (z : EuclideanSpace ℝ (Fin 3)) :=
    fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
      (t (L.subsequence k)) ((blowupSequence P E t x ht hR).scale (L.subsequence k))
      (fun w => ((L.embedding k).forward 0
        ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ w).val) q a b (0, z)
  let H (a b : Fin 3) (z : EuclideanSpace ℝ (Fin 3)) :=
    (L.limit.flow.metric 0).pullbackCoefficients c.symm z
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)
  have hreal : ∀ᶠ k : ℕ in atTop,
      ∃ gd : Σ g' : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)), LeviCivitaData g',
        (∀ᶠ z in 𝓝 (pseq k), ∀ a b : Fin 3,
          gd.1.euclideanCoefficients z (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b) = B (sigma k) a b z) ∧
        gd.2.scalarCurvature (pseq k) =
          (E.flow.connection (t (L.subsequence (sigma k)))).scalarCurvature
            (((L.embedding (sigma k)).forward 0
              ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩
                (c.symm (pseq k))).val) /
                  (blowupSequence P E t x ht hR).scale (L.subsequence (sigma k)) := by
    filter_upwards [hsigma.eventually (eventually_ge_atTop j)] with k hk
    have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time (sigma k)) 0 :=
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩
    obtain ⟨gk, Dk, hco, hsc⟩ := exists_cylinder_scalar_realization E.flow.base.flow
      (L.embedding (sigma k)) (L.exhaustion.space_open (sigma k)) hzero
      ((L.embedding (sigma k)).forward 0 hzero L.limit.base).property q (hKU (hpseq k)).1
      (L.exhaustion.space_increasing hk (hKU (hpseq k)).2)
    exact ⟨⟨gk, Dk⟩, hco, hsc⟩
  obtain ⟨gd, hgd⟩ := hreal.choice
  have hlimcoeff (a b : Fin 3) :
      (fun z => g.inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 p] H a b := by
    filter_upwards [hcoeff] with z hz
    have heq := congrArg (fun B : EuclideanSpace ℝ (Fin 3) →L[ℝ]
      EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ => B (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) hz
    change g.euclideanCoefficients z (EuclideanSpace.basisFun (Fin 3) ℝ a)
      (EuclideanSpace.basisFun (Fin 3) ℝ b) =
        (L.limit.flow.metric 0).pullbackCoefficients c.symm z
          (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)
    simpa only [one_smul] using heq
  have hsc := scalar_tendsto_of_moving_metric_jets (fun k => (gd k).2) D pseq p (by
    intro r _ a b
    rw [(hlimcoeff a b).iteratedFDeriv ℝ r |>.self_of_nhds]
    have herr : Tendsto (fun k => iteratedFDeriv ℝ r (B (sigma k) a b) (pseq k) -
        iteratedFDeriv ℝ r (H a b) (pseq k)) atTop (𝓝 0) := by
      apply Metric.tendsto_nhds.mpr
      intro eta heta
      obtain ⟨N, _, hN⟩ := blowupSequence_terminal_spatial_CInfinity P E t x ht hR L q
        j r K hK hKU eta heta
      filter_upwards [hsigma.eventually (eventually_ge_atTop N)] with k hk
      have hnk := hN (sigma k) hk a b (pseq k) (hpseq k)
      change ‖iteratedFDeriv ℝ r (B (sigma k) a b) (pseq k) -
        iteratedFDeriv ℝ r (H a b) (pseq k)‖ < eta at hnk
      simpa only [dist_zero_right] using hnk
    have hmetric := ((L.limit.flow.metric 0).contDiffOn_chartCoefficients
      (show L.limit.carrier.carrier from q)).contDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3)
          (show L.limit.carrier.carrier from q)).mem_nhds (hKU hp).1)
    have hfirst := hmetric.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a))
    have hsecond : ContDiffAt ℝ ∞ (H a b) p := hfirst.clm_apply
      (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ b))
    have hr : (r : ℕ∞ω) ≤ ∞ := by exact_mod_cast le_top (a := (r : ℕ∞))
    have hmodel := (hsecond.continuousAt_iteratedFDeriv hr).tendsto.comp hplim
    have hjet : Tendsto (fun k => iteratedFDeriv ℝ r (B (sigma k) a b) (pseq k)) atTop
        (𝓝 (iteratedFDeriv ℝ r (H a b) p)) := by
      simpa only [Function.comp_apply, sub_add_cancel, zero_add] using herr.add hmodel
    apply hjet.congr'
    filter_upwards [hgd] with k hk
    have heq : (fun z => (gd k).1.inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 (pseq k)] B (sigma k) a b :=
      hk.1.mono (fun z hz => hz a b)
    exact ((heq.iteratedFDeriv ℝ r).self_of_nhds).symm)
  have hscalar' : D.scalarCurvature p =
      (L.limit.flow.connection 0).scalarCurvature (c.symm p) := by
    simpa only [div_one] using hscalar
  rw [hscalar'] at hsc
  exact hsc.congr' (hgd.mono (fun _ hk => hk.2))

end PoincareConjecture.M35.OrdinaryRealization
