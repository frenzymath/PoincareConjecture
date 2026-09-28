import PoincareConjecture.Proofs.M35.Thm12_28.CylinderScalarOperators
import PoincareConjecture.Proofs.M09.HessianTrace

set_option autoImplicit false
set_option maxSynthPendingDepth 5

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "V" => EuclideanSpace ℝ (Fin 3)

theorem blowupSequence_terminal_scalar_operators_tendsto_chart (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤))
    (q : L.limit.sliceCarrier.carrier) (j : ℕ)
    (K : Set V) (hK : IsCompact K)
    (hKU : K ⊆ {p | p ∈ (extChartAt (𝓡 3) q).target ∧
      (extChartAt (𝓡 3) q).symm p ∈ L.exhaustion.space j})
    (sigma : ℕ → ℕ) (hsigma : Tendsto sigma atTop atTop)
    (pseq : ℕ → V) (hpseq : ∀ k, pseq k ∈ K)
    (p : V) (hp : p ∈ K) (hplim : Tendsto pseq atTop (𝓝 p)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence (sigma k))
    let y k := ((L.embedding (sigma k)).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩
        ((extChartAt (𝓡 3) q).symm (pseq k))).val
    let z := (extChartAt (𝓡 3) q).symm p
    Tendsto (fun k => scalarGradientNorm (E.flow.metric (t (L.subsequence (sigma k))))
      (E.flow.connection (t (L.subsequence (sigma k)))) (y k) / (Q k * Real.sqrt (Q k)))
      atTop (𝓝 (scalarGradientNorm (L.limit.flow.metric 0) (L.limit.flow.connection 0) z)) ∧
    Tendsto (fun k => ((E.flow.connection (t (L.subsequence (sigma k)))).laplacian
      (E.flow.connection (t (L.subsequence (sigma k)))).scalarCurvature (y k) +
        2 * (E.flow.connection (t (L.subsequence (sigma k)))).ricciNormSq (y k)) / Q k ^ 2)
      atTop (𝓝 ((L.limit.flow.connection 0).laplacian
        (L.limit.flow.connection 0).scalarCurvature z +
          2 * (L.limit.flow.connection 0).ricciNormSq z)) := by
  classical
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace V L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  have : T2Space L.limit.carrier.carrier := L.limit.carrier.t2Space
  let c := extChartAt (𝓡 3) (show L.limit.carrier.carrier from q)
  have hc (z : V) (hz : z ∈ c.target) : ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm z :=
    (contMDiffOn_extChartAt_symm (n := ∞)
      (show L.limit.carrier.carrier from q)).contMDiffAt
        ((isOpen_extChartAt_target (I := 𝓡 3)
          (show L.limit.carrier.carrier from q)).mem_nhds hz)
  have hci (z : V) (hz : z ∈ c.target) :
      (mfderiv (𝓡 3) (𝓡 3) c.symm z).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm
        (I := 𝓡 3) (x := (show L.limit.carrier.carrier from q)) hz
  obtain ⟨g, D, hcoeff, _, hgradient, hevolution⟩ := exists_local_scalar_operator_realization
    (L.limit.flow.metric 0) (L.limit.flow.connection 0) c.symm
    (isOpen_extChartAt_target (show L.limit.carrier.carrier from q)) (hKU hp).1 hc hci
    (Proofs.M09.scalarCurvature_contMDiff P.curvature (L.limit.flow.connection 0) (c.symm p))
  let B (k : ℕ) (a b : Fin 3) (z : V) :=
    fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
      (t (L.subsequence k)) ((blowupSequence P E t x ht hR).scale (L.subsequence k))
      (fun w => ((L.embedding k).forward 0
        ⟨neg_nonpos.mpr (L.exhaustion.time_pos k).le, le_rfl⟩ w).val) q a b (0, z)
  let H (a b : Fin 3) (z : V) :=
    (L.limit.flow.metric 0).pullbackCoefficients c.symm z
      (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)
  let Q k := (blowupSequence P E t x ht hR).scale (L.subsequence (sigma k))
  let y k := ((L.embedding (sigma k)).forward 0
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩ (c.symm (pseq k))).val
  have hreal : ∀ᶠ k : ℕ in atTop,
      ∃ gd : Σ g' : RiemannianMetric 3 V, LeviCivitaData g',
        (∀ᶠ z in 𝓝 (pseq k), ∀ a b : Fin 3,
          gd.1.euclideanCoefficients z (EuclideanSpace.basisFun (Fin 3) ℝ a)
            (EuclideanSpace.basisFun (Fin 3) ℝ b) = B (sigma k) a b z) ∧
        scalarGradientNorm gd.1 gd.2 (pseq k) =
          scalarGradientNorm (E.flow.metric (t (L.subsequence (sigma k))))
            (E.flow.connection (t (L.subsequence (sigma k)))) (y k) /
              (Q k * Real.sqrt (Q k)) ∧
        gd.2.laplacian gd.2.scalarCurvature (pseq k) + 2 * gd.2.ricciNormSq (pseq k) =
          ((E.flow.connection (t (L.subsequence (sigma k)))).laplacian
            (E.flow.connection (t (L.subsequence (sigma k)))).scalarCurvature (y k) +
              2 * (E.flow.connection (t (L.subsequence (sigma k)))).ricciNormSq (y k)) /
                Q k ^ 2 := by
    filter_upwards [hsigma.eventually (eventually_ge_atTop j)] with k hk
    have hzero : (0 : ℝ) ∈ Icc (-L.exhaustion.time (sigma k)) 0 :=
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩
    obtain ⟨gk, Dk, hco, _, hgr, hev⟩ := exists_cylinder_scalar_operator_realization
      E.flow.base.flow (L.embedding (sigma k)) (L.exhaustion.space_open (sigma k)) hzero
      ((L.embedding (sigma k)).forward 0 hzero L.limit.base).property q (hKU (hpseq k)).1
      (L.exhaustion.space_increasing hk (hKU (hpseq k)).2)
    exact ⟨⟨gk, Dk⟩, hco, hgr, hev⟩
  obtain ⟨gd, hgd⟩ := hreal.choice
  have hlimcoeff (a b : Fin 3) :
      (fun z => g.inner z (EuclideanSpace.basisFun (Fin 3) ℝ a)
        (EuclideanSpace.basisFun (Fin 3) ℝ b)) =ᶠ[𝓝 p] H a b := by
    filter_upwards [hcoeff] with z hz
    exact congrArg (fun A : V →L[ℝ] V →L[ℝ] ℝ =>
      A (EuclideanSpace.basisFun (Fin 3) ℝ a) (EuclideanSpace.basisFun (Fin 3) ℝ b)) hz
  have hjets (r : ℕ) : Tendsto
      (fun k => iteratedFDeriv ℝ r (gd k).1.euclideanCoefficients (pseq k)) atTop
        (𝓝 (iteratedFDeriv ℝ r g.euclideanCoefficients p)) := by
    apply metric_jet_tendsto_of_scalar_jets
    intro a b
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
    have hsecond : ContDiffAt ℝ ∞ (H a b) p :=
      (hmetric.clm_apply (contDiffAt_const (c := EuclideanSpace.basisFun (Fin 3) ℝ a))).clm_apply
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
    exact ((heq.iteratedFDeriv ℝ r).self_of_nhds).symm
  have hgr := scalarGradientNorm_tendsto_of_metric_jets (fun k => (gd k).2) D pseq p
    (fun r _ => hjets r)
  have hev := scalar_evolution_tendsto_of_metric_jets (fun k => (gd k).2) D pseq p
    (fun r _ => hjets r)
  rw [hgradient] at hgr
  rw [hevolution] at hev
  exact ⟨hgr.congr' (hgd.mono (fun _ hk => hk.2.1)),
    hev.congr' (hgd.mono (fun _ hk => hk.2.2))⟩

end PoincareConjecture.M35.OrdinaryRealization
