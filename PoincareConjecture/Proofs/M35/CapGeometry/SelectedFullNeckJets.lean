import PoincareConjecture.Proofs.M35.CapGeometry.BoundedPullbackJets
import PoincareConjecture.Proofs.M35.Thm12_28.SelectedNeckJets









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle BigOperators Topology

namespace PoincareConjecture.M35.OrdinaryRealization

local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)




theorem blowupSequence_neck_coefficient_error_jets_of_bounded
    (P : M35StandardCapPredecessors)
    {g₀ : StandardInitialMetric} (E : RepairedStandardCapExistenceData g₀)
    (t : ℕ → ℝ) (x : ℕ → StandardCapSpace)
    (ht : ∀ k, t k ∈ Ico 0 E.flow.base.lifetime)
    (hR : Tendsto (fun k => (E.flow.connection (t k)).scalarCurvature (x k)) atTop atTop)
    (L : GeneralizedBlowupConvergence (blowupSequence P E t x ht hR)
      (blowupBackwardInterval ⊤)) :
    letI : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
    letI : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
    letI : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
    ∀ (coordinate : RoundCylinderSpace → L.limit.sliceCarrier.carrier)
      (U : Set RoundCylinderSpace) (_hU : IsOpen U)
      (_hc : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate U)
      (q : ℕ → UnitTwoSphere) (s : ℕ → ℝ) (_hp : ∀ k, (q k, s k) ∈ U)
      (c : L.limit.sliceCarrier.carrier)
      (_hcseq : ∀ k, coordinate (q k, s k) ∈ (extChartAt (𝓡 3) c).source)
      (j : ℕ) (K : Set (ℝ × E3)) (_hK : IsCompact K)
      (_hKU : K ⊆ {p | p ∈ blowupMetricChartDomain L.limit c ∧
        (extChartAt (𝓡 3) c).symm p.2 ∈ L.exhaustion.space j})
      (sigma : ℕ → ℕ) (_hsigma : Tendsto sigma atTop atTop) (u : ℕ → ℝ)
      (_hpoints : ∀ k, (u k, extChartAt (𝓡 3) c (coordinate (q k, s k))) ∈ K)
      (r : ℕ) (a b : Fin 3)
      (_hjets : HasUniformJetBoundsAt (r + 1)
        (fun (k : ℕ) (y : RoundCylinderCoordinates) =>
          extChartAt (𝓡 3) c (coordinate ((chartAt E2 (q k)).symm y.1, y.2)))
        (fun k => (0, s k))),
      let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
        ((L.embedding (sigma k)).forward 0
          ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩ z).val
      let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence (sigma k))
      Tendsto (fun k => iteratedFDeriv ℝ r (fun y : RoundCylinderCoordinates =>
        roundCylinderTensorCoefficient (fun z v w => Q k *
          roundCylinderPullback (E.flow.metric (t (L.subsequence (sigma k)) + u k / Q k))
            (F k ∘ coordinate) z v w) (chartAt E2 (q k)) y a b -
        roundCylinderTensorCoefficient
          (roundCylinderPullback (L.limit.flow.metric (u k)) coordinate)
          (chartAt E2 (q k)) y a b) (0, s k)) atTop (𝓝 0) := by
  let : TopologicalSpace L.limit.carrier.carrier := L.limit.carrier.topologicalSpace
  let : ChartedSpace E3 L.limit.carrier.carrier := L.limit.carrier.chartedSpace
  have : IsManifold (𝓡 3) ∞ L.limit.carrier.carrier := L.limit.carrier.isManifold
  intro coordinate U hU hcoord q s hp c hcseq j K hK hKU sigma hsigma u hpoints r a b hjets
  let F (k : ℕ) (z : L.limit.sliceCarrier.carrier) :=
    ((L.embedding (sigma k)).forward 0
      ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩ z).val
  let Q (k : ℕ) := (blowupSequence P E t x ht hR).scale (L.subsequence (sigma k))
  let H : RoundCylinderSpace → E3 := extChartAt (𝓡 3) c ∘ coordinate
  let psi (k : ℕ) (y : RoundCylinderCoordinates) := H ((chartAt E2 (q k)).symm y.1, y.2)
  let A (k : ℕ) (y : E3) (i j : Fin 3) :=
    fixedCylinderMetricCoefficient E.flow.base.flow L.limit.sliceCarrier
      (t (L.subsequence (sigma k))) (Q k) (F k) c i j (u k, y) -
    FlowCarrier.coordinateCoefficient L.limit.carrier c
      (fun s z v w => (L.limit.flow.metric s).inner z v w) i j (u k, y)
  have hcenter (k : ℕ) : (chartAt E2 (q k)).symm 0 = q k := by
    have h := (chartAt E2 (q k)).left_inv (mem_chart_source E2 (q k))
    rwa [sphere_chart_center] at h
  have hpsicenter (k : ℕ) : psi k (0, s k) = H (q k, s k) := by
    simp only [psi, hcenter]
  have hpsi (k : ℕ) : ContDiffAt ℝ ∞ (psi k) (0, s k) := by
    have hchart : coordinate (q k, s k) ∈ (chartAt E3 c).source := by
      rw [← extChartAt_source (I := 𝓡 3)]
      exact hcseq k
    have hh := (contMDiffAt_extChartAt' (I := 𝓡 3) (n := ∞) hchart).comp (q k, s k)
      (hcoord.contMDiffAt (hU.mem_nhds (hp k)))
    have hh' : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ H
        ((chartAt E2 (q k)).symm 0, s k) := by
      rw [hcenter]
      exact hh
    exact (hh'.comp (0, s k) (preferredCylinderChart_contMDiff (q k) (0, s k))).contDiffAt
  have hcontrol (i j' : Fin 3) :
      (∀ᶠ k in atTop, ContDiffAt ℝ ∞ (fun y => A k y i j') (H (q k, s k))) ∧
      ∀ m : ℕ, Tendsto (fun k => iteratedFDeriv ℝ m (fun y => A k y i j') (H (q k, s k)))
        atTop (𝓝 0) :=
    blowupSequence_spatial_error_jets P E t x ht hR L c j i j' K hK hKU sigma hsigma
      (fun k => (u k, H (q k, s k))) hpoints
  have hlim := cylinder_pullback_jet_difference_tendsto_zero_of_bounded psi
    (fun k => (0, s k)) (roundCylinderCoordinateBasis a) (roundCylinderCoordinateBasis b)
    A r hpsi hjets
    (fun i j' => by simpa only [hpsicenter] using (hcontrol i j').1)
    (fun m _ i j' => by simpa only [hpsicenter] using (hcontrol i j').2 m)
  apply hlim.congr'
  filter_upwards [hsigma.eventually (eventually_ge_atTop j)] with k hk
  have hzeroTime : (0 : ℝ) ∈ Icc (-L.exhaustion.time (sigma k)) 0 :=
    ⟨neg_nonpos.mpr (L.exhaustion.time_pos (sigma k)).le, le_rfl⟩
  have htime : t (L.subsequence (sigma k)) + 0 / Q k ∈ Ico 0 E.flow.base.lifetime :=
    ((L.embedding (sigma k)).forward 0 hzeroTime L.limit.base).property
  have hF : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (F k) (L.exhaustion.space (sigma k)) :=
    (sliceDiffeomorph htime).contMDiff.comp_contMDiffOn
      ((L.embedding (sigma k)).forward_smooth 0 hzeroTime)
  let pref (y : RoundCylinderCoordinates) := ((chartAt E2 (q k)).symm y.1, y.2)
  let phi : RoundCylinderCoordinates → L.limit.sliceCarrier.carrier := coordinate ∘ pref
  have hpref : pref (0, s k) = (q k, s k) := by simp only [pref, hcenter]
  have hphiCenter : phi (0, s k) = coordinate (q k, s k) := congrArg coordinate hpref
  have hcoordAt : ContMDiffAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ coordinate (pref (0, s k)) :=
    hpref.symm ▸ hcoord.contMDiffAt (hU.mem_nhds (hp k))
  have hphi : ContMDiffAt 𝓘(ℝ, RoundCylinderCoordinates) (𝓡 3) ∞ phi (0, s k) :=
    hcoordAt.comp (0, s k) (preferredCylinderChart_contMDiff (q k) (0, s k))
  have hyj : coordinate (q k, s k) ∈ L.exhaustion.space j := by
    have hy := (hKU (hpoints k)).2
    rwa [(extChartAt (𝓡 3) c).left_inv (hcseq k)] at hy
  have hnearU := (preferredCylinderChart_contMDiff (q k) (0, s k)).continuousAt.preimage_mem_nhds
    (hU.mem_nhds (by
      change pref (0, s k) ∈ U
      rw [hpref]
      exact hp k))
  have hnearC := hphi.continuousAt.preimage_mem_nhds
    ((isOpen_extChartAt_source (I := 𝓡 3) c).mem_nhds (hphiCenter.symm ▸ hcseq k))
  have hnearF := hphi.continuousAt.preimage_mem_nhds
    ((L.exhaustion.space_open (sigma k)).mem_nhds
      (hphiCenter.symm ▸ L.exhaustion.space_increasing hk hyj))
  have hgerm : (fun y : RoundCylinderCoordinates =>
      roundCylinderTensorCoefficient (fun z v w => Q k *
        roundCylinderPullback (E.flow.metric (t (L.subsequence (sigma k)) + u k / Q k))
          (F k ∘ coordinate) z v w) (chartAt E2 (q k)) y a b -
      roundCylinderTensorCoefficient (roundCylinderPullback (L.limit.flow.metric (u k)) coordinate)
        (chartAt E2 (q k)) y a b) =ᶠ[𝓝 (0, s k)]
      (fun y => ∑ i : Fin 3, ∑ j' : Fin 3, A k (psi k y) i j' *
        (fderiv ℝ (psi k) y (roundCylinderCoordinateBasis a)) i *
        (fderiv ℝ (psi k) y (roundCylinderCoordinateBasis b)) j') := by
    filter_upwards [hnearU, hnearC, hnearF] with y hyU hyC hyF
    have hco := hcoord.contMDiffAt (hU.mem_nhds hyU)
    have hfo := hF.contMDiffAt ((L.exhaustion.space_open (sigma k)).mem_nhds hyF)
    have hfirst := roundCylinderPullback_coefficient_eq_chart_sum
      (E.flow.metric (t (L.subsequence (sigma k)) + u k / Q k)) (F k) coordinate
      (q k) c y a b hyC hfo hco
    have hsecond := roundCylinderPullback_coefficient_eq_chart_sum
      (L.limit.flow.metric (u k)) id coordinate (q k) c y a b hyC contMDiffAt_id hco
    have hcoef (i j' : Fin 3) : A k (psi k y) i j' =
        Q k * (E.flow.metric (t (L.subsequence (sigma k)) + u k / Q k)).pullbackCoefficients
          (F k ∘ (extChartAt (𝓡 3) c).symm) (psi k y)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j') -
        (L.limit.flow.metric (u k)).pullbackCoefficients (extChartAt (𝓡 3) c).symm (psi k y)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j') := by
      have hinv : (extChartAt (𝓡 3) c).symm (psi k y) = phi y :=
        (extChartAt (𝓡 3) c).left_inv hyC
      have hfixed := fixedCylinderMetricCoefficient_eq_pullback
        E.flow.base.flow L.limit.sliceCarrier
        (t (L.subsequence (sigma k))) (Q k) (F k) c i j' (u k, psi k y)
        ((extChartAt (𝓡 3) c).map_source hyC) (hinv.symm ▸ hfo)
      exact congrArg (fun z : ℝ => z -
        (L.limit.flow.metric (u k)).pullbackCoefficients (extChartAt (𝓡 3) c).symm (psi k y)
          (EuclideanSpace.basisFun (Fin 3) ℝ i) (EuclideanSpace.basisFun (Fin 3) ℝ j')) hfixed
    change Q k * roundCylinderTensorCoefficient
      (roundCylinderPullback (E.flow.metric (t (L.subsequence (sigma k)) + u k / Q k))
        (F k ∘ coordinate)) (chartAt E2 (q k)) y a b -
        roundCylinderTensorCoefficient
          (roundCylinderPullback (L.limit.flow.metric (u k)) coordinate)
          (chartAt E2 (q k)) y a b = _
    refine (congrArg₂ (fun v w : ℝ => Q k * v - w) hfirst hsecond).trans ?_
    simp_rw [hcoef]
    simp only [Finset.mul_sum, sub_mul, Finset.sum_sub_distrib, mul_assoc,
      psi, H, Function.comp_def, id_eq]
    rfl
  exact ((hgerm.iteratedFDeriv ℝ r).eq_of_nhds).symm

end PoincareConjecture.M35.OrdinaryRealization
