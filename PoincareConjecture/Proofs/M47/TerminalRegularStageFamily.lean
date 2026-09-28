import PoincareConjecture.Proofs.M47.TerminalRegularSourceG4
import PoincareConjecture.Proofs.M47.TerminalRegularNormalStage
import PoincareConjecture.Proofs.M47.TerminalRegularNormalMaps
import PoincareConjecture.Proofs.M07.Topology.Sequences.Diagonal










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)


def terminalRegularStageSource (F : SurgeryFlowData.{u}) (base Q A : ℝ)
    (center : (F.slice base).carrier) : TopologicalSpace.Opens (F.slice base).carrier :=
  ⟨(F.metric base).ball center (A / Real.sqrt Q), M04.initial_ball_isOpen _ _ _⟩



structure TerminalRegularStageData
    (S : RepairedControlledSchedulesData.{u}) (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) {F : SurgeryFlowData.{u}}
    (O : SurgeryObservation F) {W : M33RegularHistoryWindow F} (H : M33RegularHistoryData W)
    (base Q r A tau0 tau K L a R rho : ℝ) (N : ℕ)
    (center : (F.slice base).carrier) where
  original : SurgeryFlowCylinder F (F.slice base) base Q (Icc (-tau0) 0)
    (terminalRegularStageSource F base Q A center)
  short : tau ≤ tau0
  rho_pos : 0 < rho
  point : terminalRegularStageSource F base Q A center
  point_eq : point.val = center
  time : ∀ s ∈ Icc (-tau) 0, base + s / Q ∈ H.generalized.interval
  cylinder : GeneralizedFlowCylinder H.generalized (F.slice base) base Q (Icc (-tau) 0)
    (terminalRegularStageSource F base Q A center)
  flow : RicciFlow 3 (terminalRegularStageSource F base Q A center) (Icc (-tau) 0)
  forward_eq : ∀ s hs y, y ∈ terminalRegularStageSource F base Q A center →
    H.history.forward (base + s / Q) (time s hs) (cylinder.forward s hs y) =
      original.forward s ⟨(neg_le_neg short).trans hs.1, hs.2⟩ y
  metric : ∀ s hs (z : terminalRegularStageSource F base Q A center)
    (v w : TangentSpace (𝓡 3) z),
    (flow.metric s).inner z v w = cylinder.pullbackInner s hs z.val
      (mfderiv (𝓡 3) (𝓡 3)
        (Subtype.val : terminalRegularStageSource F base Q A center → (F.slice base).carrier) z v)
      (mfderiv (𝓡 3) (𝓡 3)
        (Subtype.val : terminalRegularStageSource F base Q A center → (F.slice base).carrier) z w)
  scalar : ∀ s hs (z : terminalRegularStageSource F base Q A center),
    (flow.connection s).scalarCurvature z =
      (H.generalized.connection (base + s / Q)).scalarCurvature (cylinder.forward s hs z.val) / Q
  norm : ∀ s hs (z : terminalRegularStageSource F base Q A center),
    (flow.connection s).curvatureTensorNorm z =
      (H.generalized.connection (base + s / Q)).curvatureTensorNorm
        (cylinder.forward s hs z.val) / Q
  bound : ∀ s ∈ Icc (-tau) 0, ∀ z, (flow.connection s).curvatureTensorNorm z ≤ K
  terminal_scalar : ∀ z, (flow.connection 0).scalarCurvature z =
    (F.connection base).scalarCurvature z.val / Q
  scalar_one : (flow.connection 0).scalarCurvature point = 1
  terminal : ∀ h0 : (0 : ℝ) ∈ Icc (-tau) 0,
    let j := terminalSourceNormal_terminalMap (terminalRegularStageSource F base Q A center)
      point (terminalSourceNormal_historyCylinder H _ time cylinder) h0
    j.source = univ ∧ j.target = terminalRegularStageSource F base Q A center ∧
      ∀ z, j z = z.val
  cover : TerminalSourceIndexedChartCover (flow.metric 0) point a R rho N
  quadratic : ∀ i, ∀ z ∈ Metric.closedBall (0 : E) (2 * rho), ∀ v,
    (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ (flow.metric 0).pullbackCoefficients (cover.chart i).chart z v v ∧
      (flow.metric 0).pullbackCoefficients (cover.chart i).chart z v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2
  maps : Fin (N + 1) → terminalSourceCountableDomain rho →
    Poincare.connectedComponentOpens E center
  projection : ∀ i z, (maps i z).val = ((cover.chart i).chart z.val).val
  zero : maps 0 (terminalSourceCountableZero rho_pos) = ⟨center, mem_connectedComponent⟩
  geometry : ∀ i, Topology.IsOpenEmbedding (maps i) ∧
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (maps i)
  distances :
    let h : RiemannianMetric 3 (F.slice base).carrier :=
      M13.scaleSmoothMetric (F.metric base) Q original.scale_pos
    letI := terminalSourceComponentMetricSpace h center
    ∀ i z z', (1 / 2 : ℝ) * dist z z' ≤ dist (maps i z) (maps i z') ∧
      dist (maps i z) (maps i z') ≤ (3 / 2 : ℝ) * dist z z'
  based_distances :
    let h : RiemannianMetric 3 (F.slice base).carrier :=
      M13.scaleSmoothMetric (F.metric base) Q original.scale_pos
    letI := terminalSourceComponentMetricSpace h center
    ∀ i z, dist (⟨center, mem_connectedComponent⟩ : Poincare.connectedComponentOpens E center)
      (maps i z) ≤ a + R
  map_metric :
    let h : RiemannianMetric 3 (F.slice base).carrier :=
      M13.scaleSmoothMetric (F.metric base) Q original.scale_pos
    ∀ i (z : terminalSourceCountableDomain rho) (v w : TangentSpace (𝓡 3) z),
      (h.connectedComponentMetric center).inner (maps i z)
        (mfderiv (𝓡 3) (𝓡 3) (maps i) z v) (mfderiv (𝓡 3) (𝓡 3) (maps i) z w) =
      (flow.metric 0).inner ((cover.chart i).chart z.val)
        (mfderiv (𝓡 3) (𝓡 3)
          (fun y : terminalSourceCountableDomain rho => (cover.chart i).chart y.val) z v)
        (mfderiv (𝓡 3) (𝓡 3)
          (fun y : terminalSourceCountableDomain rho => (cover.chart i).chart y.val) z w)
  cores :
    let h : RiemannianMetric 3 (F.slice base).carrier :=
      M13.scaleSmoothMetric (F.metric base) Q original.scale_pos
    letI := terminalSourceComponentMetricSpace h center
    ∃ core : Set (terminalSourceCountableDomain rho), IsCompact core ∧
      (∀ z, z ∈ core ↔ z.val ∈ Metric.closedBall (0 : E) (rho / 4)) ∧
      Metric.ball (⟨center, mem_connectedComponent⟩ : Poincare.connectedComponentOpens E center) a ⊆
        ⋃ i, maps i '' core
  good : ∀ i, TerminalSourceJetsG4Good S B p O H
    (terminalRegularStageSource F base Q A center) cylinder flow
      (rNext := r) (L := L) (eta := 1) (cover.chart i)



theorem terminalSource_regular_stage_family
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (B : M47ComponentAnalyticBounds.{u} S.setup.C)
    (p : SurgeryParameterPrefix S.constants) (hp : S.SeedCompatible p)
    (F : ℕ → SurgeryFlowData.{u}) (O : ∀ n, SurgeryObservation (F n))
    (W : ∀ n, M33RegularHistoryWindow (F n)) (H : ∀ n, M33RegularHistoryData (W n))
    (base r delta : ℕ → ℝ) (ht : ∀ n, base n ∈ (H n).generalized.interval)
    (x : ∀ n, ((H n).generalized.slice (base n)).carrier)
    (old : ∀ n, SurgeryPrefixControls p (F n) (O n))
    (hBase : ∀ n, base n ∈ Ico (surgeryEpochStart p.i) (O n).H)
    (hPinched : ∀ n, SurgeryFlowPinched (F n))
    (hEarlier : ∀ n, SurgeryCanonicalOn (F n) (Ico 0 (base n)) (r n))
    (hFloor : ∀ n, (r n)⁻¹ ^ 2 ≤ ((F n).connection (base n)).scalarCurvature
      ((H n).history.forward (base n) (ht n) (x n)))
    (hOverlap : ∀ n t, t ∈ surgeryObservationInterval (O n) ∩
      Ico (surgeryEpochStart (p.i - 1)) (O n).H → (F n).parameters.delta t ≤ delta n)
    (hdelta : Tendsto delta atTop (𝓝 0))
    (hDiverges : Tendsto (fun n => ((F n).connection (base n)).scalarCurvature
      ((H n).history.forward (base n) (ht n) (x n))) atTop atTop)
    (A tau0 K : ℕ → ℝ) (hA : ∀ j, 0 < A j) (htau0 : ∀ j, 0 < tau0 j)
    (hK : ∀ j, 0 ≤ K j) (hcofinal : ∀ R : ℝ, 0 < R → ∃ j, R ≤ A j)
    {rvol vvol : ℝ} (hrvol : 0 < rvol) (hvvol : 0 < vvol) :
    let Q : ℕ → ℝ := fun n => (H n).generalized.scalar ⟨base n, x n⟩
    let center := fun n => (H n).history.forward (base n) (ht n) (x n)
    let U := fun j n => terminalRegularStageSource (F n) (base n) (Q n) (A j) (center n)
    (∀ᶠ n in atTop, ENNReal.ofReal (vvol / Real.sqrt (Q n) ^ 3) ≤
      calibratedMetricVolume ((H n).generalized.metric (base n))
        (((H n).generalized.metric (base n)).ball (x n) (rvol / Real.sqrt (Q n)))) →
    ∀ e : ∀ j (n : {k : ℕ // j ≤ k}),
      SurgeryFlowCylinder (F n.val) ((F n.val).slice (base n.val)) (base n.val) (Q n.val)
        (Icc (-(tau0 j)) 0) (U j n.val),
    (∀ (j : ℕ) (n : {k : ℕ // j ≤ k}) hs (z : ((F n.val).slice (base n.val)).carrier),
      z ∈ U j n.val → HEq ((e j n).forward 0 hs z) z) →
    (∀ (j : ℕ) (n : {k : ℕ // j ≤ k}) s hs (z : ((F n.val).slice (base n.val)).carrier),
      z ∈ U j n.val →
      ((F n.val).connection (base n.val + s / Q n.val)).curvatureTensorNorm
        ((e j n).forward s hs z) ≤ K j * Q n.val) →
    let a := fun j : ℕ => (j : ℝ) + 1
    let Rbig := fun j => a j + rvol + 1
    ∃ m : ℕ → ℕ, (∀ j, 6 * Rbig j ≤ A (m j)) ∧
      let L := fun j => max 1 (9 * K (m j))
      let tau := fun j => min (tau0 (m j) / 2) (1 / (4 * blowupAnalyticConstant S B * L j))
      let Hbar := fun j => 13 * max (4 * L j / 3) 1
      let Rchart := fun j => RiemannianMetric.localInjectivityRadius 3 (Hbar j) (Rbig j) vvol
      ∃ rho : ℕ → ℝ,
        (∀ j, 0 < tau j ∧ tau j < tau0 (m j) ∧ 0 < rho j ∧
          2 * rho j < Rchart j ∧ Rchart j < Rbig j) ∧
        (∀ j s, |s| ≤ 2 * rho j →
          ((Hbar j) * s ^ 2) * Real.exp (max 1 ((Hbar j) * s ^ 2)) ≤ 3) ∧
      let N := fun j => ⌈RiemannianMetric.modelVolume 3 (Hbar j) (3 * a j) /
        RiemannianMetric.modelVolume 3 (Hbar j) (min (a j / 2) (rho j / 4) / 2)⌉₊ + 1
      ∃ lambda : ℕ → ℕ, StrictMono lambda ∧
      ∃ available : ∀ k j, j ≤ k → m j ≤ lambda k,
      ∃ data : ∀ k j, j ≤ k → TerminalRegularStageData S B p (O (lambda k)) (H (lambda k))
        (base (lambda k)) (Q (lambda k)) (r (lambda k)) (A (m j))
        (tau0 (m j)) (tau j) (K (m j)) (L j) (a j) (Rchart j) (rho j) (N j)
        (center (lambda k)),
        ∀ k j hjk, (data k j hjk).original = e (m j) ⟨lambda k, available k j hjk⟩ := by
  classical
  let Q : ℕ → ℝ := fun n => (H n).generalized.scalar ⟨base n, x n⟩
  let center := fun n => (H n).history.forward (base n) (ht n) (x n)
  let U := fun j n => terminalRegularStageSource (F n) (base n) (Q n) (A j) (center n)
  dsimp only
  intro hvolume e hbased hbound
  let a := fun j : ℕ => (j : ℝ) + 1
  let Rbig := fun j => a j + rvol + 1
  have ha (j : ℕ) : 0 < a j := by dsimp only [a]; positivity
  have hRbig (j : ℕ) : 0 < Rbig j := by dsimp only [Rbig]; linarith [ha j]
  choose m hm using fun j => hcofinal (6 * Rbig j) (mul_pos (by norm_num) (hRbig j))
  let L := fun j => max 1 (9 * K (m j))
  let tau := fun j => min (tau0 (m j) / 2) (1 / (4 * blowupAnalyticConstant S B * L j))
  let Hbar := fun j => 13 * max (4 * L j / 3) 1
  let Rchart := fun j => RiemannianMetric.localInjectivityRadius 3 (Hbar j) (Rbig j) vvol
  have hapos (j : ℕ) : a j ≤ Rbig j := by dsimp only [Rbig]; linarith
  have harp (j : ℕ) : a j + rvol ≤ Rbig j := by dsimp only [Rbig]; linarith
  choose rho hrho hrhoR hsmall factory using fun j =>
    terminalSource_regular_normal_stage (hK (m j)) (ha j) hrvol hvvol (hapos j) (harp j) (hm j)
  have htau (j : ℕ) : 0 < tau j := by
    have hL : 0 < L j := zero_lt_one.trans_le (le_max_left _ _)
    exact lt_min (half_pos (htau0 (m j))) (one_div_pos.mpr
      (mul_pos (mul_pos (by norm_num) (blowupAnalyticConstant_pos S B)) hL))
  have hshort (j : ℕ) : tau j < tau0 (m j) :=
    (min_le_left _ _).trans_lt (half_lt_self (htau0 (m j)))
  have hchart (j : ℕ) : Rchart j < Rbig j :=
    RiemannianMetric.localInjectivityRadius_lt 3 (Hbar j) (hRbig j) vvol
  have sources := fun (j : ℕ) =>
    (terminalSource_regular_stage_G4 P S B p hp
      (Filter.comap (Subtype.val : {n : ℕ // m j ≤ n} → ℕ) atTop)
      (fun n => F n.val) (fun n => O n.val) (fun n => W n.val) (fun n => H n.val)
      (fun n => base n.val) (fun n => r n.val) (fun n => delta n.val)
      (fun n => ht n.val) (fun n => x n.val) (fun n => old n.val)
      (fun n => hBase n.val) (fun n => hPinched n.val) (fun n => hEarlier n.val)
      (fun n => hFloor n.val) (fun n => hOverlap n.val)
      (hdelta.comp tendsto_comap) (hDiverges.comp tendsto_comap)
      (hA (m j)) (htau0 (m j))).2.2.2
        (e (m j)) (hbased (m j)) (hbound (m j))
  choose points times cylinders flows readouts good using sources
  let N := fun j => ⌈RiemannianMetric.modelVolume 3 (Hbar j) (3 * a j) /
    RiemannianMetric.modelVolume 3 (Hbar j) (min (a j / 2) (rho j / 4) / 2)⌉₊ + 1
  have hstage (j : ℕ) : ∀ᶠ n in atTop, ∃ hn : m j ≤ n,
      ∃ d : TerminalRegularStageData S B p (O n) (H n) (base n) (Q n) (r n) (A (m j))
        (tau0 (m j)) (tau j) (K (m j)) (L j) (a j) (Rchart j) (rho j) (N j) (center n),
        d.original = e (m j) ⟨n, hn⟩ := by
    filter_upwards [eventually_ge_atTop (m j), hvolume, Filter.eventually_comap.mp (good j)]
      with n hn hv hg
    let k : {n : ℕ // m j ≤ n} := ⟨n, hn⟩
    rcases readouts j k with ⟨hp0, hforward, hG, hnorm, hscalar, hone, _hterminal, hmap⟩
    let h0 : (0 : ℝ) ∈ Icc (-(tau j)) 0 := ⟨neg_nonpos.mpr (htau j).le, le_rfl⟩
    obtain ⟨cover, hquadratic, hmetric, himage⟩ := factory j (H n) (base n)
      (tau0 (m j)) (tau j) (ht n) (htau0 (m j)) (htau j) (x n)
      (e (m j) k) (hbased (m j) k) hv (points j k) hp0
      (times j k) (cylinders j k) (flows j k)
      (fun z => (hG 0 h0 z).1) (fun z => (hG 0 h0 z).2.2)
      (hnorm 0 h0) hmap.2.2
    let ereal := terminalSourceNormal_historyCylinder (H n) (U (m j) n)
      (times j k) (cylinders j k)
    obtain ⟨maps, hprojection, hzero, hgeometry, hdist, hbaseDist, hmapMetric, hcores⟩ :=
      terminalSource_regular_normal_maps (U (m j) n) (points j k) ereal h0
        ((flows j k).metric 0) (center n) hp0 hmap.2.2 hmetric cover
        (ha j) (hapos j) (hchart j).le (hrho j) (hrhoR j) himage hquadratic
    refine ⟨hn, {
      original := e (m j) k
      short := (hshort j).le
      rho_pos := hrho j
      point := points j k
      point_eq := hp0
      time := times j k
      cylinder := cylinders j k
      flow := flows j k
      forward_eq := hforward
      metric := fun s hs z => (hG s hs z).1
      scalar := fun s hs z => (hG s hs z).2.1
      norm := fun s hs z => (hG s hs z).2.2
      bound := hnorm
      terminal_scalar := hscalar
      scalar_one := hone
      terminal := fun _ => hmap
      cover := cover
      quadratic := hquadratic
      maps := maps
      projection := fun i z => (hprojection i z).trans (hmap.2.2 _)
      zero := hzero
      geometry := hgeometry
      distances := hdist
      based_distances := hbaseDist
      map_metric := hmapMetric
      cores := hcores
      good := fun i => hg k rfl _ (cover.chart i) }, rfl⟩
  obtain ⟨lambda, hlambda, selected⟩ := Poincare.exists_strictMono_forall_le_of_eventually hstage
  choose available data hsame using selected
  exact ⟨m, hm, rho, fun j => ⟨htau j, hshort j, hrho j, hrhoR j, hchart j⟩,
    hsmall, lambda, hlambda, available, data, hsame⟩

end PoincareConjecture.M47
