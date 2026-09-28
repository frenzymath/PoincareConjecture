import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Coordinates.Transitions
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Curvature.Estimates.Shi.Paths.UniformTaylor
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

set_option autoImplicit false

open Set Filter Topology
open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareConjecture.RicciFlowAnalysis

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "End" => E →L[ℝ] E
local notation "Data" => ℝ × ((E × (E × End)) × ((E × End) × (E × End)))

def joinedTime (p : Data) : ℝ := p.1
def joinedX (p : Data) : E := p.2.1.1
def joinedT (p : Data) : E := p.2.1.2.1
def joinedP (p : Data) : End := p.2.1.2.2
def joinedYL (p : Data) : E := p.2.2.1.1
def joinedQL (p : Data) : End := p.2.2.1.2
def joinedYR (p : Data) : E := p.2.2.2.1
def joinedQR (p : Data) : End := p.2.2.2.2

private theorem joinedTime_contDiff : ContDiff ℝ ∞ (joinedTime (n := n)) := by
  unfold joinedTime
  fun_prop
private theorem joinedX_contDiff : ContDiff ℝ ∞ (joinedX (n := n)) := by
  unfold joinedX
  fun_prop
private theorem joinedT_contDiff : ContDiff ℝ ∞ (joinedT (n := n)) := by
  unfold joinedT
  fun_prop
private theorem joinedP_contDiff : ContDiff ℝ ∞ (joinedP (n := n)) := by
  unfold joinedP
  fun_prop
private theorem joinedYL_contDiff : ContDiff ℝ ∞ (joinedYL (n := n)) := by
  unfold joinedYL
  fun_prop
private theorem joinedQL_contDiff : ContDiff ℝ ∞ (joinedQL (n := n)) := by
  unfold joinedQL
  fun_prop
private theorem joinedYR_contDiff : ContDiff ℝ ∞ (joinedYR (n := n)) := by
  unfold joinedYR
  fun_prop
private theorem joinedQR_contDiff : ContDiff ℝ ∞ (joinedQR (n := n)) := by
  unfold joinedQR
  fun_prop

noncomputable def shiRawCoordinateVariation
    (D : LeviCivitaData g) (c : OpenPartialHomeomorph M E)
    (s : ℝ) (y : E) (Q : End) (z : E) : E :=
  y + s • Q z - (1 / 2 : ℝ) •
    shiChartChristoffel D c y (s • Q z) (s • Q z)

noncomputable def shiJoinedTransition
    (c k : OpenPartialHomeomorph M E) (y : E) : E := c (k.symm y)

noncomputable def shiJoinedRawEndpoint
    (D : LeviCivitaData g) (c k : OpenPartialHomeomorph M E)
    (s : ℝ) (y : E) (Q : End) (z : E) : E :=
  shiRawCoordinateVariation D c s (shiJoinedTransition c k y)
    ((fderiv ℝ (c ∘ k.symm) y).comp Q) z

noncomputable def shiJoinedDiscrepancy
    (D : LeviCivitaData g) (c k : OpenPartialHomeomorph M E)
    (s : ℝ) (y : E) (Q : End) (z : E) : E :=
  (c ∘ k.symm) (shiRawCoordinateVariation D k s y Q z) -
    shiJoinedRawEndpoint D c k s y Q z

noncomputable def shiJoinedA (p : Data) (z : E) : E := joinedTime p • joinedP p z

noncomputable def shiJoinedJ
    (D : LeviCivitaData g) (c : OpenPartialHomeomorph M E)
    (p : Data) (z : E) : E :=
  joinedP p z - shiChartChristoffel D c (joinedX p)
    (joinedT p) (shiJoinedA p z)

noncomputable def shiJoinedPosition
    (D : LeviCivitaData g) (c cL cR : OpenPartialHomeomorph M E)
    (a b : ℝ) (p : Data) (z : E) : E :=
  shiRawCoordinateVariation D c (joinedTime p) (joinedX p) (joinedP p) z +
    ((b - joinedTime p) / (b - a)) •
      shiJoinedDiscrepancy D c cL a (joinedYL p) (joinedQL p) z +
    ((joinedTime p - a) / (b - a)) •
      shiJoinedDiscrepancy D c cR b (joinedYR p) (joinedQR p) z

noncomputable def shiJoinedVelocity
    (D : LeviCivitaData g) (c cL cR : OpenPartialHomeomorph M E)
    (a b : ℝ) (p : Data) (z : E) : E :=
  joinedT p + shiJoinedJ D c p z -
    (1 / 2 : ℝ) •
      ((fderiv ℝ (shiChartChristoffel D c) (joinedX p) (joinedT p))
          (shiJoinedA p z) (shiJoinedA p z) +
        shiChartChristoffel D c (joinedX p)
          (shiJoinedJ D c p z) (shiJoinedA p z) +
        shiChartChristoffel D c (joinedX p)
          (shiJoinedA p z) (shiJoinedJ D c p z)) +
    (b - a)⁻¹ •
      (shiJoinedDiscrepancy D c cR b (joinedYR p) (joinedQR p) z -
        shiJoinedDiscrepancy D c cL a (joinedYL p) (joinedQL p) z)

noncomputable def shiJoinedDensity
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (c cL cR : OpenPartialHomeomorph M E) (a b : ℝ)
    (p : Data) (z : E) : ℝ :=
  shiChartMetric g c (shiJoinedPosition D c cL cR a b p z)
    (shiJoinedVelocity D c cL cR a b p z)
    (shiJoinedVelocity D c cL cR a b p z)

def shiJoinedBase
    (c cL cR : OpenPartialHomeomorph M E)
    (p : Data) : Prop :=
  joinedX p ∈ c.target ∧
    joinedYL p ∈ (cL.target ∩ cL.symm ⁻¹' c.source) ∧
    joinedYR p ∈ (cR.target ∩ cR.symm ⁻¹' c.source)

def shiJoinedDomain
    (D : LeviCivitaData g) (c cL cR : OpenPartialHomeomorph M E)
    (a b : ℝ) : Set (Data × E) :=
  {q | shiJoinedBase c cL cR q.1 ∧
    shiRawCoordinateVariation D cL a (joinedYL q.1) (joinedQL q.1) q.2 ∈
      (cL.target ∩ cL.symm ⁻¹' c.source) ∧
    shiRawCoordinateVariation D cR b (joinedYR q.1) (joinedQR q.1) q.2 ∈
      (cR.target ∩ cR.symm ⁻¹' c.source) ∧
    shiJoinedPosition D c cL cR a b q.1 q.2 ∈ c.target}

def shiJoinedBaseSet
    (c cL cR : OpenPartialHomeomorph M E) : Set Data :=
  {p | shiJoinedBase c cL cR p}

theorem shiJoinedBase_isOpen
    {c cL cR : OpenPartialHomeomorph M E} :
    IsOpen (shiJoinedBaseSet c cL cR) := by
  unfold shiJoinedBaseSet shiJoinedBase
  have hx : IsOpen {p : Data | joinedX p ∈ c.target} :=
    c.open_target.preimage joinedX_contDiff.continuous
  have hl : IsOpen {p : Data | joinedYL p ∈
      (cL.target ∩ cL.symm ⁻¹' c.source)} := by
    exact (cL.isOpen_inter_preimage_symm c.open_source).preimage
      joinedYL_contDiff.continuous
  have hr : IsOpen {p : Data | joinedYR p ∈
      (cR.target ∩ cR.symm ⁻¹' c.source)} := by
    exact (cR.isOpen_inter_preimage_symm c.open_source).preimage
      joinedYR_contDiff.continuous
  exact hx.inter (hl.inter hr)

private theorem joinedRaw_contDiffAt [T2Space M]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (D : LeviCivitaData g) {c : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    {s : P → ℝ} {y : P → E} {Q : P → End} {z : P → E} {p : P}
    (hs : ContDiffAt ℝ ∞ s p) (hy : ContDiffAt ℝ ∞ y p)
    (hQ : ContDiffAt ℝ ∞ Q p) (hz : ContDiffAt ℝ ∞ z p)
    (hyt : y p ∈ c.target) :
    ContDiffAt ℝ ∞
      (fun r => shiRawCoordinateVariation D c (s r) (y r) (Q r) (z r)) p := by
  have hGamma := ((shiChartChristoffel_smooth D hc hi).contDiffAt
    (c.open_target.mem_nhds hyt)).comp p hy
  have hA := hs.smul (hQ.clm_apply hz)
  have hEval := (hGamma.clm_apply hA).clm_apply hA
  exact (hy.add hA).sub (hEval.const_smul (1 / 2 : ℝ))

private theorem joinedTransition_contDiffOn
    {c k : OpenPartialHomeomorph M E}
    (hk : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ k.symm k.target)
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source) :
    ContDiffOn ℝ ∞ (c ∘ k.symm)
      (k.target ∩ k.symm ⁻¹' c.source) :=
  shiChartTransition_smooth hk hc

private theorem joinedEndpoint_contDiffAt [T2Space M]
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (D : LeviCivitaData g) {c k : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hk : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ k k.source)
    (hki : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ k.symm k.target)
    (s : ℝ) {y : P → E} {Q : P → End} {z : P → E} {p : P}
    (hy : ContDiffAt ℝ ∞ y p) (hQ : ContDiffAt ℝ ∞ Q p)
    (hz : ContDiffAt ℝ ∞ z p)
    (hyt : y p ∈ k.target ∩ k.symm ⁻¹' c.source)
    (hrawt : shiRawCoordinateVariation D k s (y p) (Q p) (z p) ∈
      k.target ∩ k.symm ⁻¹' c.source) :
    ContDiffAt ℝ ∞
      (fun r => shiJoinedDiscrepancy D c k s (y r) (Q r) (z r)) p := by
  have hO := k.isOpen_inter_preimage_symm c.open_source
  have hTau := (joinedTransition_contDiffOn hki hc).contDiffAt
    (hO.mem_nhds hyt)
  have hRaw := joinedRaw_contDiffAt D hk hki (s := fun _ => s)
    contDiffAt_const hy hQ hz hyt.1
  have hLeft := ((joinedTransition_contDiffOn hki hc).contDiffAt
    (hO.mem_nhds hrawt)).comp p hRaw
  have hY := hTau.comp p hy
  have hMatrix := ((hTau.fderiv_right (m := ∞) (by simp)).comp p hy).clm_comp hQ
  have hRight := joinedRaw_contDiffAt D hc hi (s := fun _ => s)
    contDiffAt_const hY hMatrix hz
    (c.map_source hyt.2)
  exact hLeft.sub hRight

private def shiJoinedPreDomain
    (D : LeviCivitaData g) (c cL cR : OpenPartialHomeomorph M E)
    (a b : ℝ) : Set (Data × E) :=
  {q | shiJoinedBase c cL cR q.1 ∧
    shiRawCoordinateVariation D cL a (joinedYL q.1) (joinedQL q.1) q.2 ∈
      (cL.target ∩ cL.symm ⁻¹' c.source) ∧
    shiRawCoordinateVariation D cR b (joinedYR q.1) (joinedQR q.1) q.2 ∈
      (cR.target ∩ cR.symm ⁻¹' c.source)}

private theorem joinedPreDomain_isOpen [T2Space M]
    (D : LeviCivitaData g) {c cL cR : OpenPartialHomeomorph M E}
    (hl : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cL cL.source)
    (hli : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cL.symm cL.target)
    (hr : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cR cR.source)
    (hri : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cR.symm cR.target)
    (a b : ℝ) : IsOpen (shiJoinedPreDomain D c cL cR a b) := by
  let O0 : Set (Data × E) := {q | shiJoinedBase c cL cR q.1}
  let rL : Data × E → E :=
    fun q => shiRawCoordinateVariation D cL a (joinedYL q.1) (joinedQL q.1) q.2
  let rR : Data × E → E :=
    fun q => shiRawCoordinateVariation D cR b (joinedYR q.1) (joinedQR q.1) q.2
  have hO0 : IsOpen O0 := shiJoinedBase_isOpen.preimage continuous_fst
  have hL : ContDiffOn ℝ ∞ rL O0 := by
    intro q hq
    exact (joinedRaw_contDiffAt D hl hli (s := fun _ => a) contDiffAt_const
      ((joinedYL_contDiff.comp contDiff_fst).contDiffAt)
      ((joinedQL_contDiff.comp contDiff_fst).contDiffAt)
      contDiffAt_snd hq.2.1.1).contDiffWithinAt
  have hR : ContDiffOn ℝ ∞ rR O0 := by
    intro q hq
    exact (joinedRaw_contDiffAt D hr hri (s := fun _ => b) contDiffAt_const
      ((joinedYR_contDiff.comp contDiff_fst).contDiffAt)
      ((joinedQR_contDiff.comp contDiff_fst).contDiffAt)
      contDiffAt_snd hq.2.2.1).contDiffWithinAt
  have hOL := hL.continuousOn.isOpen_inter_preimage hO0
    (cL.isOpen_inter_preimage_symm c.open_source)
  have hO := (hR.continuousOn.mono inter_subset_left).isOpen_inter_preimage hOL
    (cR.isOpen_inter_preimage_symm c.open_source)
  have hset : shiJoinedPreDomain D c cL cR a b =
      O0 ∩ rL ⁻¹' (cL.target ∩ cL.symm ⁻¹' c.source) ∩
        rR ⁻¹' (cR.target ∩ cR.symm ⁻¹' c.source) := by
    ext q
    simp only [shiJoinedPreDomain, O0, rL, rR, mem_setOf_eq, mem_inter_iff,
      mem_preimage, and_assoc]
  rw [hset]
  exact hO

private theorem joinedPosition_contDiffAt [T2Space M]
    (D : LeviCivitaData g) {c cL cR : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hl : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cL cL.source)
    (hli : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cL.symm cL.target)
    (hr : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cR cR.source)
    (hri : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cR.symm cR.target)
    (a b : ℝ) {q : Data × E} (hq : q ∈ shiJoinedPreDomain D c cL cR a b) :
    ContDiffAt ℝ ∞ (fun r : Data × E => shiJoinedPosition D c cL cR a b r.1 r.2) q := by
  have ht : ContDiffAt ℝ ∞ (fun r : Data × E => joinedTime r.1) q :=
    (joinedTime_contDiff.comp contDiff_fst).contDiffAt
  have hX : ContDiffAt ℝ ∞ (fun r : Data × E => joinedX r.1) q :=
    (joinedX_contDiff.comp contDiff_fst).contDiffAt
  have hP : ContDiffAt ℝ ∞ (fun r : Data × E => joinedP r.1) q :=
    (joinedP_contDiff.comp contDiff_fst).contDiffAt
  have hYL : ContDiffAt ℝ ∞ (fun r : Data × E => joinedYL r.1) q :=
    (joinedYL_contDiff.comp contDiff_fst).contDiffAt
  have hQL : ContDiffAt ℝ ∞ (fun r : Data × E => joinedQL r.1) q :=
    (joinedQL_contDiff.comp contDiff_fst).contDiffAt
  have hYR : ContDiffAt ℝ ∞ (fun r : Data × E => joinedYR r.1) q :=
    (joinedYR_contDiff.comp contDiff_fst).contDiffAt
  have hQR : ContDiffAt ℝ ∞ (fun r : Data × E => joinedQR r.1) q :=
    (joinedQR_contDiff.comp contDiff_fst).contDiffAt
  have hRaw := joinedRaw_contDiffAt D hc hi ht hX hP contDiffAt_snd hq.1.1
  have hLeft := joinedEndpoint_contDiffAt D hc hi hl hli a hYL hQL
    contDiffAt_snd hq.1.2.1 hq.2.1
  have hRight := joinedEndpoint_contDiffAt D hc hi hr hri b hYR hQR
    contDiffAt_snd hq.1.2.2 hq.2.2
  have hla : ContDiffAt ℝ ∞ (fun r : Data × E => (b - joinedTime r.1) / (b - a)) q :=
    (contDiffAt_const.sub ht).div_const (b - a)
  have hra : ContDiffAt ℝ ∞ (fun r : Data × E => (joinedTime r.1 - a) / (b - a)) q :=
    (ht.sub contDiffAt_const).div_const (b - a)
  exact (hRaw.add (hla.smul hLeft)).add (hra.smul hRight)

theorem shiJoinedDomain_isOpen [T2Space M]
    (D : LeviCivitaData g) {c cL cR : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hl : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cL cL.source)
    (hli : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cL.symm cL.target)
    (hr : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cR cR.source)
    (hri : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cR.symm cR.target)
    (a b : ℝ) : IsOpen (shiJoinedDomain D c cL cR a b) := by
  have hF : ContDiffOn ℝ ∞
      (fun q : Data × E => shiJoinedPosition D c cL cR a b q.1 q.2)
      (shiJoinedPreDomain D c cL cR a b) := by
    intro q hq
    exact (joinedPosition_contDiffAt D hc hi hl hli hr hri a b hq).contDiffWithinAt
  have hO := hF.continuousOn.isOpen_inter_preimage
    (joinedPreDomain_isOpen D hl hli hr hri a b) c.open_target
  have hset : shiJoinedDomain D c cL cR a b =
      shiJoinedPreDomain D c cL cR a b ∩
        (fun q : Data × E => shiJoinedPosition D c cL cR a b q.1 q.2) ⁻¹'
          c.target := by
    ext q
    simp only [shiJoinedDomain, shiJoinedPreDomain, mem_setOf_eq, mem_inter_iff,
      mem_preimage, and_assoc]
  rw [hset]
  exact hO

theorem shiJoinedPosition_contDiffOn [T2Space M]
    (D : LeviCivitaData g) {c cL cR : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hl : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cL cL.source)
    (hli : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cL.symm cL.target)
    (hr : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cR cR.source)
    (hri : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cR.symm cR.target)
    (a b : ℝ) :
    ContDiffOn ℝ ∞ (fun q : Data × E => shiJoinedPosition D c cL cR a b q.1 q.2)
      (shiJoinedDomain D c cL cR a b) := by
  intro q hq
  exact (joinedPosition_contDiffAt D hc hi hl hli hr hri a b
    ⟨hq.1, hq.2.1, hq.2.2.1⟩).contDiffWithinAt

set_option synthInstance.maxHeartbeats 100000 in

private theorem joinedVelocity_contDiffAt [T2Space M]
    (D : LeviCivitaData g) {c cL cR : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hl : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cL cL.source)
    (hli : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cL.symm cL.target)
    (hr : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cR cR.source)
    (hri : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cR.symm cR.target)
    (a b : ℝ) {q : Data × E} (hq : q ∈ shiJoinedPreDomain D c cL cR a b) :
    ContDiffAt ℝ ∞ (fun r : Data × E => shiJoinedVelocity D c cL cR a b r.1 r.2) q := by
  have ht : ContDiffAt ℝ ∞ (fun r : Data × E => joinedTime r.1) q :=
    (joinedTime_contDiff.comp contDiff_fst).contDiffAt
  have hX : ContDiffAt ℝ ∞ (fun r : Data × E => joinedX r.1) q :=
    (joinedX_contDiff.comp contDiff_fst).contDiffAt
  have hT : ContDiffAt ℝ ∞ (fun r : Data × E => joinedT r.1) q :=
    (joinedT_contDiff.comp contDiff_fst).contDiffAt
  have hP : ContDiffAt ℝ ∞ (fun r : Data × E => joinedP r.1) q :=
    (joinedP_contDiff.comp contDiff_fst).contDiffAt
  have hYL : ContDiffAt ℝ ∞ (fun r : Data × E => joinedYL r.1) q :=
    (joinedYL_contDiff.comp contDiff_fst).contDiffAt
  have hQL : ContDiffAt ℝ ∞ (fun r : Data × E => joinedQL r.1) q :=
    (joinedQL_contDiff.comp contDiff_fst).contDiffAt
  have hYR : ContDiffAt ℝ ∞ (fun r : Data × E => joinedYR r.1) q :=
    (joinedYR_contDiff.comp contDiff_fst).contDiffAt
  have hQR : ContDiffAt ℝ ∞ (fun r : Data × E => joinedQR r.1) q :=
    (joinedQR_contDiff.comp contDiff_fst).contDiffAt
  have hGammaAt := (shiChartChristoffel_smooth D hc hi).contDiffAt
    (c.open_target.mem_nhds hq.1.1)
  have hGamma := hGammaAt.comp q hX
  have hDGamma := (hGammaAt.fderiv_right (m := ∞) (by simp)).comp q hX
  have hPz : ContDiffAt ℝ ∞ (fun r : Data × E => joinedP r.1 r.2) q :=
    hP.clm_apply contDiffAt_snd
  have hA := ht.smul hPz
  have hJ := hPz.sub ((hGamma.clm_apply hT).clm_apply hA)
  have hG1 := ((hDGamma.clm_apply hT).clm_apply hA).clm_apply hA
  have hG2 := (hGamma.clm_apply hJ).clm_apply hA
  have hG3 := (hGamma.clm_apply hA).clm_apply hJ
  have hLeft := joinedEndpoint_contDiffAt D hc hi hl hli a hYL hQL
    contDiffAt_snd hq.1.2.1 hq.2.1
  have hRight := joinedEndpoint_contDiffAt D hc hi hr hri b hYR hQR
    contDiffAt_snd hq.1.2.2 hq.2.2
  exact ((hT.add hJ).sub (((hG1.add hG2).add hG3).const_smul (1 / 2 : ℝ))).add
    ((hRight.sub hLeft).const_smul (b - a)⁻¹)

theorem shiJoinedVelocity_contDiffOn [T2Space M]
    (D : LeviCivitaData g) {c cL cR : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hl : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cL cL.source)
    (hli : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cL.symm cL.target)
    (hr : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cR cR.source)
    (hri : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cR.symm cR.target)
    (a b : ℝ) :
    ContDiffOn ℝ ∞ (fun q : Data × E => shiJoinedVelocity D c cL cR a b q.1 q.2)
      (shiJoinedDomain D c cL cR a b) := by
  intro q hq
  exact (joinedVelocity_contDiffAt D hc hi hl hli hr hri a b
    ⟨hq.1, hq.2.1, hq.2.2.1⟩).contDiffWithinAt

theorem shiJoinedDensity_contDiffOn [T2Space M]
    (D : LeviCivitaData g) {c cL cR : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hl : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cL cL.source)
    (hli : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cL.symm cL.target)
    (hr : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cR cR.source)
    (hri : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cR.symm cR.target)
    (a b : ℝ) :
    ContDiffOn ℝ ∞ (fun q : Data × E => shiJoinedDensity g D c cL cR a b q.1 q.2)
      (shiJoinedDomain D c cL cR a b) := by
  have hF := shiJoinedPosition_contDiffOn D hc hi hl hli hr hri a b
  have hW := shiJoinedVelocity_contDiffOn D hc hi hl hli hr hri a b
  have hG := (shiChartMetric_smooth g hc hi).comp hF (fun _ h => h.2.2.2)
  exact (hG.clm_apply hW).clm_apply hW

@[simp] theorem shiRawCoordinateVariation_zero
    (D : LeviCivitaData g) (c : OpenPartialHomeomorph M E)
    (s : ℝ) (y : E) (Q : End) :
    shiRawCoordinateVariation D c s y Q 0 = y := by
  simp [shiRawCoordinateVariation]

@[simp] theorem shiJoinedDiscrepancy_zero
    (D : LeviCivitaData g) (c k : OpenPartialHomeomorph M E)
    (s : ℝ) (y : E) (Q : End) :
    shiJoinedDiscrepancy D c k s y Q 0 = 0 := by
  simp [shiJoinedDiscrepancy, shiJoinedRawEndpoint, shiJoinedTransition]

@[simp] theorem shiJoinedPosition_zero
    (D : LeviCivitaData g) (c cL cR : OpenPartialHomeomorph M E)
    (a b : ℝ) (p : Data) :
    shiJoinedPosition D c cL cR a b p 0 = joinedX p := by
  simp [shiJoinedPosition]

@[simp] theorem shiJoinedVelocity_zero
    (D : LeviCivitaData g) (c cL cR : OpenPartialHomeomorph M E)
    (a b : ℝ) (p : Data) :
    shiJoinedVelocity D c cL cR a b p 0 = joinedT p := by
  simp [shiJoinedVelocity, shiJoinedJ, shiJoinedA]

@[simp] theorem shiJoinedDensity_zero
    (D : LeviCivitaData g) (c cL cR : OpenPartialHomeomorph M E)
    (a b : ℝ) (p : Data) :
    shiJoinedDensity g D c cL cR a b p 0 =
      shiChartMetric g c (joinedX p) (joinedT p) (joinedT p) := by
  simp [shiJoinedDensity]

theorem shiJoinedDomain_zero
    (D : LeviCivitaData g) (c cL cR : OpenPartialHomeomorph M E)
    (a b : ℝ) {p : Data} (hp : shiJoinedBase c cL cR p) :
    (p, (0 : E)) ∈ shiJoinedDomain D c cL cR a b := by
  refine ⟨hp, ?_, ?_, ?_⟩
  · simpa only [shiRawCoordinateVariation_zero] using hp.2.1
  · simpa only [shiRawCoordinateVariation_zero] using hp.2.2
  · simpa only [shiJoinedPosition_zero] using hp.1

theorem shiJoinedDensity_nonneg
    (D : LeviCivitaData g) {c cL cR : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (a b : ℝ) {q : Data × E} (hq : q ∈ shiJoinedDomain D c cL cR a b) :
    0 ≤ shiJoinedDensity g D c cL cR a b q.1 q.2 := by
  by_cases hW : shiJoinedVelocity D c cL cR a b q.1 q.2 = 0
  · simp only [shiJoinedDensity, hW, map_zero, zero_apply, le_refl]
  · exact (shiChartMetric_pos g hc hi hq.2.2.2 hW).le

def shiJoinedCompactTuples (a b L R : ℝ) (H HL HR : Set E) : Set Data :=
  Icc a b ×ˢ
    ((H ×ˢ (Metric.closedBall (0 : E) (L * R) ×ˢ Metric.closedBall (0 : End) L)) ×ˢ
      ((HL ×ˢ Metric.closedBall (0 : End) L) ×ˢ
        (HR ×ˢ Metric.closedBall (0 : End) L)))

theorem shiJoinedCompactTuples_isCompact (a b L R : ℝ)
    {H HL HR : Set E} (hH : IsCompact H) (hHL : IsCompact HL) (hHR : IsCompact HR) :
    IsCompact (shiJoinedCompactTuples a b L R H HL HR) :=
  isCompact_Icc.prod ((hH.prod ((isCompact_closedBall _ _).prod
    (isCompact_closedBall _ _))).prod
      ((hHL.prod (isCompact_closedBall _ _)).prod
        (hHR.prod (isCompact_closedBall _ _))))

theorem shiJoinedCompactTuples_subset_base
    {c cL cR : OpenPartialHomeomorph M E} (a b L R : ℝ)
    {H HL HR : Set E} (hH : H ⊆ c.target)
    (hHL : HL ⊆ cL.target ∩ cL.symm ⁻¹' c.source)
    (hHR : HR ⊆ cR.target ∩ cR.symm ⁻¹' c.source) :
    shiJoinedCompactTuples a b L R H HL HR ⊆ shiJoinedBaseSet c cL cR := by
  intro p hp
  exact ⟨hH hp.2.1.1, hHL hp.2.2.1.1, hHR hp.2.2.2.1⟩

theorem exists_shiJoinedDensity_uniform_bound [T2Space M]
    (D : LeviCivitaData g) {c cL cR : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hl : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cL cL.source)
    (hli : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cL.symm cL.target)
    (hr : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cR cR.source)
    (hri : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cR.symm cR.target)
    (a b L R : ℝ) (_hab : a < b) (_hL : 1 ≤ L) (_hR : 0 ≤ R)
    {H HL HR : Set E} (hH : IsCompact H) (hHL : IsCompact HL) (hHR : IsCompact HR)
    (hHt : H ⊆ c.target)
    (hHLt : HL ⊆ cL.target ∩ cL.symm ⁻¹' c.source)
    (hHRt : HR ⊆ cR.target ∩ cR.symm ⁻¹' c.source) :
    ∃ ρ B : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ 1 ≤ B ∧
      shiJoinedCompactTuples a b L R H HL HR ×ˢ Metric.closedBall (0 : E) ρ ⊆
        shiJoinedDomain D c cL cR a b ∧
      ∀ p ∈ shiJoinedCompactTuples a b L R H HL HR,
        ‖fderiv ℝ (shiJoinedDensity g D c cL cR a b p) 0‖ ≤ B ∧
        ‖fderiv ℝ (fderiv ℝ (shiJoinedDensity g D c cL cR a b p)) 0‖ ≤ B ∧
        (∀ v w,
          fderiv ℝ (fderiv ℝ (shiJoinedDensity g D c cL cR a b p)) 0 v w =
          fderiv ℝ (fderiv ℝ (shiJoinedDensity g D c cL cR a b p)) 0 w v) ∧
        ∀ z, ‖z‖ ≤ ρ →
          |shiJoinedDensity g D c cL cR a b p z -
              shiJoinedDensity g D c cL cR a b p 0 -
              fderiv ℝ (shiJoinedDensity g D c cL cR a b p) 0 z -
              fderiv ℝ (fderiv ℝ (shiJoinedDensity g D c cL cR a b p)) 0 z z / 2| ≤
            B * ‖z‖ ^ 3 := by
  exact exists_uniform_quadratic_taylor_bound
    (shiJoinedCompactTuples a b L R H HL HR)
    (shiJoinedCompactTuples_isCompact a b L R hH hHL hHR)
    (shiJoinedDomain D c cL cR a b)
    (shiJoinedDomain_isOpen D hc hi hl hli hr hri a b)
    (fun q : Data × E => shiJoinedDensity g D c cL cR a b q.1 q.2)
    ((shiJoinedDensity_contDiffOn D hc hi hl hli hr hri a b).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 3))
    (fun p hp => shiJoinedDomain_zero D c cL cR a b
      (shiJoinedCompactTuples_subset_base a b L R hHt hHLt hHRt hp))

private theorem partial_fderiv_contDiffOn
    {P V Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {O : Set (P × V)} (hO : IsOpen O) {f : P × V → Y}
    (hf : ContDiffOn ℝ ∞ f O) :
    ContDiffOn ℝ ∞ (fun q : P × V => fderiv ℝ (fun z => f (q.1, z)) q.2) O := by
  intro q hq
  have hpull : ContDiffAt ℝ ∞
      (fun r : (P × V) × V => f (r.1.1, r.2)) (q, q.2) := by
    exact (hf.contDiffAt (hO.mem_nhds hq)).comp (q, q.2)
      (contDiffAt_fst.fst.prodMk contDiffAt_snd)
  exact (hpull.fderiv (m := ∞) contDiffAt_snd (by simp)).contDiffWithinAt

theorem shiJoinedDensity_jet_continuousOn [T2Space M]
    (D : LeviCivitaData g) {c cL cR : OpenPartialHomeomorph M E}
    (hc : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ c c.source)
    (hi : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ c.symm c.target)
    (hl : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cL cL.source)
    (hli : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cL.symm cL.target)
    (hr : ContMDiffOn (𝓡 n) 𝓘(ℝ, E) ∞ cR cR.source)
    (hri : ContMDiffOn 𝓘(ℝ, E) (𝓡 n) ∞ cR.symm cR.target)
    (a b : ℝ) :
    ContinuousOn
      (fun p : Data => fderiv ℝ (shiJoinedDensity g D c cL cR a b p) 0)
      (shiJoinedBaseSet c cL cR) ∧
    ContinuousOn
      (fun p : Data => fderiv ℝ (fderiv ℝ (shiJoinedDensity g D c cL cR a b p)) 0)
      (shiJoinedBaseSet c cL cR) := by
  let O := shiJoinedDomain D c cL cR a b
  let e : Data × E → ℝ := fun q => shiJoinedDensity g D c cL cR a b q.1 q.2
  have hO : IsOpen O := shiJoinedDomain_isOpen D hc hi hl hli hr hri a b
  have he : ContDiffOn ℝ ∞ e O := shiJoinedDensity_contDiffOn D hc hi hl hli hr hri a b
  have h1 := partial_fderiv_contDiffOn hO he
  have h2 := partial_fderiv_contDiffOn hO h1
  constructor
  · intro p hp
    have hzero : (p, (0 : E)) ∈ O := shiJoinedDomain_zero D c cL cR a b hp
    have hs : ContDiffAt ℝ ∞ (fun r : Data => (r, (0 : E))) p :=
      contDiffAt_id.prodMk contDiffAt_const
    exact (((h1.contDiffAt (hO.mem_nhds hzero)).comp p hs).continuousAt).continuousWithinAt
  · intro p hp
    have hzero : (p, (0 : E)) ∈ O := shiJoinedDomain_zero D c cL cR a b hp
    have hs : ContDiffAt ℝ ∞ (fun r : Data => (r, (0 : E))) p :=
      contDiffAt_id.prodMk contDiffAt_const
    exact (((h2.contDiffAt (hO.mem_nhds hzero)).comp p hs).continuousAt).continuousWithinAt

theorem shiJoinedCore_coordinate_sets [T2Space M]
    (c cL cR : OpenPartialHomeomorph M E) {C CL CR : Set M}
    (hC : IsCompact C) (hCL : IsCompact CL) (hCR : IsCompact CR)
    (hCs : C ⊆ c.source) (hCLs : CL ⊆ cL.source) (hCRs : CR ⊆ cR.source) :
    IsCompact (c '' C) ∧
      IsCompact (cL '' (C ∩ CL)) ∧ IsCompact (cR '' (C ∩ CR)) ∧
      c '' C ⊆ c.target ∧
      cL '' (C ∩ CL) ⊆ cL.target ∩ cL.symm ⁻¹' c.source ∧
      cR '' (C ∩ CR) ⊆ cR.target ∩ cR.symm ⁻¹' c.source := by
  have hL : C ∩ CL ⊆ cL.source := fun _ h => hCLs h.2
  have hR : C ∩ CR ⊆ cR.source := fun _ h => hCRs h.2
  refine ⟨hC.image_of_continuousOn (c.continuousOn.mono hCs),
    (hC.inter_right hCL.isClosed).image_of_continuousOn (cL.continuousOn.mono hL),
    (hC.inter_right hCR.isClosed).image_of_continuousOn (cR.continuousOn.mono hR),
    ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact c.map_source (hCs hx)
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨cL.map_source (hCLs hx.2), ?_⟩
    change cL.symm (cL x) ∈ c.source
    rw [cL.left_inv (hCLs hx.2)]
    exact hCs hx.1
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨cR.map_source (hCRs hx.2), ?_⟩
    change cR.symm (cR x) ∈ c.source
    rw [cR.left_inv (hCRs hx.2)]
    exact hCs hx.1

end PoincareConjecture.RicciFlowAnalysis
