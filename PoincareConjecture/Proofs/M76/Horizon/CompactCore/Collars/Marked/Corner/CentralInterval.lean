import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.Marked.Coordinates.Rim
import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductSlices
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart

set_option autoImplicit false

open Set Metric Geometry Topology

namespace PoincareConjecture.M76

open Dehn.Annuli.RimBands

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Disk" => closedBall (0 : V2) 1
local notation "Rim" => sphere (0 : V2) 1
local notation "J" => Icc (0 : ℝ) 1

theorem OriginalDiskProduct.exists_corner_central_interval
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {R D T : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e R j) (H : Rim ≃ₜ Rim)
    {h : V2 → V2} (hhPL : FinitePiecewiseAffineOn h Rim)
    (hh : ∀ z : Rim, (H z : V2) = h z) (side : Bool)
    {y : X} (B : OriginalSurfacePairChart e D T y true)
    (hcenter : j (h (armPoint side (1 / 2))) = y) :
    ∃ a b : ℝ, 0 < a ∧ a < 1 / 2 ∧ 1 / 2 < b ∧ b < 1 ∧
      PolyhedralPLInCharts e (j ∘ h ∘ armPoint side) (Icc a b) ∧
      InjOn (j ∘ h ∘ armPoint side) (Icc a b) ∧
      MapsTo (j ∘ h ∘ armPoint side) (Icc a b) B.chart.source ∧
      MapsTo (B.chart ∘ (j ∘ h ∘ armPoint side)) (Icc a b) B.coordinates.source := by
  have hj : PolyhedralPLInCharts e j Disk :=
    (P.polyhedral_slice (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by norm_num)).congr
      (fun z hz => P.central z hz)
  have hji : InjOn j Disk := by
    intro z hz w hw heq
    have heq' : P.map (z, 0) = P.map (w, 0) := by
      rw [P.central z hz, P.central w hw]
      exact heq
    exact congrArg Prod.fst (P.injective ⟨hz, by norm_num⟩ ⟨hw, by norm_num⟩ heq')
  have harm (s) (hs : s ∈ J) : armPoint side s ∈ Rim :=
    (armPoint_mem side ⟨by linarith [hs.1], by linarith [hs.2]⟩).1
  have hmap (s) (hs : s ∈ J) : h (armPoint side s) ∈ Disk :=
    sphere_subset_closedBall (hh ⟨_, harm s hs⟩ ▸ (H ⟨_, harm s hs⟩).property)
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K, hK, hKs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show (0 : ℝ) < 1 by norm_num)
  have hid : FinitePiecewiseAffineOn (id : ℝ → ℝ) J :=
    ⟨K, hK, hKs, K.affineOnFaces_affine (ContinuousAffineMap.id ℝ ℝ)⟩
  have hcoord : FinitePiecewiseAffineOn (h ∘ armPoint side) J :=
    hhPL.comp (finitePL_armPoint hid side) harm
  have hp : PolyhedralPLInCharts e (j ∘ h ∘ armPoint side) J :=
    hKs ▸ hj.comp_finitePiecewiseAffineOn K hK (hKs.symm ▸ hcoord)
      (fun s hs => hmap s (hKs.subset hs))
  have hpi : InjOn (j ∘ h ∘ armPoint side) J := by
    intro s hs t ht heq
    have hhst := hji (hmap s hs) (hmap t ht) heq
    have hHst : H ⟨_, harm s hs⟩ = H ⟨_, harm t ht⟩ := by
      apply Subtype.ext
      exact (hh ⟨_, harm s hs⟩).trans (hhst.trans (hh ⟨_, harm t ht⟩).symm)
    have harmeq := congrArg Subtype.val (H.injective hHst)
    have hphase := congrArg (armPhase side) harmeq
    simpa only [armPoint_eq_rimArm side hs, armPoint_eq_rimArm side ht,
      armPhase_rimArm side hs, armPhase_rimArm side ht] using hphase
  let O := B.chart.source ∩ B.chart ⁻¹' B.coordinates.source
  have hO : IsOpen O := B.chart.isOpen_inter_preimage B.coordinates.open_source
  have hpoint : (j ∘ h ∘ armPoint side) (1 / 2) ∈ O := by
    change j (h (armPoint side (1 / 2))) ∈ O
    rw [hcenter]
    exact ⟨B.center_source, B.center_coordinates⟩
  have hcont : ContinuousAt (j ∘ h ∘ armPoint side) (1 / 2) :=
    hp.continuousOn.continuousAt (Icc_mem_nhds (by norm_num) (by norm_num))
  have hpre : (j ∘ h ∘ armPoint side) ⁻¹' O ∈ 𝓝 (1 / 2 : ℝ) :=
    hcont (hO.mem_nhds hpoint)
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp hpre
  let d := min (ε / 2) (1 / 4)
  have hd : 0 < d := lt_min (by positivity) (by norm_num)
  have hds : d ≤ 1 / 4 := min_le_right _ _
  have hdε : d < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  let a := 1 / 2 - d
  let b := 1 / 2 + d
  have hsub : Icc a b ⊆ J := by
    intro s hs
    dsimp [a, b] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hcharts : MapsTo (j ∘ h ∘ armPoint side) (Icc a b) O := by
    intro s hs
    apply hεsub
    rw [mem_ball, Real.dist_eq, abs_lt]
    dsimp [a, b] at hs
    exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨L, hL, hLs, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_Icc (show a < b by dsimp [a, b]; linarith)
  refine ⟨a, b, ?_, ?_, ?_, ?_, ?_, hpi.mono hsub,
    fun s hs => (hcharts hs).1, fun s hs => (hcharts hs).2⟩
  all_goals try { dsimp [a, b]; linarith }
  exact hLs ▸ hp.restrict_finite L hL (hLs.subset.trans hsub)

end PoincareConjecture.M76
