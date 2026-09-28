import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.PolygonalParameter
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.RoundedVertexPath
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Rounding.SmoothAbsolute
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Coordinates.PeriodicInjection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.LocalSides
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Polygon.OppositeCoordinate

set_option autoImplicit false

open Set Function Filter
open scoped Topology ContDiff

namespace Poincare.Manifold.Schoenflies.Plane

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {n : ℕ}

theorem IsSimplePolygon.exists_positive_corner_functional [NeZero n] [FiniteDimensional ℝ E]
    {p : Polygon E n} (hp : IsSimplePolygon p) (k : Fin n) :
    ∃ ℓ : E →L[ℝ] ℝ, 0 < ℓ (p k - p ((finRotate n).symm k)) ∧
      0 < ℓ (p (finRotate n k) - p k) := by
  let j := (finRotate n).symm k
  have hjk : finRotate n j = k := (finRotate n).apply_symm_apply k
  have ha : p j ≠ p k := by simpa only [hjk] using hp.hasNondegenerateEdges j
  have hb : p (finRotate n k) ≠ p k := (hp.hasNondegenerateEdges k).symm
  have hne : j ≠ k := fun h => ha (congrArg p h)
  have hneighbors : j ≠ finRotate n k := finRotate_symm_ne_apply_of_three_le hp.three_le k
  have hsegj : segment ℝ (p k) (p j) = p.edgeSet ℝ j := by
    rw [polygon_edgeSet_eq_segment, hjk, segment_symm]
  have hsegk : segment ℝ (p k) (p (finRotate n k)) = p.edgeSet ℝ k :=
    (polygon_edgeSet_eq_segment p k).symm
  have hinter : segment ℝ (p k) (p j) ∩ segment ℝ (p k) (p (finRotate n k)) ⊆ {p k} := by
    rw [hsegj, hsegk]
    intro x hx
    have hends := hp.edges_inter j k hne hx
    rw [hjk] at hends
    rcases hends.1 with hj | hk
    · rcases hends.2 with hk | hl
      · exact hk
      · exact False.elim (hneighbors (hp.vertices_injective (hj.symm.trans hl)))
    · exact hk
  obtain ⟨X, hneg, hpos⟩ := exists_linearMap_neg_pos_of_not_sameRay
    (not_sameRay_sub_of_segments_inter_subset_singleton ha hb hinter)
  refine ⟨X.toContinuousLinearMap, ?_, hpos⟩
  change 0 < X (p k - p j)
  have heq : X (p k - p j) = -X (p j - p k) := by simp only [map_sub]; ring
  rw [heq]
  exact neg_pos.mpr hneg

variable [NeZero n]

noncomputable def roundedPolygonParameter (ρ : ℝ → ℝ) (p : Polygon E n) : ℝ → E :=
  roundedVertexPath ρ (fun j => p (polygonIntegerIndex n j))

theorem periodic_roundedPolygonParameter (ρ : ℝ → ℝ) (p : Polygon E n) :
    Periodic (roundedPolygonParameter ρ p) (n : ℝ) := by
  exact periodic_roundedVertexPath ρ (fun j => p (polygonIntegerIndex n j)) (n : ℤ)
    (fun j => congrArg p (polygonIntegerIndex_add_period j))

theorem contDiff_roundedPolygonParameter {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {p : V → Polygon E n} {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : ContDiff ℝ ∞ ρ) (hp : ∀ i, ContDiff ℝ ∞ (fun z => p z i)) :
    ContDiff ℝ ∞ (fun x : V × ℝ => roundedPolygonParameter ρ (p x.1) x.2) :=
  contDiff_roundedVertexPath hδ hδhalf htail hbound hρ (fun j => hp (polygonIntegerIndex n j))

theorem dist_roundedPolygonParameter_le (p : Polygon E n) {ρ : ℝ → ℝ} {δ B : ℝ}
    (hδ : 0 < δ) (hδhalf : δ < 1 / 2)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hB : ∀ i, ‖p i‖ ≤ B) (t : ℝ) :
    dist (roundedPolygonParameter ρ p t) (polygonLinearParameter p t) ≤ 2 * δ * B := by
  let i : ℤ := ⌊t + 1 / 2⌋
  let P : ℤ → E := fun j => p (polygonIntegerIndex n j)
  have hlo : (i : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hhi : t + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
  have ht : t ∈ Ioo ((i : ℝ) - 1) ((i : ℝ) + 1) := by constructor <;> linarith
  have hnorm : ‖(P (i + 1) - P i) - (P i - P (i - 1))‖ ≤ 4 * B := by
    have hn := norm_sub_le (P (i + 1) - P i) (P i - P (i - 1))
    have h1 := norm_sub_le (P (i + 1)) (P i)
    have h2 := norm_sub_le (P i) (P (i - 1))
    have hB' (j : ℤ) : ‖P j‖ ≤ B := hB (polygonIntegerIndex n j)
    linarith [hB' (i + 1), hB' i, hB' (i - 1)]
  change dist (roundedCorner ρ (P i) (P i - P (i - 1)) (P (i + 1) - P i) (t - i))
    (polygonLinearParameter p t) ≤ _
  rw [polygonLinearParameter_eq_corner p i ht]
  have hpiece : roundedCorner abs (P i) (P i - P (i - 1)) (P (i + 1) - P i) (t - i) =
      (if t - (i : ℝ) ≤ 0 then P i + (t - i) • (P i - P (i - 1))
      else P i + (t - i) • (P (i + 1) - P i)) := by
    by_cases hs : t - (i : ℝ) ≤ 0
    · rw [if_pos hs, roundedCorner, abs_of_nonpos hs]
      module
    · rw [if_neg hs, roundedCorner, abs_of_pos (lt_of_not_ge hs)]
      module
  change dist _ (roundedCorner abs (P i) (P i - P (i - 1)) (P (i + 1) - P i) (t - i)) ≤ _
  rw [hpiece]
  exact ((roundedCorner_tail_bounds _ _ _ hδ htail hbound).2.2 (t - i)).trans (by nlinarith)

theorem IsSimplePolygon.roundedPolygonParameter_regular [FiniteDimensional ℝ E]
    {p : Polygon E n} (hp : IsSimplePolygon p) {ρ : ℝ → ℝ} {δ : ℝ}
    (hδ : 0 < δ) (hδquarter : δ < 1 / 4)
    (htail : ∀ s, δ ≤ |s| → ρ s = |s|)
    (hbound : ∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ)
    (hρ : Differentiable ℝ ρ) (hder : ∀ s, |deriv ρ s| ≤ 1) :
    (∀ s t : ℝ, |s - t| < 1 / 4 →
      roundedPolygonParameter ρ p s = roundedPolygonParameter ρ p t → s = t) ∧
    ∀ t : ℝ, deriv (roundedPolygonParameter ρ p) t ≠ 0 := by
  let P : ℤ → E := fun j => p (polygonIntegerIndex n j)
  have hhalf : δ < 1 / 2 := by linarith
  have hcoord (i : ℤ) : ∃ ℓ : E →L[ℝ] ℝ,
      0 < ℓ (P i - P (i - 1)) ∧ 0 < ℓ (P (i + 1) - P i) := by
    obtain ⟨ℓ, hl, hr⟩ := hp.exists_positive_corner_functional (polygonIntegerIndex n i)
    have hprev : polygonIntegerIndex n (i - 1) =
        (finRotate n).symm (polygonIntegerIndex n i) := by
      apply (finRotate n).injective
      rw [← polygonIntegerIndex_succ, sub_add_cancel, Equiv.apply_symm_apply]
    refine ⟨ℓ, ?_, ?_⟩
    · simpa only [P, hprev] using hl
    · simpa only [P, polygonIntegerIndex_succ] using hr
  constructor
  · intro s t hst heq
    let i : ℤ := ⌊s + 1 / 2⌋
    have hlo : (i : ℝ) ≤ s + 1 / 2 := Int.floor_le _
    have hhi : s + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
    rcases abs_lt.mp hst with ⟨hstlo, hsthi⟩
    have hs : s ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ) := by
      constructor <;> linarith
    have ht : t ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ) := by
      constructor <;> linarith
    obtain ⟨ℓ, hu, hv⟩ := hcoord i
    have hinj := (strictMono_roundedCorner_projection (P i) (P i - P (i - 1))
      (P (i + 1) - P i) hρ hder ℓ hu hv).2.2
    have hsEq := roundedVertexPath_eq_local P hδ hhalf htail hbound i hs
    have htEq := roundedVertexPath_eq_local P hδ hhalf htail hbound i ht
    have hparam : s - (i : ℝ) = t - i := hinj (by
      rw [← hsEq, ← htEq]
      exact heq)
    linarith
  · intro t
    let i : ℤ := ⌊t + 1 / 2⌋
    have hlo : (i : ℝ) ≤ t + 1 / 2 := Int.floor_le _
    have hhi : t + 1 / 2 < (i : ℝ) + 1 := Int.lt_floor_add_one _
    have ht : t ∈ Ioo ((i : ℝ) - 1 + δ) ((i : ℝ) + 1 - δ) := by
      constructor <;> linarith
    obtain ⟨ℓ, hu, hv⟩ := hcoord i
    let Γ := roundedCorner ρ (P i) (P i - P (i - 1)) (P (i + 1) - P i)
    have hΓ := hasDerivAt_roundedCorner (P i) (P i - P (i - 1))
      (P (i + 1) - P i) (hρ (t - i))
    have hΓ' : HasDerivAt Γ (deriv Γ (t - i)) (t - i) := hΓ.congr_deriv hΓ.deriv.symm
    have htrans : HasDerivAt (fun s : ℝ => Γ (s - i)) (deriv Γ (t - i)) t := by
      simpa only [Function.comp_def, one_smul, id_eq] using
        hΓ'.scomp t ((hasDerivAt_id t).sub_const (i : ℝ))
    have hactual : HasDerivAt (roundedPolygonParameter ρ p) (deriv Γ (t - i)) t := by
      apply htrans.congr_of_eventuallyEq
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact roundedVertexPath_eq_local P hδ hhalf htail hbound i hs
    rw [hactual.deriv]
    intro hz
    have hpos := (strictMono_roundedCorner_projection (P i) (P i - P (i - 1))
      (P (i + 1) - P i) hρ hder ℓ hu hv).1 (t - i)
    change 0 < ℓ (deriv Γ (t - i)) at hpos
    rw [hz, map_zero] at hpos
    exact (lt_irrefl 0) hpos

theorem exists_smooth_rounded_polygon_family [FiniteDimensional ℝ E]
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {K : Set V}
    (hK : IsCompact K) (p : V → Polygon E n)
    (hp : ∀ i, ContDiff ℝ ∞ (fun z => p z i))
    (hsimple : ∀ z ∈ K, IsSimplePolygon (p z)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 / 4 ∧ ∃ ρ : ℝ → ℝ,
      ContDiff ℝ ∞ ρ ∧ (∀ s, δ ≤ |s| → ρ s = |s|) ∧
      (∀ s, |s| ≤ ρ s ∧ ρ s ≤ |s| + δ) ∧ (∀ s, |deriv ρ s| ≤ 1) ∧
      ContDiff ℝ ∞ (fun x : V × ℝ => roundedPolygonParameter ρ (p x.1) x.2) ∧
      (∀ z, Periodic (roundedPolygonParameter ρ (p z)) (n : ℝ)) ∧
      (∀ z ∈ K, InjOn (roundedPolygonParameter ρ (p z)) (Ico 0 (n : ℝ))) ∧
      (∀ z ∈ K, ∀ t, deriv (roundedPolygonParameter ρ (p z)) t ≠ 0) ∧
      ∀ z ∈ K, ∀ t, dist (roundedPolygonParameter ρ (p z) t)
        (polygonLinearParameter (p z) t) < ε := by
  have hsum : Continuous (fun z : V => ∑ i : Fin n, ‖p z i‖) :=
    continuous_finsetSum _ (fun i _ => (hp i).continuous.norm)
  obtain ⟨b, hb⟩ := hK.bddAbove_image hsum.continuousOn
  let B := max b 0 + 1
  have hB0 : 0 < B := by dsimp [B]; positivity
  have hB (z : V) (hz : z ∈ K) (i : Fin n) : ‖p z i‖ ≤ B := by
    calc
      ‖p z i‖ ≤ ∑ j : Fin n, ‖p z j‖ :=
        Finset.single_le_sum (fun j _ => norm_nonneg (p z j)) (Finset.mem_univ i)
      _ ≤ b := hb ⟨z, hz, rfl⟩
      _ ≤ B := by dsimp [B]; linarith [le_max_left b 0]
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne n)
  obtain ⟨η, hη, hstable⟩ := exists_periodic_injection_tolerance hK
    (T := (n : ℝ)) (r := 1 / 4) (by linarith) (by norm_num) (by linarith)
    (fun z => polygonLinearParameter (p z))
    (continuous_polygonLinearParameter (fun i => (hp i).continuous)).continuousOn
    (fun _ _ => periodic_polygonLinearParameter _)
    (fun z hz => (hsimple z hz).injOn_polygonLinearParameter)
  have hmin : 0 < min (1 / 4 : ℝ) (min ε η / (2 * B)) := by positivity
  obtain ⟨δ, hδ, hd⟩ := exists_between hmin
  have hδquarter : δ < 1 / 4 := lt_of_lt_of_le hd (min_le_left _ _)
  have herr : 2 * δ * B < min ε η := by
    have h := (lt_div_iff₀ (show 0 < 2 * B by positivity)).mp
      (lt_of_lt_of_le hd (min_le_right _ _))
    nlinarith
  obtain ⟨ρ, hρ, _, _, htail, hbound, hder⟩ := exists_smooth_absolute_rounding hδ
  have hhalf : δ < 1 / 2 := by linarith
  have hreg (z : V) (hz : z ∈ K) := (hsimple z hz).roundedPolygonParameter_regular
    hδ hδquarter htail hbound (hρ.differentiable (by simp)) hder
  have hclose (z : V) (hz : z ∈ K) (t : ℝ) :
      dist (roundedPolygonParameter ρ (p z) t) (polygonLinearParameter (p z) t) < min ε η :=
    (dist_roundedPolygonParameter_le (p z) hδ hhalf htail hbound (hB z hz) t).trans_lt herr
  refine ⟨δ, hδ, hδquarter, ρ, hρ, htail, hbound, hder,
    contDiff_roundedPolygonParameter hδ hhalf htail hbound hρ hp,
    (fun z => periodic_roundedPolygonParameter ρ (p z)), ?_, ?_, ?_⟩
  · apply hstable (fun z => roundedPolygonParameter ρ (p z))
      (fun _ _ => periodic_roundedPolygonParameter _ _)
    · intro z hz t _
      exact lt_of_lt_of_le (hclose z hz t) (min_le_right _ _)
    · intro z hz
      exact (hreg z hz).1
  · intro z hz
    exact (hreg z hz).2
  · intro z hz t
    exact lt_of_lt_of_le (hclose z hz t) (min_le_left _ _)

end Poincare.Manifold.Schoenflies.Plane
