import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Boundedness.Geometry.Smoothing.ComponentDiameter.Euclidean
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.AncientCompactness

local notation "I₃" => 𝓘(ℝ, CoordinateThree)

theorem exists_collar_in_open
    {M Y : Type*} [TopologicalSpace M] [TopologicalSpace Y] [CompactSpace Y]
    {U V : Set M} (hU : IsOpen U) (hV : IsOpen V)
    {s : ℝ} (hs : 0 < s) (e : (Y × Ioo (-s) s) ≃ₜ U)
    (hcenter : ∀ y : Y, (e (y, ⟨0, neg_lt_zero.mpr hs, hs⟩) : M) ∈ V) :
    ∃ (t : ℝ) (ht : 0 < t) (W : Set M), IsOpen W ∧ W ⊆ V ∧
      ∃ d : (Y × Ioo (-t) t) ≃ₜ W,
        ∀ y : Y, (d (y, ⟨0, neg_lt_zero.mpr ht, ht⟩) : M) =
          (e (y, ⟨0, neg_lt_zero.mpr hs, hs⟩) : M) := by
  let z : Ioo (-s) s := ⟨0, neg_lt_zero.mpr hs, hs⟩
  let O : Set (Y × Ioo (-s) s) := (fun q => (e q : M)) ⁻¹' V
  have hO : IsOpen O := hV.preimage (continuous_subtype_val.comp e.continuous)
  have hzero : (univ : Set Y) ×ˢ ({z} : Set (Ioo (-s) s)) ⊆ O := by
    rintro ⟨y, v⟩ ⟨_, hv⟩
    have hvz : v = z := hv
    subst v
    exact hcenter y
  obtain ⟨A, B, _, hB, hYA, hzB, hAB⟩ := generalized_tube_lemma
    (isCompact_univ : IsCompact (univ : Set Y)) isCompact_singleton hO hzero
  obtain ⟨r, hr, hrB⟩ := Metric.isOpen_iff.mp hB z (hzB (mem_singleton z))
  let t := min r s / 2
  have ht : 0 < t := half_pos (lt_min hr hs)
  have htr : t < r := (half_lt_self (lt_min hr hs)).trans_le (min_le_left _ _)
  have hts : t < s := (half_lt_self (lt_min hr hs)).trans_le (min_le_right _ _)
  have hsub : Ioo (-t) t ⊆ Ioo (-s) s := Ioo_subset_Ioo (by linarith) hts.le
  let j : (Y × Ioo (-t) t) → (Y × Ioo (-s) s) := Prod.map id (inclusion hsub)
  have hj : IsOpenEmbedding j := IsOpenEmbedding.id.prodMap
    (IsOpenEmbedding.inclusion hsub (isOpen_Ioo.preimage continuous_subtype_val))
  let F : (Y × Ioo (-t) t) → M := fun q => (e (j q) : M)
  have hF : IsOpenEmbedding F := hU.isOpenEmbedding_subtypeVal.comp
    (e.isOpenEmbedding.comp hj)
  refine ⟨t, ht, range F, hF.isOpen_range, ?_, hF.isEmbedding.toHomeomorph, ?_⟩
  · rintro _ ⟨⟨y, v⟩, rfl⟩
    apply hAB
    refine ⟨hYA (mem_univ y), hrB ?_⟩
    change dist (v : ℝ) 0 < r
    rw [Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [v.property.1], by linarith [v.property.2]⟩
  · intro y
    rfl

theorem exists_coordinate_critical_point_of_compact_connected_level_collar
    {M Y : Type*} [TopologicalSpace M] [TopologicalSpace Y]
    [CompactSpace Y] [ConnectedSpace Y]
    (e : OpenPartialHomeomorph M CoordinateThree)
    {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e.source)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (c : (Y × Ioo (-s) s) ≃ₜ U)
    (himage : ∀ y : Y, e (c (y, ⟨0, neg_lt_zero.mpr hs, hs⟩)) ∈ ball 0 r)
    {f : M → ℝ} (hf : ContinuousOn (f ∘ e.symm) (closedBall 0 r)) {a : ℝ}
    (hlevel : ∀ y : Y, f (c (y, ⟨0, neg_lt_zero.mpr hs, hs⟩)) = a) :
    ∃ x ∈ ball (0 : CoordinateThree) r, fderiv ℝ (f ∘ e.symm) x = 0 := by
  let d : (Y × Ioo (-s) s) ≃ₜ e '' U :=
    c.trans (e.homeomorphOfImageSubsetSource hUe rfl)
  apply exists_critical_point_in_ball_of_compact_connected_level_collar
    (e.isOpen_image_of_subset_source hU hUe) hs hr d
      (by rintro _ ⟨y, rfl⟩; exact himage y) hf
  intro y
  change f (e.symm (e (c (y, ⟨0, neg_lt_zero.mpr hs, hs⟩)))) = a
  rw [e.left_inv (hUe (c (y, ⟨0, neg_lt_zero.mpr hs, hs⟩)).property)]
  exact hlevel y

theorem mfderiv_eq_zero_of_coordinate_critical_point
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace CoordinateThree M]
    (e : OpenPartialHomeomorph M CoordinateThree)
    {f : M → ℝ} {x : CoordinateThree} (hx : x ∈ e.target)
    (hf : MDifferentiableAt I₃ 𝓘(ℝ, ℝ) f (e.symm x))
    (he : MDifferentiableAt I₃ I₃ e (e.symm x))
    (hei : MDifferentiableAt I₃ I₃ e.symm x)
    (hzero : fderiv ℝ (f ∘ e.symm) x = 0) :
    mfderiv I₃ 𝓘(ℝ, ℝ) f (e.symm x) = 0 := by
  have hcomp := mfderiv_comp x hf hei
  rw [mfderiv_eq_fderiv, hzero] at hcomp
  have hinv : (e.symm ∘ e) =ᶠ[𝓝 (e.symm x)] id := by
    filter_upwards [e.open_source.mem_nhds (e.map_target hx)] with y hy
    exact e.left_inv hy
  have hchain := mfderiv_comp (e.symm x) (by simpa only [e.right_inv hx] using hei) he
  rw [hinv.mfderiv_eq, mfderiv_id, e.right_inv hx] at hchain
  apply ContinuousLinearMap.ext
  intro v
  have hv := congrArg (fun L : CoordinateThree →L[ℝ] CoordinateThree => L v) hchain
  have hz := congrArg (fun L : CoordinateThree →L[ℝ] ℝ =>
    L (mfderiv I₃ I₃ e (e.symm x) v)) hcomp
  change v = mfderiv I₃ I₃ e.symm x (mfderiv I₃ I₃ e (e.symm x) v) at hv
  change 0 = mfderiv I₃ 𝓘(ℝ, ℝ) f (e.symm x)
    (mfderiv I₃ I₃ e.symm x (mfderiv I₃ I₃ e (e.symm x) v)) at hz
  rw [← hv] at hz
  exact hz.symm

theorem exists_critical_point_in_chart_ball_of_compact_connected_level_collar
    {M Y : Type*} [TopologicalSpace M] [TopologicalSpace Y]
    [ChartedSpace CoordinateThree M] [CompactSpace Y] [ConnectedSpace Y]
    (e : OpenPartialHomeomorph M CoordinateThree)
    {U : Set M} (hU : IsOpen U)
    {s r : ℝ} (hs : 0 < s) (hr : 0 < r)
    (c : (Y × Ioo (-s) s) ≃ₜ U)
    (hcenter : ∀ y : Y, (c (y, ⟨0, neg_lt_zero.mpr hs, hs⟩) : M) ∈ e.source)
    (himage : ∀ y : Y, e (c (y, ⟨0, neg_lt_zero.mpr hs, hs⟩)) ∈ ball 0 r)
    (hball : closedBall (0 : CoordinateThree) r ⊆ e.target)
    {f : M → ℝ}
    (hf : MDifferentiableOn I₃ 𝓘(ℝ, ℝ) f e.source)
    (he : MDifferentiableOn I₃ I₃ e e.source)
    (hei : MDifferentiableOn I₃ I₃ e.symm e.target)
    {a : ℝ} (hlevel : ∀ y : Y, f (c (y, ⟨0, neg_lt_zero.mpr hs, hs⟩)) = a) :
    ∃ x ∈ e.source, e x ∈ ball (0 : CoordinateThree) r ∧
      mfderiv I₃ 𝓘(ℝ, ℝ) f x = 0 := by
  obtain ⟨t, ht, W, hW, hWe, d, hd⟩ :=
    exists_collar_in_open hU e.open_source hs c hcenter
  have hcont : ContinuousOn (f ∘ e.symm) (closedBall (0 : CoordinateThree) r) :=
    (hf.continuousOn.comp e.continuousOn_symm e.mapsTo_symm).mono hball
  obtain ⟨x, hx, hcrit⟩ :=
    exists_coordinate_critical_point_of_compact_connected_level_collar e hW hWe ht hr d
      (fun y => by simpa only [hd y] using himage y) hcont
      (fun y => by simpa only [hd y] using hlevel y)
  have hxt : x ∈ e.target := hball (ball_subset_closedBall hx)
  have hxs : e.symm x ∈ e.source := e.map_target hxt
  refine ⟨e.symm x, hxs, by simpa only [e.right_inv hxt] using hx, ?_⟩
  exact mfderiv_eq_zero_of_coordinate_critical_point e hxt
    ((hf _ hxs).mdifferentiableAt (e.open_source.mem_nhds hxs))
    ((he _ hxs).mdifferentiableAt (e.open_source.mem_nhds hxs))
    ((hei _ hxt).mdifferentiableAt (e.open_target.mem_nhds hxt)) hcrit

end PoincareConjecture.AncientCompactness
