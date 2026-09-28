import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Continuation.Construction.Terminal.Event.StrongBoundary.OldCylinder
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.RegularLimit.Canonical.Neck.CylinderCompatibility
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.SingularLimitConclusion

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M] [SecondCountableTopology M]
  {G : GeneralizedRicciFlowData.{u}} {T epsilon : ℝ}
  {H : SingularTimeAssumptions G T M} (Q : SingularLimitConclusion H)
  (N : TerminalStrongNeck Q.extension epsilon)

theorem strongNeck_eq_gluing (x : (Q.extension.extended.slice T).carrier)
    (hx : x ∈ N.carrier) (s : ℝ) (hs : s ∈ Ioc (-1 : ℝ) 0)
    (ht : T + s / (N.scale⁻¹ ^ 2) ∈ Ioc H.reference.tMinus T) :
    Q.gluing_map (⟨T + s / (N.scale⁻¹ ^ 2), ht⟩, x) = N.time_cylinder.pointMap s hs x := by
  let q := N.scale⁻¹ ^ 2
  have hq : 0 < q := N.time_cylinder.scale_pos
  let J : Set ℝ := Ioc (-1 : ℝ) 0 ∩ (fun z => T + z / q) ⁻¹' Ioc H.reference.tMinus T
  have hclock : Monotone (fun z : ℝ => T + z / q) := by
    intro z w hzw
    exact add_le_add le_rfl (div_le_div_of_nonneg_right hzw hq.le)
  let : T2Space Q.extension.extended.point := Q.extension.extended.space_t2
  let : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp
    (ordConnected_Ioc.inter (ordConnected_Ioc.preimage_mono hclock)).isPreconnected
  let r : J → Q.extension.extended.point := fun z =>
    Q.gluing_map (⟨T + (z : ℝ) / q, z.property.2⟩, x)
  let c : J → Q.extension.extended.point := fun z =>
    N.time_cylinder.pointMap z z.property.1 x
  have hr : Continuous r := Q.gluing_openEmbedding.continuous.comp
    (((continuous_const.add (continuous_subtype_val.div_const q)).subtype_mk
      (fun z => z.property.2)).prodMk continuous_const)
  have hc : Continuous c := N.time_cylinder.embedding.continuous.comp
    ((continuous_subtype_val.subtype_mk (fun z => z.property.1)).prodMk
      (continuous_const (y := (⟨x, hx⟩ : N.carrier))))
  have hclosed : IsClosed {z : J | r z = c z} := isClosed_eq hr hc
  have hopen : IsOpen {z : J | r z = c z} := by
    rw [Metric.isOpen_iff]
    intro z hz
    obtain ⟨b, y, δ, hδ, hcurve⟩ :=
      N.time_cylinder.vertical_compatibility z z.property.1 x hx
    obtain ⟨k, w, ε, hε, hglue⟩ :=
      Q.gluing_vertical_compatibility (T + (z : ℝ) / q) z.property.2 x
    obtain ⟨hb, hby⟩ := hcurve z z.property.1 (by simpa using hδ)
    obtain ⟨hk, hkw⟩ := hglue (T + (z : ℝ) / q) z.property.2 (by simpa using hε)
    have hbase : (Q.extension.extended.box k).forward (T + (z : ℝ) / q) hk w =
        (Q.extension.extended.box b).forward (T + (z : ℝ) / q) hb y := by
      have he : (⟨T + (z : ℝ) / q,
          (Q.extension.extended.box k).forward (T + (z : ℝ) / q) hk w⟩ :
          Q.extension.extended.point) = N.time_cylinder.pointMap z z.property.1 x :=
        hkw.symm.trans hz
      exact (eq_of_heq (Sigma.mk.inj he).2).trans hby
    refine ⟨min δ (ε * q), lt_min hδ (mul_pos hε hq), ?_⟩
    intro v hv
    have hvδ : |(v : ℝ) - (z : ℝ)| < min δ (ε * q) := by
      simpa only [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq] using hv
    have hphysical : |(T + (v : ℝ) / q) - (T + (z : ℝ) / q)| < ε := by
      rw [show (T + (v : ℝ) / q) - (T + (z : ℝ) / q) = ((v : ℝ) - z) / q by ring,
        abs_div, abs_of_pos hq]
      exact (div_lt_iff₀ hq).mpr (hvδ.trans_le (min_le_right _ _))
    obtain ⟨hbv, hbyv⟩ := hcurve v v.property.1 (hvδ.trans_le (min_le_left _ _))
    obtain ⟨hkv, hkwv⟩ := hglue (T + (v : ℝ) / q) v.property.2 hphysical
    have hsame := Q.extension.extended.vertical_compatibility k b
      (T + (z : ℝ) / q) hk hb w y hbase (T + (v : ℝ) / q) hkv hbv
    exact hkwv.trans (congrArg (Sigma.mk (T + (v : ℝ) / q)) (hsame.trans hbyv.symm))
  have hzero : (0 : ℝ) ∈ J := by
    exact ⟨by norm_num, by simpa using (show T ∈ Ioc H.reference.tMinus T from
      ⟨H.reference.tMinus_lt, le_rfl⟩)⟩
  have hall : {z : J | r z = c z} = univ :=
    (show IsClopen {z : J | r z = c z} from ⟨hclosed, hopen⟩).eq_univ
      ⟨⟨0, hzero⟩, by
        change Q.gluing_map (⟨T + 0 / q, _⟩, x) = N.time_cylinder.pointMap 0 _ x
        simpa only [zero_div, add_zero] using
          (Q.gluing_terminal x).trans (N.cylinder_identity hzero.1 x hx).symm⟩
  exact Set.eq_univ_iff_forall.mp hall ⟨s, hs, ht⟩

theorem strongNeck_inverse_reference (x : (Q.extension.extended.slice T).carrier)
    (hx : x ∈ N.carrier) (s : ℝ) (hs : s ∈ Ioo (-1 : ℝ) 0)
    (ht : T + s / (N.scale⁻¹ ^ 2) ∈ Ico H.reference.tMinus T) :
    Q.extension.inverse (T + s / (N.scale⁻¹ ^ 2)) (H.reference.window_subset ht)
        (N.time_cylinder.forward s ⟨hs.1, hs.2.le⟩ x) =
      H.reference.forward (T + s / (N.scale⁻¹ ^ 2)) ht (Q.terminal_source x) := by
  obtain ⟨t, htt, htT⟩ := exists_between (max_lt ht.2 H.reference.tMinus_lt)
  have htime_lt : T + s / (N.scale⁻¹ ^ 2) < T := ht.2
  by_cases hstart : H.reference.tMinus < T + s / (N.scale⁻¹ ^ 2)
  · have he := Q.strongNeck_eq_gluing N x hx s ⟨hs.1, hs.2.le⟩ ⟨hstart, ht.2.le⟩
    rw [Q.gluing_old _ ⟨hstart, ht.2.le⟩ htime_lt x,
      Q.extension.spacetime_slices _ (H.reference.window_subset ht) _] at he
    have hf := eq_of_heq (Sigma.mk.inj he).2
    have hi := congrArg (Q.extension.inverse _ (H.reference.window_subset ht)) hf
    exact hi.symm.trans (Q.extension.left_inverse _ _ _)
  · have hC : Nonempty (Q.extension.extended.slice T).carrier := ⟨x⟩
    have htimes (r : ℝ) (hr : r ∈ Ioo (-1 : ℝ) 0) :
        T + r / (N.scale⁻¹ ^ 2) ∈ G.interval := by
      have hm := Q.extension.times_subset
        (N.time_cylinder.time_mem_of_nonempty_source hC r ⟨hr.1, hr.2.le⟩)
      exact hm.resolve_right (by
        have hh := div_neg_of_neg_of_pos hr.2 N.time_cylinder.scale_pos
        simp only [mem_singleton_iff]
        linarith)
    let d := Q.extension.pullCylinder
      (N.time_cylinder.restrictTime (show Ioo (-1 : ℝ) 0 ⊆ Ioc (-1 : ℝ) 0 from
        fun _ hr => ⟨hr.1, hr.2.le⟩)) htimes
    let r := (t - T) * (N.scale⁻¹ ^ 2)
    have hrclock : T + r / (N.scale⁻¹ ^ 2) = t := by
      dsimp [r]
      rw [mul_div_cancel_right₀ _ (ne_of_gt N.time_cylinder.scale_pos)]
      ring
    have hsr : s < r := by
      have ht' := (le_max_left _ _).trans_lt htt
      dsimp [r]
      apply (div_lt_iff₀ N.time_cylinder.scale_pos).mp
      linarith
    have hr : r ∈ Ioo (-1 : ℝ) 0 := by
      refine ⟨hs.1.trans hsr, ?_⟩
      exact mul_neg_of_neg_of_pos (sub_neg.mpr htT) N.time_cylinder.scale_pos
    have hrt : T + r / (N.scale⁻¹ ^ 2) ∈ Ico H.reference.tMinus T := by
      rw [hrclock]
      exact ⟨((le_max_right _ _).trans_lt htt).le, htT⟩
    have hglue := Q.strongNeck_eq_gluing N x hx r ⟨hr.1, hr.2.le⟩
      (show T + r / (N.scale⁻¹ ^ 2) ∈ Ioc H.reference.tMinus T by
        rw [hrclock]; exact ⟨(le_max_right _ _).trans_lt htt, htT.le⟩)
    rw [Q.gluing_old _ _ hrt.2 x,
      Q.extension.spacetime_slices _ (H.reference.window_subset hrt) _] at hglue
    have hf := eq_of_heq (Sigma.mk.inj hglue).2
    have hbase : H.reference.forward _ hrt (Q.terminal_source x) = d.forward r hr x := by
      exact (Q.extension.left_inverse _ _ _).symm.trans
        (congrArg (Q.extension.inverse _ (H.reference.window_subset hrt)) hf)
    exact (H.reference.forward_eq_cylinder_of_eq d ordConnected_Ioo x hx
      (Q.terminal_source x) hr hrt hbase hs ht).symm

end PoincareConjecture.SingularLimitConclusion
