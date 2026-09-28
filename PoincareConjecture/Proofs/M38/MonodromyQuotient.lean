import PoincareConjecture.Proofs.M38.SphereMonodromy
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Module.Connected

set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

theorem monodromy_continuousConstVAdd :
    letI := monodromyAddAction phi
    ContinuousConstVAdd ℤ monodromyPunctureOpen := by
  let := monodromyAddAction phi
  exact ⟨fun n => (monodromyDeck_smooth phi n).continuous⟩

theorem monodromy_isCancelVAdd :
    letI := monodromyAddAction phi
    IsCancelVAdd ℤ monodromyPunctureOpen := by
  let := monodromyAddAction phi
  constructor
  intro m n x h
  have heq := congrArg monodromyLogRadius h
  change monodromyLogRadius (monodromyDeck phi m x) =
    monodromyLogRadius (monodromyDeck phi n x) at heq
  rw [monodromyDeck_logRadius, monodromyDeck_logRadius] at heq
  exact Int.cast_injective (add_right_cancel heq)

theorem monodromy_properlyDiscontinuous :
    letI := monodromyAddAction phi
    ProperlyDiscontinuousVAdd ℤ monodromyPunctureOpen := by
  let := monodromyAddAction phi
  constructor
  intro K L hK hL
  have hc := monodromyLogRadius_smooth.continuous
  obtain ⟨aK, haK⟩ := hK.bddBelow_image hc.continuousOn
  obtain ⟨bK, hbK⟩ := hK.bddAbove_image hc.continuousOn
  obtain ⟨aL, haL⟩ := hL.bddBelow_image hc.continuousOn
  obtain ⟨bL, hbL⟩ := hL.bddAbove_image hc.continuousOn
  apply (Set.finite_Icc (⌊aL - bK⌋ : ℤ) ⌈bL - aK⌉).subset
  rintro n ⟨y, ⟨x, hx, rfl⟩, hy⟩
  have hax := haK (mem_image_of_mem monodromyLogRadius hx)
  have hbx := hbK (mem_image_of_mem monodromyLogRadius hx)
  have hay := haL (mem_image_of_mem monodromyLogRadius hy)
  have hby := hbL (mem_image_of_mem monodromyLogRadius hy)
  change aL ≤ monodromyLogRadius (monodromyDeck phi n x) at hay
  change monodromyLogRadius (monodromyDeck phi n x) ≤ bL at hby
  rw [monodromyDeck_logRadius] at hay hby
  constructor
  · apply (Int.cast_le (R := ℝ)).mp
    have := Int.floor_le (aL - bK)
    linarith
  · apply (Int.cast_le (R := ℝ)).mp
    have := Int.le_ceil (bL - aK)
    linarith

noncomputable def monodromyOrbitRel : Setoid monodromyPunctureOpen :=
  letI := monodromyAddAction phi
  AddAction.orbitRel ℤ monodromyPunctureOpen

abbrev MonodromyQuotient := Quotient (monodromyOrbitRel phi)

instance monodromyPuncture_locallyCompact : LocallyCompactSpace monodromyPunctureOpen :=
  monodromyPunctureOpen.isOpen.locallyCompactSpace

theorem monodromy_quotientCovering :
    letI := monodromyAddAction phi
    IsAddQuotientCoveringMap
      (Quotient.mk (monodromyOrbitRel phi)) ℤ := by
  let := monodromyAddAction phi
  have := monodromy_continuousConstVAdd phi
  have := monodromy_isCancelVAdd phi
  have := monodromy_properlyDiscontinuous phi
  exact isAddQuotientCoveringMap_quotientMk_of_properlyDiscontinuousVAdd

instance monodromyQuotient_t2 : T2Space (MonodromyQuotient phi) := by
  let := monodromyAddAction phi
  have := monodromy_continuousConstVAdd phi
  have := monodromy_properlyDiscontinuous phi
  exact inferInstanceAs (T2Space (Quotient (AddAction.orbitRel ℤ monodromyPunctureOpen)))

theorem monodromy_open_quotient :
    IsOpenQuotientMap
      (Quotient.mk (monodromyOrbitRel phi) : monodromyPunctureOpen → MonodromyQuotient phi) := by
  let := monodromyAddAction phi
  exact (monodromy_quotientCovering phi).isOpenQuotientMap

instance monodromyQuotient_secondCountable :
    SecondCountableTopology (MonodromyQuotient phi) :=
  TopologicalSpace.Quotient.secondCountableTopology (monodromy_open_quotient phi).isOpenMap

theorem monodromy_quotient_localHomeomorph :
    IsLocalHomeomorph
      (Quotient.mk (monodromyOrbitRel phi) : monodromyPunctureOpen → MonodromyQuotient phi) := by
  let := monodromyAddAction phi
  exact (monodromy_quotientCovering phi).isCoveringMap.isLocalHomeomorph

theorem monodromy_quotient_eq_iff (x y : monodromyPunctureOpen) :
    (Quotient.mk (monodromyOrbitRel phi) x : MonodromyQuotient phi) =
      Quotient.mk (monodromyOrbitRel phi) y ↔
        ∃ n : ℤ, monodromyDeck phi n y = x := by
  let := monodromyAddAction phi
  exact (monodromy_quotientCovering phi).apply_eq_iff_mem_orbit

instance monodromyPuncture_connected : ConnectedSpace monodromyPunctureOpen :=
  isConnected_iff_connectedSpace.mp
    (isConnected_compl_singleton_of_one_lt_rank
      (Module.one_lt_rank_of_one_lt_finrank (by simp [StandardCapSpace])) 0)

instance monodromyQuotient_connected : ConnectedSpace (MonodromyQuotient phi) :=
  (monodromy_open_quotient phi).surjective.connectedSpace
    (monodromy_open_quotient phi).continuous

def monodromyFundamentalDomain : Set monodromyPunctureOpen :=
  {x | 1 ≤ ‖x.val‖ ∧ ‖x.val‖ ≤ Real.exp 1}

theorem monodromyFundamentalDomain_compact : IsCompact monodromyFundamentalDomain := by
  apply Subtype.isCompact_iff.mpr
  have heq : Subtype.val '' monodromyFundamentalDomain =
      {x : StandardCapSpace | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      have hzero : x ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le zero_lt_one hx.1)
      exact ⟨⟨x, hzero⟩, hx, rfl⟩
  rw [heq]
  have hc := (isCompact_closedBall (0 : StandardCapSpace) (Real.exp 1)).inter_left
    (isClosed_le continuous_const continuous_norm : IsClosed {x : StandardCapSpace | 1 ≤ ‖x‖})
  have hset : {x : StandardCapSpace | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ Real.exp 1} =
      {x : StandardCapSpace | 1 ≤ ‖x‖} ∩ Metric.closedBall 0 (Real.exp 1) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
  exact hset.symm ▸ hc

theorem monodromy_mem_fundamental_of_log (x : monodromyPunctureOpen)
    (hx : monodromyLogRadius x ∈ Icc (0 : ℝ) 1) :
    x ∈ monodromyFundamentalDomain := by
  have he : Real.exp (monodromyLogRadius x) = ‖x.val‖ :=
    Real.exp_log (norm_pos_iff.mpr x.property)
  constructor
  · simpa only [Real.exp_zero, he] using Real.exp_le_exp.mpr hx.1
  · simpa only [he] using Real.exp_le_exp.mpr hx.2

theorem monodromyFundamentalDomain_image :
    (Quotient.mk (monodromyOrbitRel phi) : monodromyPunctureOpen → MonodromyQuotient phi) ''
      monodromyFundamentalDomain = univ := by
  apply Set.eq_univ_of_forall
  intro q
  obtain ⟨x, rfl⟩ := (monodromy_open_quotient phi).surjective q
  let n : ℤ := -⌊monodromyLogRadius x⌋
  refine ⟨monodromyDeck phi n x, monodromy_mem_fundamental_of_log _ ?_, ?_⟩
  · rw [monodromyDeck_logRadius]
    have hlow := Int.floor_le (monodromyLogRadius x)
    have hupp := Int.lt_floor_add_one (monodromyLogRadius x)
    dsimp [n]
    rw [Int.cast_neg]
    constructor <;> linarith
  · exact (monodromy_quotient_eq_iff phi _ _).mpr ⟨n, rfl⟩

instance monodromyQuotient_compact : CompactSpace (MonodromyQuotient phi) := by
  constructor
  exact (monodromyFundamentalDomain_image phi) ▸
    monodromyFundamentalDomain_compact.image (monodromy_open_quotient phi).continuous

end PoincareConjecture.M38
