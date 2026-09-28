import PoincareConjecture.Proofs.M38.MonodromyModel










set_option autoImplicit false

open Set Topology
open scoped Manifold ContDiff

namespace PoincareConjecture.M38

private instance cylinderNonempty : Nonempty RoundCylinderSpace :=
  ⟨(capUnitDirection (0 : StandardCapSpace), 0)⟩


noncomputable def monodromyPolarDiffeomorph :
    Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace monodromyPunctureOpen ∞ where
  toFun := monodromyPolarPoint
  invFun x := (capUnitDirection x.val, monodromyLogRadius x)
  left_inv p := Prod.ext (monodromyPolarPoint_direction p) (monodromyPolarPoint_logRadius p)
  right_inv := monodromyPolarPoint_reconstruct
  contMDiff_toFun := monodromyPolarPoint_smooth
  contMDiff_invFun :=
    (capUnitDirection_smooth.comp_contMDiff contMDiff_subtype_val
      (fun x => x.property)).prodMk monodromyLogRadius_smooth

variable (phi : Diffeomorph (𝓡 2) (𝓡 2) UnitTwoSphere UnitTwoSphere ∞)

attribute [local instance] monodromyChartedSpace monodromy_isManifold

local notation "mq" => (Quotient.mk (monodromyOrbitRel phi) :
  monodromyPunctureOpen → MonodromyQuotient phi)



theorem monodromyDeck_polar (n : ℤ) (p : RoundCylinderSpace) :
    monodromyDeck phi n (monodromyPolarPoint p) =
      monodromyPolarPoint ((phi.toEquiv ^ (-n)) p.1, p.2 + (n : ℝ)) := by
  calc
    monodromyDeck phi n (monodromyPolarPoint p) = monodromyPolarPoint
        (capUnitDirection (monodromyDeck phi n (monodromyPolarPoint p)).val,
          monodromyLogRadius (monodromyDeck phi n (monodromyPolarPoint p))) :=
      (monodromyPolarPoint_reconstruct _).symm
    _ = monodromyPolarPoint ((phi.toEquiv ^ (-n)) p.1, p.2 + (n : ℝ)) := by
      rw [monodromyDeck_direction, monodromyPolarPoint_direction,
        monodromyDeck_logRadius, monodromyPolarPoint_logRadius, add_comm (n : ℝ)]


noncomputable def monodromyCylinder (p : RoundCylinderSpace) : MonodromyQuotient phi :=
  mq (monodromyPolarPoint p)


theorem monodromyCylinder_eq_iff (p q : RoundCylinderSpace) :
    monodromyCylinder phi p = monodromyCylinder phi q ↔
      ∃ n : ℤ, p.1 = (phi.toEquiv ^ (-n)) q.1 ∧ p.2 = q.2 + (n : ℝ) := by
  rw [monodromyCylinder, monodromyCylinder, monodromy_quotient_eq_iff]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_, ?_⟩
    · simpa only [monodromyDeck_direction, monodromyPolarPoint_direction] using
        (congrArg (fun x : monodromyPunctureOpen => capUnitDirection x.val) hn).symm
    · have hs := (congrArg monodromyLogRadius hn).symm
      rw [monodromyDeck_logRadius, monodromyPolarPoint_logRadius,
        monodromyPolarPoint_logRadius] at hs
      simpa only [add_comm (n : ℝ)] using hs
  · rintro ⟨n, hz, hs⟩
    refine ⟨n, ?_⟩
    rw [monodromyDeck_polar, ← hz, ← hs]


theorem monodromyCylinder_endpoint (z : UnitTwoSphere) :
    monodromyCylinder phi (z, 1) = monodromyCylinder phi (phi z, 0) := by
  have h := (monodromy_quotient_deck phi (-1) (monodromyPolarPoint (z, 1))).symm
  simpa only [monodromyCylinder, monodromyDeck_polar, neg_neg, zpow_one,
    Int.cast_neg, Int.cast_one, add_neg_cancel, Diffeomorph.coe_toEquiv] using h


theorem monodromyCylinder_projection (p : RoundCylinderSpace) :
    monodromyProjection phi (monodromyCylinder phi p) = circlePeriodMap p.2 := by
  rw [monodromyCylinder, monodromyProjection_mk, monodromyPolarPoint_logRadius]


theorem monodromyCylinder_injective_strip (a b : ℝ) (hwidth : b - a ≤ 1) :
    Set.InjOn (monodromyCylinder phi) (Set.univ ×ˢ Set.Ioo a b) := by
  intro p hp q hq hpq
  obtain ⟨n, hz, hs⟩ := (monodromyCylinder_eq_iff phi p q).mp hpq
  have hlo : (-1 : ℝ) < (n : ℝ) := by linarith [hp.2.1, hq.2.2]
  have hhi : (n : ℝ) < 1 := by linarith [hp.2.2, hq.2.1]
  have hnlo : -1 < n := by exact_mod_cast hlo
  have hnhi : n < 1 := by exact_mod_cast hhi
  have hn : n = 0 := by omega
  apply Prod.ext
  · simpa only [hn, neg_zero, zpow_zero, Equiv.Perm.one_apply] using hz
  · simpa only [hn, Int.cast_zero, add_zero] using hs


theorem monodromy_quotient_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ mq := by
  intro x
  let s := (monodromy_quotient_localHomeomorph phi).localInverseAt x
  refine ⟨{
    toPartialEquiv := s.symm.toPartialEquiv
    open_source := s.open_target
    open_target := s.open_source
    contMDiffOn_toFun := ?_
    contMDiffOn_invFun := monodromy_sheet_contMDiffOn phi x }, ?_, ?_⟩
  · simpa only [s, OpenPartialHomeomorph.coe_toPartialEquiv,
      OpenPartialHomeomorph.symm_source,
      (monodromy_quotient_localHomeomorph phi).localInverseAt_symm] using
        (monodromy_quotient_contMDiff phi).contMDiffOn
          (s := ((monodromy_quotient_localHomeomorph phi).localInverseAt x).target)
  · exact (monodromy_quotient_localHomeomorph phi).self_mem_localInverseAt_target
  · intro y _
    exact (congrFun ((monodromy_quotient_localHomeomorph phi).localInverseAt_symm x) y).symm


theorem monodromyCylinder_localDiffeomorph :
    IsLocalDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (monodromyCylinder phi) := by
  intro p
  exact (monodromyPolarDiffeomorph.isLocalDiffeomorph p).comp (𝓡 3)
    (MonodromyQuotient phi) (monodromy_quotient_localDiffeomorph phi (monodromyPolarPoint p))


noncomputable def monodromyStripInverse (a b : ℝ) :
    MonodromyQuotient phi → RoundCylinderSpace :=
  Function.invFunOn (monodromyCylinder phi) (Set.univ ×ˢ Set.Ioo a b)


theorem monodromyStripInverse_left (a b : ℝ) (hwidth : b - a ≤ 1) :
    Set.LeftInvOn (monodromyStripInverse phi a b) (monodromyCylinder phi)
      (Set.univ ×ˢ Set.Ioo a b) :=
  (monodromyCylinder_injective_strip phi a b hwidth).leftInvOn_invFunOn


theorem monodromyStripInverse_mem (a b : ℝ) {q : MonodromyQuotient phi}
    (hq : q ∈ monodromyCylinder phi '' (Set.univ ×ˢ Set.Ioo a b)) :
    monodromyStripInverse phi a b q ∈ Set.univ ×ˢ Set.Ioo a b :=
  Function.invFunOn_mem hq


theorem monodromyStripInverse_right (a b : ℝ) :
    Set.LeftInvOn (monodromyCylinder phi) (monodromyStripInverse phi a b)
      (monodromyCylinder phi '' (Set.univ ×ˢ Set.Ioo a b)) :=
  fun _ hq => Function.invFunOn_eq hq



theorem monodromyStripInverse_smooth (a b : ℝ) (hwidth : b - a ≤ 1) :
    ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (monodromyStripInverse phi a b)
      (monodromyCylinder phi '' (Set.univ ×ˢ Set.Ioo a b)) := by
  rintro y ⟨x, hx, hxy⟩
  let hlocal := monodromyCylinder_localDiffeomorph phi x
  let s := hlocal.localInverse
  have hy : y ∈ s.source := hxy ▸ hlocal.localInverse_mem_source
  have hsy : s y = x := by
    rw [← hxy]
    exact hlocal.localInverse_left_inv hlocal.localInverse_mem_target
  have hs : ContMDiffAt (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ s y :=
    hlocal.contmdiffOn_localInverse.contMDiffAt (s.open_source.mem_nhds hy)
  have hD : IsOpen ((Set.univ : Set UnitTwoSphere) ×ˢ Set.Ioo a b) :=
    isOpen_univ.prod isOpen_Ioo
  have hsd : s y ∈ Set.univ ×ˢ Set.Ioo a b := hsy ▸ hx
  have hn : ∀ᶠ z in 𝓝 y, s z ∈ Set.univ ×ˢ Set.Ioo a b :=
    hs.continuousAt.preimage_mem_nhds (hD.mem_nhds hsd)
  apply (hs.congr_of_eventuallyEq ?_).contMDiffWithinAt
  filter_upwards [s.open_source.mem_nhds hy, hn] with z hz hsz
  have hzimage : z ∈ monodromyCylinder phi '' (Set.univ ×ˢ Set.Ioo a b) :=
    ⟨s z, hsz, hlocal.localInverse_right_inv hz⟩
  apply monodromyCylinder_injective_strip phi a b hwidth
    (monodromyStripInverse_mem phi a b hzimage) hsz
  rw [monodromyStripInverse_right phi a b hzimage, hlocal.localInverse_right_inv hz]


noncomputable def monodromyStripChart (a b : ℝ) (hwidth : b - a ≤ 1) :
    PartialDiffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3)
      RoundCylinderSpace (MonodromyQuotient phi) ∞ where
  toFun := monodromyCylinder phi
  invFun := monodromyStripInverse phi a b
  source := Set.univ ×ˢ Set.Ioo a b
  target := monodromyCylinder phi '' (Set.univ ×ˢ Set.Ioo a b)
  map_source' := fun _ hx => Set.mem_image_of_mem _ hx
  map_target' := fun {_} hy => monodromyStripInverse_mem phi a b hy
  left_inv' := monodromyStripInverse_left phi a b hwidth
  right_inv' := monodromyStripInverse_right phi a b
  open_source := isOpen_univ.prod isOpen_Ioo
  open_target := (monodromyCylinder_localDiffeomorph phi).isOpenMap _
    (isOpen_univ.prod isOpen_Ioo)
  contMDiffOn_toFun := (monodromyCylinder_localDiffeomorph phi).contMDiff.contMDiffOn
  contMDiffOn_invFun := monodromyStripInverse_smooth phi a b hwidth


theorem monodromy_unit_strip_image :
    monodromyCylinder phi '' (Set.univ ×ˢ Set.Ioo (0 : ℝ) 1) =
      {q | monodromyProjection phi q ≠ circlePeriodMap 0} := by
  ext q
  constructor
  · rintro ⟨p, hp, rfl⟩ he
    rw [monodromyCylinder_projection] at he
    obtain ⟨n, hn⟩ := (circlePeriodMap_eq_iff p.2 0).mp he
    have hnpos : (0 : ℝ) < (n : ℝ) := by linarith [hp.2.1]
    have hnlt : (n : ℝ) < 1 := by linarith [hp.2.2]
    have hlo : 0 < n := by exact_mod_cast hnpos
    have hhi : n < 1 := by exact_mod_cast hnlt
    omega
  · intro hq
    obtain ⟨x, rfl⟩ := (monodromy_open_quotient phi).surjective q
    let y := monodromyDeck phi (-⌊monodromyLogRadius x⌋) x
    have hyq : mq y = mq x := monodromy_quotient_deck phi _ x
    have ht : 0 ≤ monodromyLogRadius y ∧ monodromyLogRadius y < 1 := by
      dsimp [y]
      rw [monodromyDeck_logRadius, Int.cast_neg]
      have hlo := Int.floor_le (monodromyLogRadius x)
      have hhi := Int.lt_floor_add_one (monodromyLogRadius x)
      constructor <;> linarith
    have hne : monodromyLogRadius y ≠ 0 := by
      intro he
      apply hq
      calc
        monodromyProjection phi (mq x) = monodromyProjection phi (mq y) :=
          congrArg (monodromyProjection phi) hyq.symm
        _ = circlePeriodMap (monodromyLogRadius y) := monodromyProjection_mk phi y
        _ = circlePeriodMap 0 := congrArg circlePeriodMap he
    refine ⟨(capUnitDirection y.val, monodromyLogRadius y),
      ⟨Set.mem_univ _, lt_of_le_of_ne ht.1 hne.symm, ht.2⟩, ?_⟩
    change mq (monodromyPolarPoint (capUnitDirection y.val, monodromyLogRadius y)) = mq x
    rw [monodromyPolarPoint_reconstruct]
    exact hyq

end PoincareConjecture.M38
