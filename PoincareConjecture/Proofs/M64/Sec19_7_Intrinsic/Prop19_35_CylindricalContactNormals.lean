import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_NormalContactPositive













noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace




theorem m64Intrinsic_cylindrical_normal_contact_opposite
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u) {P R : ℝ} (hP : 0 < P)
    {p q : ℝ × ℝ} (hpbase : p.1 ∈ Ico (0 : ℝ) P) (hqbase : q.1 ∈ Ico (0 : ℝ) P)
    (hpheight : p.2 ∈ Ioc (0 : ℝ) R) (hqheight : q.2 ∈ Ioc (0 : ℝ) R)
    (hne : p ≠ q) (hmeet : u p = u q)
    (hbelow : ∀ x y : ℝ × ℝ, x.2 ∈ Ico (0 : ℝ) R → y.2 ∈ Ico (0 : ℝ) R →
      u x = u y → (x.1 : AddCircle P) = (y.1 : AddCircle P) ∧ x.2 = y.2)
    (hip : Function.Injective (fderiv ℝ u p))
    (hiq : Function.Injective (fderiv ℝ u q))
    (hpunit : G.inner (u p) (fderiv ℝ u p (0, 1)) (fderiv ℝ u p (0, 1)) = 1)
    (hqunit : G.inner (u q) (fderiv ℝ u q (0, 1)) (fderiv ℝ u q (0, 1)) = 1)
    (hporth : G.inner (u p) (fderiv ℝ u p (0, 1)) (fderiv ℝ u p (1, 0)) = 0)
    (hqorth : G.inner (u q) (fderiv ℝ u q (0, 1)) (fderiv ℝ u q (1, 0)) = 0) :
    p.2 = R ∧ q.2 = R ∧ fderiv ℝ u p (0, 1) = -fderiv ℝ u q (0, 1) := by
  let : Fact (0 < P) := ⟨hP⟩
  let c := (max p.1 q.1 - P) / 2
  let S : Set (ℝ × ℝ) := {z | c < z.1 ∧ z.1 < c + P}
  have hS : IsOpen S := isOpen_Ioo.preimage continuous_fst
  have hmax : max p.1 q.1 < P := max_lt hpbase.2 hqbase.2
  have hpS : p ∈ S := by
    change c < p.1 ∧ p.1 < c + P
    dsimp only [c]
    constructor <;> linarith [hpbase.1, le_max_left p.1 q.1]
  have hqS : q ∈ S := by
    change c < q.1 ∧ q.1 < c + P
    dsimp only [c]
    constructor <;> linarith [hqbase.1, le_max_right p.1 q.1]
  have hinj : InjOn u (S ∩ {z | 0 < z.2 ∧ z.2 < R}) := by
    intro x hx y hy hxy
    obtain ⟨hbase, hheight⟩ := hbelow x y ⟨hx.2.1.le, hx.2.2⟩
      ⟨hy.2.1.le, hy.2.2⟩ hxy
    have hb : x.1 = y.1 := (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := c)
      ⟨hx.1.1.le, hx.1.2⟩ ⟨hy.1.1.le, hy.1.2⟩).mp hbase
    exact Prod.ext hb hheight
  exact m64Intrinsic_first_normal_contact_opposite G hu hS hpS hqS hpheight hqheight
    hne hmeet hinj hip hiq hpunit hqunit hporth hqorth






theorem m64Intrinsic_nonembedded_normal_strip_has_opposite_contact
    (G : RiemannianMetric 2 AnnulusCoordinates)
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u) {T : ℝ}
    (hperiod : ∀ t, Function.Periodic (fun a => u (a, t)) rampPeriod)
    (hboundary : ∀ a, u (a, 0) = intrinsicAnnulusBoundary 1 a)
    (hinside : ∀ a ∈ Ico (0 : ℝ) rampPeriod, ∀ t ∈ Ioc (0 : ℝ) T,
      1 < ‖u (a, t)‖)
    (hregular : ∀ z ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T,
      Function.Injective (fderiv ℝ u z))
    (hunit : ∀ z ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T,
      G.inner (u z) (fderiv ℝ u z (0, 1)) (fderiv ℝ u z (0, 1)) = 1)
    (horth : ∀ z ∈ Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T,
      G.inner (u z) (fderiv ℝ u z (0, 1)) (fderiv ℝ u z (1, 0)) = 0)
    (hfail : ¬InjOn u (Ico (0 : ℝ) rampPeriod ×ˢ Icc (0 : ℝ) T)) :
    ∃ a b R : ℝ, a ∈ Ico (0 : ℝ) rampPeriod ∧ b ∈ Ico (0 : ℝ) rampPeriod ∧
      a ≠ b ∧ 0 < R ∧ R ≤ T ∧ u (a, R) = u (b, R) ∧
      fderiv ℝ u (a, R) (0, 1) = -fderiv ℝ u (b, R) (0, 1) ∧
      ∀ x y : ℝ × ℝ, x.2 ∈ Ico (0 : ℝ) R → y.2 ∈ Ico (0 : ℝ) R →
        u x = u y → (x.1 : AddCircle rampPeriod) = (y.1 : AddCircle rampPeriod) ∧
          x.2 = y.2 := by
  have hP : 0 < rampPeriod := by unfold rampPeriod; positivity
  obtain ⟨p, q, hp, hq, hne, hmeet, hbelow⟩ :=
    m64Intrinsic_exists_periodic_first_contact hu hP hperiod hregular hfail
  obtain ⟨hp0, hq0⟩ := m64Intrinsic_normal_collision_heights_pos hboundary hinside hp hq hne hmeet
  let R := max p.2 q.2
  obtain ⟨hpR, hqR, hopp⟩ := m64Intrinsic_cylindrical_normal_contact_opposite G hu hP
    hp.1 hq.1 ⟨hp0, le_max_left _ _⟩ ⟨hq0, le_max_right _ _⟩ hne hmeet hbelow
    (hregular p hp) (hregular q hq) (hunit p hp) (hunit q hq) (horth p hp) (horth q hq)
  have hpEq : p = (p.1, R) := Prod.ext rfl hpR
  have hqEq : q = (q.1, R) := Prod.ext rfl hqR
  refine ⟨p.1, q.1, R, hp.1, hq.1, ?_, hp0.trans_le (le_max_left _ _),
    max_le hp.2.2 hq.2.2, ?_, ?_, hbelow⟩
  · intro heq
    exact hne (Prod.ext heq (hpR.trans hqR.symm))
  · exact (congrArg u hpEq).symm.trans (hmeet.trans (congrArg u hqEq))
  · exact (congrArg (fun z => fderiv ℝ u z (0, 1)) hpEq).symm.trans
      (hopp.trans (congrArg (fun z => -fderiv ℝ u z (0, 1)) hqEq))

end PoincareConjecture
