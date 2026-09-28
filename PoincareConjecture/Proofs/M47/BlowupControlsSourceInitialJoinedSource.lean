import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialBirthSlice
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialCylinderJoin
import PoincareConjecture.Proofs.M47.SeedCylinderClock
import PoincareConjecture.Proofs.M47.SeedCylinderSource

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

open Proofs.M47

theorem exists_source_initial_joined_source
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {T q Q tau s base : ℝ} (hQ : 0 < Q) (htau : 0 < tau) (hs : 0 ≤ s)
    (hbaseClock : base = T + s / q)
    {U : Set C.carrier} {V Up : Set (F.slice T).carrier} {J : Set ℝ}
    (old : SurgeryFlowCylinder F C T q (Icc (-tau) 0) U)
    (recent : SurgeryFlowCylinder F (F.slice T) T q J V)
    (hJ : Icc (0 : ℝ) s ⊆ J)
    (D : PartialDiffeomorph (𝓡 3) (𝓡 3) C.carrier (F.slice T).carrier ∞)
    (hDsource : D.source = U)
    (hDpoint : ∀ x, HEq (D x) (old.forward 0 ⟨by linarith only [htau], le_rfl⟩ x))
    (hbased : ∀ hz x, x ∈ V → HEq (recent.forward 0 hz x) x)
    (hUp : IsOpen Up) (hne : Up.Nonempty) (hUpD : Up ⊆ D.target) (hUpV : Up ⊆ V) :
    let H := Q / q
    let dr := H * s
    let dold := dr + H * tau
    ∃ hOldTimes : MapsTo (fun u : ℝ => (u + dr) / H)
        (Icc (-dold) (-dr)) (Icc (-tau) 0),
    ∃ hRecentTimes : MapsTo (fun u : ℝ => s + u / H) (Icc (-dr) 0) J,
    ∃ e : SurgeryFlowCylinder F (F.slice T) base Q (Icc (-dold) 0) Up,
      (∀ u (hu : u ∈ Icc (-dold) (-dr)) (hu' : u ∈ Icc (-dold) 0),
        ∀ x ∈ Up,
          (⟨base + u / Q, e.forward u hu' x⟩ : Σ t, (F.slice t).carrier) =
            ⟨T + ((u + dr) / H) / q,
              old.forward ((u + dr) / H) (hOldTimes hu) (D.symm x)⟩) ∧
      ∀ u (hu : u ∈ Icc (-dr) 0) (hu' : u ∈ Icc (-dold) 0) x,
        (⟨base + u / Q, e.forward u hu' x⟩ : Σ t, (F.slice t).carrier) =
          ⟨T + (s + u / H) / q, recent.forward (s + u / H) (hRecentTimes hu) x⟩ := by
  let H := Q / q
  let dr := H * s
  let dold := dr + H * tau
  let phiOld := fun u : ℝ => (u + dr) / H
  let phiRecent := fun u : ℝ => s + u / H
  have hq : 0 < q := old.scale_pos
  have hH : 0 < H := div_pos hQ hq
  have hdr : 0 ≤ dr := mul_nonneg hH.le hs
  have horder : -dold ≤ -dr := by
    dsimp only [dold]
    nlinarith only [mul_pos hH htau]
  have hOldTimes : MapsTo phiOld (Icc (-dold) (-dr)) (Icc (-tau) 0) := by
    intro u hu
    constructor
    · apply (le_div_iff₀ hH).mpr
      dsimp only [dold] at hu
      nlinarith only [hu.1]
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hu.2]) hH.le
  have hRecentRaw : MapsTo phiRecent (Icc (-dr) 0) (Icc (0 : ℝ) s) := by
    intro u hu
    have hlo : -s ≤ u / H := (le_div_iff₀ hH).mpr (by
      dsimp only [dr] at hu
      nlinarith only [hu.1])
    have hhi : u / H ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu.2 hH.le
    constructor <;> dsimp only [phiRecent] <;> linarith only [hlo, hhi]
  have hRecentTimes : MapsTo phiRecent (Icc (-dr) 0) J := fun _ hu => hJ (hRecentRaw hu)
  have hmonoOld : StrictMonoOn phiOld (Icc (-dold) (-dr)) := by
    intro u _ v _ huv
    exact (div_lt_div_iff_of_pos_right hH).mpr (by linarith only [huv])
  have hmonoRecent : StrictMonoOn phiRecent (Icc (-dr) 0) := by
    intro u _ v _ huv
    have h := (div_lt_div_iff_of_pos_right hH).mpr huv
    change s + u / H < s + v / H
    linarith only [h]
  have hclockOld : ∀ u ∈ Icc (-dold) (-dr), base + u / Q = T + phiOld u / q := by
    intro u _
    rw [hbaseClock]
    dsimp only [phiOld, dr, H]
    field_simp
    ring
  have hclockRecent : ∀ u ∈ Icc (-dr) 0, base + u / Q = T + phiRecent u / q := by
    intro u _
    rw [hbaseClock]
    dsimp only [phiRecent, H]
    field_simp
    ring
  let oldShift := seedCylinderReclock old hQ ordConnected_Icc phiOld hOldTimes hmonoOld hclockOld
  have hmaps : MapsTo D.symm Up U := by
    intro x hx
    rw [← hDsource]
    exact D.map_target (hUpD hx)
  let past := seedCylinderSource oldShift D.symm Up hUpD hmaps
  let recentShift := seedCylinderReclock recent hQ ordConnected_Icc
    phiRecent hRecentTimes hmonoRecent hclockRecent
  let future := recentShift.restrict Subset.rfl ordConnected_Icc hUpV
  have hOldZero : phiOld (-dr) = 0 := by simp only [phiOld, neg_add_cancel, zero_div]
  have hRecentZero : phiRecent (-dr) = 0 := by
    dsimp only [phiRecent, dr]
    field_simp
    ring
  have hzOld : (0 : ℝ) ∈ Icc (-tau) 0 := ⟨by linarith only [htau], le_rfl⟩
  have hzRecent : (0 : ℝ) ∈ J := hJ ⟨le_rfl, hs⟩
  have holdAtZero (r : ℝ) (hr : r ∈ Icc (-tau) 0) (hr0 : r = 0) (x : C.carrier) :
      HEq (old.forward r hr x) (old.forward 0 hzOld x) := by
    subst r
    rfl
  have hrecentAtZero (r : ℝ) (hr : r ∈ J) (hr0 : r = 0) (x : (F.slice T).carrier) :
      HEq (recent.forward r hr x) (recent.forward 0 hzRecent x) := by
    subst r
    rfl
  have hjoin : ∀ x ∈ Up, past.forward (-dr) ⟨horder, le_rfl⟩ x =
      future.forward (-dr) ⟨le_rfl, neg_nonpos.mpr hdr⟩ x := by
    intro x hx
    have hp := seedCylinderReclock_forward_heq old hQ ordConnected_Icc phiOld
      hOldTimes hmonoOld hclockOld (-dr) ⟨horder, le_rfl⟩ (D.symm x)
    have hOldPoint : HEq (past.forward (-dr) ⟨horder, le_rfl⟩ x) x :=
      (hp.trans (holdAtZero _ _ hOldZero _)).trans
        ((hDpoint (D.symm x)).symm.trans (heq_of_eq (D.right_inv (hUpD hx))))
    have hf := seedCylinderReclock_forward_heq recent hQ ordConnected_Icc phiRecent
      hRecentTimes hmonoRecent hclockRecent (-dr) ⟨le_rfl, neg_nonpos.mpr hdr⟩ x
    have hRecentPoint : HEq (future.forward (-dr) ⟨le_rfl, neg_nonpos.mpr hdr⟩ x) x :=
      (hf.trans (hrecentAtZero _ _ hRecentZero _)).trans (hbased hzRecent x (hUpV hx))
    exact eq_of_heq (hOldPoint.trans hRecentPoint.symm)
  obtain ⟨e, hfuture, hpast⟩ := exists_source_initial_joined_cylinder
    past future horder (neg_nonpos.mpr hdr) hUp hne hjoin
  refine ⟨hOldTimes, hRecentTimes, e, ?_, ?_⟩
  · intro u hu hu' x hx
    apply Sigma.ext (hclockOld u hu)
    exact (heq_of_eq (hpast u hu hu' x hx)).trans
      (seedCylinderReclock_forward_heq old hQ ordConnected_Icc phiOld
        hOldTimes hmonoOld hclockOld u hu (D.symm x))
  · intro u hu hu' x
    apply Sigma.ext (hclockRecent u hu)
    exact (heq_of_eq (hfuture u hu hu' x)).trans
      (seedCylinderReclock_forward_heq recent hQ ordConnected_Icc phiRecent
        hRecentTimes hmonoRecent hclockRecent u hu x)

end PoincareConjecture.M47
