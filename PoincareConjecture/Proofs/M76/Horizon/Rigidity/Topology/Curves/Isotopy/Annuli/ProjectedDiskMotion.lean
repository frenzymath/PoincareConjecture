import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.ProjectedDiskGeometry
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Annuli.DiskFamilyExtension



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry PLAnnularStrip Topology

namespace PoincareConjecture.M76.Dehn

local notation "I" => unitInterval
local notation "P2" => (ℝ × ℝ)
local notation "Ann" => squareAnnulus 8 1

theorem exists_projected_annular_disk_motion_at_phase (c : ℝ)
    {D : Set P2} {a b : ℝ}
    (hD : IsFinitePLBallPair P2 D (frontier D)) (hwidth : b - a < 32)
    (hstrip : D ⊆ Ioo (-1 : ℝ) 1 ×ˢ Icc a b)
    (H : I → P2 ≃ₜ P2) (hzero : H 0 = Homeomorph.refl P2)
    (hfix : ∀ t x, x ∉ interior D → H t x = x)
    (hc : Continuous (fun z : I × P2 => H z.1 z.2))
    (hci : Continuous (fun z : I × P2 => (H z.1).symm z.2))
    (f fi : (ℝ × P2) → P2)
    (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1 ×ˢ D))
    (hfi : FinitePiecewiseAffineOn fi (Icc (0 : ℝ) 1 ×ˢ D))
    (hv : ∀ t : I, ∀ x : D, f (t, x) = H t x)
    (hiv : ∀ t : I, ∀ x : D, fi (t, x) = (H t).symm x) :
    ∃ (A : I → Ann ≃ₜ Ann) (F Fi : (ℝ × P2) → P2),
      A 0 = Homeomorph.refl Ann ∧
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      (∀ t : I, ∀ x : Ann, F (t, x) = (A t x : P2)) ∧
      (∀ t : I, ∀ x : Ann, Fi (t, x) = ((A t).symm x : P2)) ∧
      Continuous (fun z : I × Ann => A z.1 z.2) ∧
      Continuous (fun z : I × Ann => (A z.1).symm z.2) ∧
      (∀ t side z, A t (annulusRimPoint side z) = annulusRimPoint side z) ∧
      (∀ t (x : Ann), (x : P2) ∉ interior ((annularLiftProjectionAt c) '' D) → A t x = x) ∧
      (∀ t (x : Ann) (y : P2), y ∈ D → (x : P2) = (annularLiftProjectionAt c) y →
        (A t x : P2) = (annularLiftProjectionAt c) (H t y)) ∧
      ∀ t (x : Ann) (y : P2) (k : ℤ), y ∈ D →
        (x : P2) = (annularLiftProjectionAt c) (y + (0, 32 * (k : ℝ))) →
        (A t x : P2) = (annularLiftProjectionAt c) (H t y + (0, 32 * (k : ℝ))) := by
  obtain ⟨_, hinj, hS, hfront, hdepth, Q, hQ, hQv⟩ :=
    exists_finitePL_projected_annular_disk_at c hD hwidth hstrip
  let S := (annularLiftProjectionAt c) '' D
  have hfixoff (t : I) (x : P2) (hx : x ∉ D) : H t x = x :=
    hfix t x (fun hi => hx (interior_subset hi))
  have hmapsD (t : I) : MapsTo (H t) D D := by
    intro x hx
    by_contra hn
    have heq : H t x = x := (H t).injective (hfixoff t (H t x) hn)
    exact hn (heq.symm ▸ hx)
  have hmemD (t : I) (x : P2) : x ∈ D ↔ H t x ∈ D := by
    constructor
    · intro hx
      exact hmapsD t hx
    · intro hx
      by_contra hn
      exact hn ((hfixoff t x hn) ▸ hx)
  let J (t : I) : D ≃ₜ D := (H t).subtype (hmemD t)
  have hJc : Continuous (fun z : I × D => J z.1 z.2) :=
    (hc.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  have hJci : Continuous (fun z : I × D => (J z.1).symm z.2) :=
    (hci.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
  let K (t : I) : S ≃ₜ S := Q.symm.trans ((J t).trans Q)
  have hKc : Continuous (fun z : I × S => K z.1 z.2) :=
    Q.continuous.comp (hJc.comp (continuous_fst.prodMk (Q.symm.continuous.comp continuous_snd)))
  have hKci : Continuous (fun z : I × S => (K z.1).symm z.2) :=
    Q.continuous.comp (hJci.comp (continuous_fst.prodMk (Q.symm.continuous.comp continuous_snd)))
  have hKzero : K 0 = Homeomorph.refl S := by
    apply Homeomorph.ext
    intro x
    change Q (J 0 (Q.symm x)) = x
    have hj : J 0 (Q.symm x) = Q.symm x := Subtype.ext (by
      change H 0 (Q.symm x) = (Q.symm x : P2)
      rw [hzero]
      rfl)
    rw [hj, Q.apply_symm_apply]
  have hKfix (t : I) (x : S) (hx : (x : P2) ∈ frontier S) : K t x = x := by
    have hx' : (Q.symm x : P2) ∈ frontier D := by
      obtain ⟨y, hy, hxy⟩ := hfront.symm ▸ hx
      have hyD := hD.1 hy
      have hQxy : Q ⟨y, hyD⟩ = x := Subtype.ext ((hQv _).trans hxy)
      rw [← hQxy, Q.symm_apply_apply]
      exact hy
    have hj : J t (Q.symm x) = Q.symm x := Subtype.ext (hfix t _ hx'.2)
    change Q (J t (Q.symm x)) = x
    rw [hj, Q.apply_symm_apply]
  obtain ⟨q, hq, hqv⟩ := CollarIsotopy.exists_conjugate_joint_finitePL
    Q hQ J f hf hv
  obtain ⟨qi, hqi, hqiv⟩ := CollarIsotopy.exists_conjugate_joint_finitePL
    Q hQ (fun t => (J t).symm) fi hfi hiv
  obtain ⟨A, F, Fi, hA0, hF, hFi, hFv, hFiv, hAc, hAci, hrims, hoff, hlocal⟩ :=
    exists_annular_motion_of_closed_disk_family hS.isCompact.isClosed hdepth K hKzero
      hKfix hKc hKci q qi hq hqi hqv hqiv
  have haction (t : I) (x : Ann) (y : P2) (hy : y ∈ D)
      (hxy : (x : P2) = (annularLiftProjectionAt c) y) :
      (A t x : P2) = (annularLiftProjectionAt c) (H t y) := by
    let z : S := Q ⟨y, hy⟩
    have hz : (z : P2) = (x : P2) := (hQv _).trans hxy.symm
    have hzAnn : (z : P2) ∈ Ann := hz.symm ▸ x.property
    have hsub : (⟨z, hzAnn⟩ : Ann) = x := Subtype.ext hz
    have h := hlocal t z hzAnn
    rw [hsub] at h
    change (A t x : P2) = (Q (J t (Q.symm (Q ⟨y, hy⟩))) : P2) at h
    rw [Q.symm_apply_apply, hQv] at h
    exact h
  refine ⟨A, F, Fi, hA0, hF, hFi, hFv, hFiv, hAc, hAci, hrims, hoff, haction, ?_⟩
  intro t x y k hy hxy
  rw [annularLiftProjectionAt_period] at hxy ⊢
  exact haction t x y hy hxy

theorem exists_projected_annular_disk_motion
    {D : Set P2} {a b : ℝ}
    (hD : IsFinitePLBallPair P2 D (frontier D)) (hwidth : b - a < 32)
    (hstrip : D ⊆ Ioo (-1 : ℝ) 1 ×ˢ Icc a b)
    (H : I → P2 ≃ₜ P2) (hzero : H 0 = Homeomorph.refl P2)
    (hfix : ∀ t x, x ∉ interior D → H t x = x)
    (hc : Continuous (fun z : I × P2 => H z.1 z.2))
    (hci : Continuous (fun z : I × P2 => (H z.1).symm z.2))
    (f fi : (ℝ × P2) → P2)
    (hf : FinitePiecewiseAffineOn f (Icc (0 : ℝ) 1 ×ˢ D))
    (hfi : FinitePiecewiseAffineOn fi (Icc (0 : ℝ) 1 ×ˢ D))
    (hv : ∀ t : I, ∀ x : D, f (t, x) = H t x)
    (hiv : ∀ t : I, ∀ x : D, fi (t, x) = (H t).symm x) :
    ∃ (A : I → Ann ≃ₜ Ann) (F Fi : (ℝ × P2) → P2),
      A 0 = Homeomorph.refl Ann ∧
      FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ Ann) ∧
      (∀ t : I, ∀ x : Ann, F (t, x) = (A t x : P2)) ∧
      (∀ t : I, ∀ x : Ann, Fi (t, x) = ((A t).symm x : P2)) ∧
      Continuous (fun z : I × Ann => A z.1 z.2) ∧
      Continuous (fun z : I × Ann => (A z.1).symm z.2) ∧
      (∀ t side z, A t (annulusRimPoint side z) = annulusRimPoint side z) ∧
      (∀ t (x : Ann), (x : P2) ∉ interior (annularLiftProjection '' D) → A t x = x) ∧
      (∀ t (x : Ann) (y : P2), y ∈ D → (x : P2) = annularLiftProjection y →
        (A t x : P2) = annularLiftProjection (H t y)) ∧
      ∀ t (x : Ann) (y : P2) (k : ℤ), y ∈ D →
        (x : P2) = annularLiftProjection (y + (0, 32 * (k : ℝ))) →
        (A t x : P2) = annularLiftProjection (H t y + (0, 32 * (k : ℝ))) := by
  have h := exists_projected_annular_disk_motion_at_phase 0 hD hwidth hstrip
    H hzero hfix hc hci f fi hf hfi hv hiv
  rw [annularLiftProjectionAt_zero] at h
  exact h

end PoincareConjecture.M76.Dehn
