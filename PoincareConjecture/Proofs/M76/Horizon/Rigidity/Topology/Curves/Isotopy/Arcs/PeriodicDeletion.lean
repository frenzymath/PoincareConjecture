import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.PeriodicFlattening
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.MotionImage
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.FlattenedDeletion
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.PeriodicContacts

set_option autoImplicit false
open Set Geometry unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Z" => ((Prod.snd : P2 → ℝ) ⁻¹' ({0} : Set ℝ))

theorem exists_periodic_empty_bigon_two_moves {r : ℝ → P2}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (hi : InjOn r (Icc 0 1))
    (htranslate : ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ∀ k : ℤ, r s = r t + (32 * (k : ℝ), 0) → s = t ∧ k = 0)
    {c d : ℝ} (hd : d < 32)
    (hreg : ∀ (x : ℝ) (j : ℤ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c + 32 * (j : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).1 - (c + 32 * (j : ℝ)) = m * (y - x))
    (k : ℤ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    {u v : P2} (huv : u.1 < v.1) {B : Set P2}
    (hpairs : ({u, v} : Set P2) = {annularLiftAboveAxis r (c + 32 * (k : ℝ)) a,
      annularLiftAboveAxis r (c + 32 * (k : ℝ)) b})
    (hball : IsFinitePLBallPair P2 B
      ((annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc a b) ∪ segment ℝ u v))
    (hband : B ⊆ Ioo (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) d)
    (hBaxis : B ∩ Z = segment ℝ u v)
    (hwhole : B ∩ (⋃ j : ℤ, annularLiftAboveAxis r (c + 32 * (j : ℝ)) '' Icc (0 : ℝ) 1) =
      annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc a b)
    (hbase : (⋃ j : ℤ, annularLiftAboveAxis r (c + 32 * (j : ℝ)) '' Icc (0 : ℝ) 1) ∩
      segment ℝ u v = {u, v}) :
    let Q (j : ℤ) := annularLiftAboveAxis r (c + 32 * (j : ℝ))
    ∃ (ε : ℝ) (D D' : Set P2) (H J : I → P2 ≃ₜ P2)
        (F Fi G Gi : (ℝ × P2) → P2),
      0 < ε ∧ d + 2 * ε < 32 ∧
      IsFinitePLBallPair P2 D (frontier D) ∧ IsFinitePLBallPair P2 D' (frontier D') ∧
      D ∪ D' ⊆ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-ε) (d + ε) ∧
      H 0 = Homeomorph.refl P2 ∧ J 0 = Homeomorph.refl P2 ∧
      Continuous (fun z : I × P2 => H z.1 z.2) ∧
      Continuous (fun z : I × P2 => (H z.1).symm z.2) ∧
      Continuous (fun z : I × P2 => J z.1 z.2) ∧
      Continuous (fun z : I × P2 => (J z.1).symm z.2) ∧
      (∀ t : I, ∀ x : P2, x ∉ interior D → H t x = x) ∧
      (∀ t : I, ∀ x : P2, x ∉ interior D' → J t x = x) ∧
      (∀ t : I, ∀ (j : ℤ), j ≠ k → ∀ s ∈ Icc (0 : ℝ) 1,
        H t (Q j s) = Q j s ∧ J t (Q j s) = Q j s) ∧
      {x ∈ Icc (0 : ℝ) 1 | (J 1 (H 1 (Q k x))).2 = 0} =
        {x ∈ Icc (0 : ℝ) 1 | (Q k x).2 = 0} \ {a, b} ∧
      (∀ x ∈ Icc (0 : ℝ) 1, (J 1 (H 1 (Q k x))).2 = 0 →
        ∃ η : ℝ, 0 < η ∧ ∀ t : I, ∀ y ∈ Icc (0 : ℝ) 1,
          |y - x| < η → J t (H 1 (Q k y)) = Q k y) ∧
      (∀ t : I, ∀ x : P2, F ((t : ℝ), x) = H t x) ∧
      (∀ t : I, ∀ x : P2, Fi ((t : ℝ), x) = (H t).symm x) ∧
      (∀ t : I, ∀ x : P2, G ((t : ℝ), x) = J t x) ∧
      (∀ t : I, ∀ x : P2, Gi ((t : ℝ), x) = (J t).symm x) ∧
      (∀ K : SimplicialComplex ℝ P2, K.faces.Finite →
        FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn G (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn Gi (Icc (0 : ℝ) 1 ×ˢ K.space)) ∧
      {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (J 1 (H 1 (Q j x))).2 = 0} =
        {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c + 32 * (j : ℝ)} \ {a, b} ∧
      (∀ j : ℤ, ∀ x ∈ Icc (0 : ℝ) 1, (J 1 (H 1 (Q j x))).2 = 0 →
        ∃ u v m : ℝ, 0 ≤ u ∧ u < x ∧ x < v ∧ v ≤ 1 ∧ m ≠ 0 ∧
          ∀ y ∈ Icc u v, (J 1 (H 1 (Q j y))).2 = m * (y - x)) ∧
      ({x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c + 32 * (j : ℝ)}.Finite →
        {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (J 1 (H 1 (Q j x))).2 = 0}.Finite ∧
        {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (J 1 (H 1 (Q j x))).2 = 0}.ncard + 2 =
          {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c + 32 * (j : ℝ)}.ncard ∧
        {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (J 1 (H 1 (Q j x))).2 = 0}.ncard <
          {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c + 32 * (j : ℝ)}.ncard) := by
  let Q (j : ℤ) := annularLiftAboveAxis r (c + 32 * (j : ℝ))
  have hqPL := finitePL_annularLiftAboveAxis hr (c + 32 * (k : ℝ))
  have hqi := injOn_annularLiftAboveAxis hi (c + 32 * (k : ℝ))
  have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := fun x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩
  have hseg : segment ℝ u v = segment ℝ (Q k a) (Q k b) := by
    rw [← convexHull_pair, hpairs, convexHull_pair]
  obtain ⟨hqa, hqb, hpositive⟩ := empty_returning_bigon_parameter_data hqi ha hab hb hpairs
    (fun _ hx => hball.1 (Or.inl hx)) (fun _ hx => (hband hx).2.1) hBaxis
    (fun _ hx => mem_iUnion.mpr ⟨k, hx⟩) hbase
  have hend (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hz : (Q k x).2 = 0) :
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (Q k y).2 = m * (y - x) := by
    exact hreg x k hx (sub_eq_zero.mp hz)
  obtain ⟨ε, D, H, F, Fi, hε, hwidth, hD, hDU, hzero, hc, hci, hfix, hcopies,
    hflat, hF, hFi, hPL⟩ := exists_periodic_empty_bigon_flattening hr hi htranslate hd hreg k
      ha hab hb huv hpairs hball hband hBaxis hwhole hbase
  let q : ℝ → P2 := fun x => H 1 (Q k x)
  have hq : FinitePiecewiseAffineOn q (Icc 0 1) :=
    finitePL_curve_after_joint_motion hqPL H F (fun K hK => (hPL K hK).1) hF 1
  have hqi' : InjOn q (Icc 0 1) := fun x hx y hy he => hqi hx hy ((H 1).injective he)
  have hfixed : ∀ x ∈ Icc (0 : ℝ) 1 \ Ioo a b, q x = Q k x := by
    intro x hx
    apply hcopies 1 k x hx.1
    rintro ⟨y, hy, he⟩
    exact hx.2 ((hqi (hsub (Ioo_subset_Icc_self hy)) hx.1 he) ▸ hy)
  have hqflat : q '' Icc a b = segment ℝ (Q k a) (Q k b) := by
    rw [← hseg]
    simpa only [q, ← image_comp, Function.comp_def] using hflat
  obtain ⟨ε₀, L, R, T, E, hε₀, _, hBU₀, hL, hLa, hbR, hR, _, hTs, _, _,
    ⟨m, n, hm, hn, hmf, hnf⟩, hE, hBE, _, hfar, hcover⟩ :=
    exists_periodic_empty_bigon_residual hr hi htranslate hd hreg k
      ha hab hb hpairs hball hband hBaxis hwhole hbase
  let U := (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-ε₀) (d + ε₀)) ∩
    (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-ε) (d + ε))
  have hU : IsOpen U := (isOpen_Ioo.prod isOpen_Ioo).inter (isOpen_Ioo.prod isOpen_Ioo)
  have hbaseU : segment ℝ (Q k a) (Q k b) ⊆ U := by
    intro x hx
    have hxB := hball.1 (Or.inr (hseg.symm ▸ hx))
    have hh := hband hxB
    exact ⟨hBU₀ hxB, hh.1, by linarith [hh.2.1], by linarith [hh.2.2]⟩
  have hbaseE : Disjoint (segment ℝ (Q k a) (Q k b)) E :=
    hBE.mono_left (fun x hx => hball.1 (Or.inr (hseg.symm ▸ hx)))
  obtain ⟨D', J, G, Gi, hD', hD'U, jzero, jc, jci, jfix, jE, hdelete, hG, hGi,
    hGPL, l, t, _, _, _, _, _, hgerm⟩ := exists_flattened_excursion_contact_deletion
      hqPL hq hqi' hL hLa hab hbR hR hpositive
      (hend a ⟨ha, hab.le.trans hb⟩ hqa) (hend b ⟨ha.trans hab.le, hb⟩ hqb)
      hfixed hqflat hm hn hmf hnf hU hbaseU hE.isClosed hbaseE hfar
  have hother : ∀ t : I, ∀ j : ℤ, j ≠ k → ∀ s ∈ Icc (0 : ℝ) 1,
      H t (Q j s) = Q j s ∧ J t (Q j s) = Q j s := by
    intro t j hj s hs
    have hdis := annular_translated_upper_images_disjoint htranslate c hj
    have hout : Q j s ∉ Q k '' Ioo a b := fun hx => disjoint_left.mp hdis
      (mem_image_of_mem (Q j) hs) (image_mono (Ioo_subset_Icc_self.trans hsub) hx)
    refine ⟨hcopies t j s hs hout, ?_⟩
    by_cases hin : Q j s ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-ε₀) (d + ε₀)
    · have hh := hcover ⟨⟨mem_iUnion.mpr ⟨j, mem_image_of_mem (Q j) hs⟩, hin⟩, hout⟩
      rcases hh with hT | hE
      · rw [hTs] at hT
        have hk : Q j s ∈ Q k '' Icc (0 : ℝ) 1 := by
          rcases hT with ⟨x, hx, he⟩ | ⟨x, hx, he⟩
          · exact ⟨x, ⟨hL.le.trans hx.1, hx.2.trans (hab.le.trans hb)⟩, he⟩
          · exact ⟨x, ⟨(ha.trans hab.le).trans hx.1, hx.2.trans hR.le⟩, he⟩
        exact (disjoint_left.mp hdis (mem_image_of_mem (Q j) hs) hk).elim
      · exact jE t _ hE
    · exact jfix t _ (fun h => hin (hD'U (interior_subset h)).1)
  have hunchanged : ∀ j : ℤ, j ≠ k → ∀ s ∈ Icc (0 : ℝ) 1,
      J 1 (H 1 (Q j s)) = Q j s := by
    intro j hj s hs
    rw [(hother 1 j hj s hs).1, (hother 1 j hj s hs).2]
  refine ⟨ε, D, D', H, J, F, Fi, G, Gi, hε, hwidth, hD, hD',
    union_subset hDU (fun _ hx => (hD'U hx).2), hzero, jzero, hc, hci, jc, jci, hfix,
    jfix, hother, hdelete, hgerm, hF, hFi, hG, hGi, ?_, ?_, ?_, ?_⟩
  · intro K hK
    exact ⟨(hPL K hK).1, (hPL K hK).2, (hGPL K hK).1, (hGPL K hK).2⟩
  · exact periodic_contacts_eq_sdiff_of_selected_copy_deletion
      (sub_eq_zero.mp hqa) (sub_eq_zero.mp hqb) hunchanged hdelete
  · apply periodic_axis_germs_of_selected_copy_deletion
      (fun x hx j => hreg x j hx) hunchanged hdelete
    intro x hx hz
    obtain ⟨η, hη, hlocal⟩ := hgerm x hx hz
    exact ⟨η, hη, fun y hy hnear => hlocal 1 y hy hnear⟩
  · intro hfinite
    exact periodic_contact_count_decreases_of_selected_copy_deletion hab.ne
      ⟨ha, hab.le.trans hb⟩ ⟨ha.trans hab.le, hb⟩
      (sub_eq_zero.mp hqa) (sub_eq_zero.mp hqb) hfinite hunchanged hdelete

end PoincareConjecture.M76.Dehn
