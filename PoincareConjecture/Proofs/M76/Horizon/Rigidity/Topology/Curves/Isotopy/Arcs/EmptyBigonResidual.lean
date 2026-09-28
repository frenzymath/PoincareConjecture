import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.EmptyBigonParameters
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.PeriodicResidual

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Z" => ((Prod.snd : P2 → ℝ) ⁻¹' ({0} : Set ℝ))

theorem exists_periodic_empty_bigon_residual {r : ℝ → P2}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (hi : InjOn r (Icc 0 1))
    (htranslate : ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ∀ k : ℤ, r s = r t + (32 * (k : ℝ), 0) → s = t ∧ k = 0)
    {c d : ℝ} (hd : d < 32)
    (hreg : ∀ (x : ℝ) (j : ℤ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c + 32 * (j : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).1 - (c + 32 * (j : ℝ)) = m * (y - x))
    (k : ℤ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    {u v : P2} {B : Set P2}
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
    let q := annularLiftAboveAxis r (c + 32 * (k : ℝ))
    ∃ (ε l t : ℝ) (T : SimplicialComplex ℝ P2) (E : Set P2),
      0 < ε ∧ d + 2 * ε < 32 ∧
      B ⊆ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-ε) (d + ε) ∧
      0 < l ∧ l < a ∧ b < t ∧ t < 1 ∧ T.faces.Finite ∧
      T.space = q '' Icc l a ∪ q '' Icc b t ∧
      (∀ x ∈ T.space, x.2 ≤ 0) ∧
      (∀ x ∈ T.space, x.2 = 0 → x = q a ∨ x = q b) ∧
      (∃ m n : ℝ, 0 < m ∧ n < 0 ∧
        (∀ s ∈ Icc l a, (q s).2 = m * (s - a)) ∧
        (∀ s ∈ Icc b t, (q s).2 = n * (s - b))) ∧
      IsCompact E ∧ Disjoint B E ∧
      E ⊆ (⋃ j : ℤ, annularLiftAboveAxis r (c + 32 * (j : ℝ)) '' Icc (0 : ℝ) 1) \
        (q '' Ioo a b) ∧
      (∀ s ∈ Icc (0 : ℝ) 1 \ Ioo l t, q s ∈ E) ∧
      (((⋃ j : ℤ, annularLiftAboveAxis r (c + 32 * (j : ℝ)) '' Icc (0 : ℝ) 1) ∩
        (Ioo (-1 : ℝ) 1 ×ˢ Ioo (-ε) (d + ε))) \ (q '' Ioo a b)) ⊆ T.space ∪ E := by
  let Q (j : ℤ) := annularLiftAboveAxis r (c + 32 * (j : ℝ))
  have hqi := injOn_annularLiftAboveAxis hi (c + 32 * (k : ℝ))
  obtain ⟨hqa, hqb, hpositive⟩ := empty_returning_bigon_parameter_data hqi ha hab hb hpairs
    (fun _ hx => hball.1 (Or.inl hx)) (fun _ hx => (hband hx).2.1) hBaxis
    (fun _ hx => mem_iUnion.mpr ⟨k, hx⟩) hbase
  have hend (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) (hz : (Q k x).2 = 0) :
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (Q k y).2 - 0 = m * (y - x) := by
    have he : (r x).1 = c + 32 * (k : ℝ) := sub_eq_zero.mp hz
    obtain ⟨a, b, m, ha, hax, hxb, hb, hm, hformula⟩ := hreg x k hx he
    refine ⟨a, b, m, ha, hax, hxb, hb, hm, ?_⟩
    intro y hy
    simpa only [Q, annularLiftAboveAxis, sub_zero] using hformula y hy
  obtain ⟨ε, K, hε, hwidth, hBU, hcapture⟩ := exists_narrow_periodic_window (c := c) hr hd hband
  obtain ⟨l, t, T, E, hl, hla, hbt, ht, hT, hTs, hlower, haxis, hslopes,
    hE, hBE, hEs, hEout, hcover⟩ := exists_complete_residual_of_finite_window Q
      (fun j => finitePL_annularLiftAboveAxis hr _) (fun i j hij =>
        annular_translated_upper_images_disjoint htranslate c hij) k hqi hab hpositive
      (hend a ⟨ha, hab.le.trans hb⟩ hqa) (hend b ⟨ha.trans hab.le, hb⟩ hqb)
      hwhole K hcapture
  refine ⟨ε, l, t, T, E, hε, hwidth, hBU, hl, hla, hbt, ht, hT, hTs,
    hlower, haxis, hslopes, hE, hBE, hEout, ?_, hcover⟩
  intro s hs
  rw [hEs]
  apply Or.inl
  by_cases hsl : s ≤ l
  · exact Or.inl (mem_image_of_mem (Q k) ⟨hs.1.1, hsl⟩)
  · exact Or.inr (mem_image_of_mem (Q k)
      ⟨le_of_not_gt (fun hst => hs.2 ⟨lt_of_not_ge hsl, hst⟩), hs.1.2⟩)

end PoincareConjecture.M76.Dehn
