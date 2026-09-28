import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.HighestAxis
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.PeriodicDeletion



set_option autoImplicit false
open Set Geometry unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)

theorem exists_strict_plane_periodic_contact_reduction {r : ℝ → P2}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (hi : InjOn r (Icc 0 1))
    (hheight : ∀ t ∈ Icc (0 : ℝ) 1, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1)
    (hbottom : (r 0).2 = -1) (htop : (r 1).2 = 1)
    (hang0 : (r 0).1 = 0) (hang1 : (r 1).1 = 0)
    (htranslate : ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ∀ k : ℤ, r s = r t + (32 * (k : ℝ), 0) → s = t ∧ k = 0)
    {c : ℝ} (hc : 0 < c)
    (hfinite : {x ∈ Icc (0 : ℝ) 1 | ∃ k : ℤ, (r x).1 = c + 32 * (k : ℝ)}.Finite)
    (hreg : ∀ (x : ℝ) (k : ℤ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c + 32 * (k : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).1 - (c + 32 * (k : ℝ)) = m * (y - x))
    (habove : ∃ t ∈ Icc (0 : ℝ) 1, c < (r t).1) :
    ∃ (n : ℤ) (lo hi : ℝ) (D D' : Set P2) (H J : I → P2 ≃ₜ P2)
        (F Fi G Gi : (ℝ × P2) → P2),
      -32 < lo ∧ lo < 0 ∧ 0 < hi ∧ hi < 32 ∧ hi - lo < 32 ∧
      IsFinitePLBallPair P2 D (frontier D) ∧ IsFinitePLBallPair P2 D' (frontier D') ∧
      D ∪ D' ⊆ Ioo (-1 : ℝ) 1 ×ˢ Icc lo hi ∧
      H 0 = Homeomorph.refl P2 ∧ J 0 = Homeomorph.refl P2 ∧
      Continuous (fun z : I × P2 => H z.1 z.2) ∧
      Continuous (fun z : I × P2 => (H z.1).symm z.2) ∧
      Continuous (fun z : I × P2 => J z.1 z.2) ∧
      Continuous (fun z : I × P2 => (J z.1).symm z.2) ∧
      (∀ t : I, ∀ x : P2, x ∉ interior D → H t x = x) ∧
      (∀ t : I, ∀ x : P2, x ∉ interior D' → J t x = x) ∧
      (∀ t : I, ∀ x : P2, F ((t : ℝ), x) = H t x) ∧
      (∀ t : I, ∀ x : P2, Fi ((t : ℝ), x) = (H t).symm x) ∧
      (∀ t : I, ∀ x : P2, G ((t : ℝ), x) = J t x) ∧
      (∀ t : I, ∀ x : P2, Gi ((t : ℝ), x) = (J t).symm x) ∧
      (∀ K : SimplicialComplex ℝ P2, K.faces.Finite →
        FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn G (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn Gi (Icc (0 : ℝ) 1 ×ˢ K.space)) ∧
      let Q (j : ℤ) := annularLiftAboveAxis r (c + 32 * (n : ℝ) + 32 * (j : ℝ))
      {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (J 1 (H 1 (Q j x))).2 = 0}.Finite ∧
      {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (J 1 (H 1 (Q j x))).2 = 0}.ncard + 2 =
        {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c + 32 * (j : ℝ)}.ncard ∧
      (∀ j : ℤ, ∀ x ∈ Icc (0 : ℝ) 1, (J 1 (H 1 (Q j x))).2 = 0 →
        ∃ u v m : ℝ, 0 ≤ u ∧ u < x ∧ x < v ∧ v ≤ 1 ∧ m ≠ 0 ∧
          ∀ y ∈ Icc u v, (J 1 (H 1 (Q j y))).2 = m * (y - x)) := by
  obtain ⟨c₀, d, k, a, b, u, v, B, _, ⟨n, hn⟩, hd, hd32, ha, hab, hb, huv,
    hpairs, hball, _, hband, hBaxis, hwhole, hbase⟩ :=
    exists_narrow_empty_returning_bigon_of_lift hr hi hheight hproper hbottom htop
      hang0 hang1 htranslate hc hfinite hreg habove
  have hphase (j : ℤ) : c₀ + 32 * (j : ℝ) = c + 32 * ((n + j : ℤ) : ℝ) := by
    rw [hn, Int.cast_add]
    ring
  have hreg' : ∀ (x : ℝ) (j : ℤ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c₀ + 32 * (j : ℝ) →
      ∃ a b m : ℝ, 0 ≤ a ∧ a < x ∧ x < b ∧ b ≤ 1 ∧ m ≠ 0 ∧
        ∀ y ∈ Icc a b, (r y).1 - (c₀ + 32 * (j : ℝ)) = m * (y - x) := by
    intro x j hx hz
    rw [hphase] at hz ⊢
    exact hreg x (n + j) hx hz
  have hcontacts : {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c₀ + 32 * (j : ℝ)} =
      {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c + 32 * (j : ℝ)} := by
    ext x
    constructor
    · rintro ⟨hx, j, hj⟩
      exact ⟨hx, n + j, (hphase j) ▸ hj⟩
    · rintro ⟨hx, j, hj⟩
      refine ⟨hx, j - n, ?_⟩
      rw [hphase, show n + (j - n) = j by omega]
      exact hj
  have hfinite' : {x ∈ Icc (0 : ℝ) 1 | ∃ j : ℤ, (r x).1 = c₀ + 32 * (j : ℝ)}.Finite :=
    hcontacts.symm ▸ hfinite
  obtain ⟨ε, D, D', H, J, F, Fi, G, Gi, hε, hwidth, hD, hD', hDU,
    hzero, jzero, hcH, hciH, hcJ, hciJ, hfixH, hfixJ, _, _, _,
    hF, hFi, hG, hGi, hPL, _, hregular, hcount⟩ :=
    exists_periodic_empty_bigon_two_moves hr hi htranslate hd32 hreg' k ha hab hb
      huv hpairs hball hband hBaxis hwhole hbase
  obtain ⟨hfin, hcount, _⟩ := hcount hfinite'
  rw [hcontacts] at hcount
  refine ⟨n, -ε, d + ε, D, D', H, J, F, Fi, G, Gi,
    by linarith, by linarith, by linarith, by linarith, by linarith,
    hD, hD', (fun x hx => ⟨(hDU hx).1, Ioo_subset_Icc_self (hDU hx).2⟩),
    hzero, jzero, hcH, hciH, hcJ, hciJ, hfixH, hfixJ, hF, hFi, hG, hGi, hPL, ?_⟩
  rw [hn] at hfin hcount hregular
  exact ⟨hfin, hcount, hregular⟩

end PoincareConjecture.M76.Dehn
