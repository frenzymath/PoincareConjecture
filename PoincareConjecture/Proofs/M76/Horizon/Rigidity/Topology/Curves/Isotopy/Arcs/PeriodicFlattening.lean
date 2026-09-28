import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.EmptyBigonResidual
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.ResidualMotion



set_option autoImplicit false
open Set Geometry unitInterval

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Z" => ((Prod.snd : P2 → ℝ) ⁻¹' ({0} : Set ℝ))

theorem exists_periodic_empty_bigon_flattening {r : ℝ → P2}
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
    ∃ (ε : ℝ) (D : Set P2) (H : I → P2 ≃ₜ P2) (F Fi : (ℝ × P2) → P2),
      0 < ε ∧ d + 2 * ε < 32 ∧
      IsFinitePLBallPair P2 D (frontier D) ∧
      D ⊆ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-ε) (d + ε) ∧
      H 0 = Homeomorph.refl P2 ∧
      Continuous (fun z : I × P2 => H z.1 z.2) ∧
      Continuous (fun z : I × P2 => (H z.1).symm z.2) ∧
      (∀ t : I, ∀ x : P2, x ∉ interior D → H t x = x) ∧
      (∀ t : I, ∀ (j : ℤ) (s : ℝ), s ∈ Icc (0 : ℝ) 1 →
        annularLiftAboveAxis r (c + 32 * (j : ℝ)) s ∉
          annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Ioo a b →
        H t (annularLiftAboveAxis r (c + 32 * (j : ℝ)) s) =
          annularLiftAboveAxis r (c + 32 * (j : ℝ)) s) ∧
      H 1 '' (annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc a b) = segment ℝ u v ∧
      (∀ t : I, ∀ x : P2, F ((t : ℝ), x) = H t x) ∧
      (∀ t : I, ∀ x : P2, Fi ((t : ℝ), x) = (H t).symm x) ∧
      ∀ K : SimplicialComplex ℝ P2, K.faces.Finite →
        FinitePiecewiseAffineOn F (Icc (0 : ℝ) 1 ×ˢ K.space) ∧
        FinitePiecewiseAffineOn Fi (Icc (0 : ℝ) 1 ×ˢ K.space) := by
  let Q (j : ℤ) := annularLiftAboveAxis r (c + 32 * (j : ℝ))
  let W := Q k '' Icc a b
  have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := fun x hx => ⟨ha.trans hx.1, hx.2.trans hb⟩
  have hW : IsFinitePLBallPair ℝ W {u, v} := by
    rw [hpairs]
    simpa only [image_pair] using (isFinitePLBallPair_Icc hab).image_of_subset
      (finitePL_annularLiftAboveAxis hr _) hsub (injOn_annularLiftAboveAxis hi _)
  have hWfamily : W ⊆ ⋃ j : ℤ, Q j '' Icc (0 : ℝ) 1 :=
    fun _ hx => mem_iUnion.mpr ⟨k, image_mono hsub hx⟩
  have hWaxis : W ∩ Z = {u, v} := by
    apply Subset.antisymm
    · intro x hx
      exact hbase.subset ⟨hWfamily hx.1, hBaxis.subset ⟨hball.1 (Or.inl hx.1), hx.2⟩⟩
    · intro x hx
      exact ⟨hW.1 hx, (hBaxis.symm.subset (hbase.symm.subset hx).2).2⟩
  have hu0 : u.2 = 0 := (hWaxis.symm.subset (by simp)).2
  have hv0 : v.2 = 0 := (hWaxis.symm.subset (by simp)).2
  obtain ⟨ε, l, s, T, E, hε, hwidth, hBU, _, _, _, _, hT, _, hlower, haxis,
    _, hE, hBE, _, _, hcover⟩ := exists_periodic_empty_bigon_residual hr hi htranslate hd hreg k
      ha hab hb hpairs hball hband hBaxis hwhole hbase
  have haxis' : ∀ x ∈ T.space, x.2 = 0 → x = u ∨ x = v := by
    intro x hx hz
    exact hpairs.symm.subset (haxis x hx hz)
  obtain ⟨D, H, F, Fi, hD, hDU, hzero, hc, hci, hfix, hres, hterminal,
    hF, hFi, hPL⟩ := exists_returning_arc_motion_fixing_residual hW huv hu0 hv0
      (fun x hx => (hband (hball.1 (Or.inl hx))).2.1) hWaxis
      (by simpa only [union_comm] using hball) (isOpen_Ioo.prod isOpen_Ioo)
      hBU hE.isClosed hBE T hT hlower haxis'
  refine ⟨ε, D, H, F, Fi, hε, hwidth, hD, hDU, hzero, hc, hci, hfix,
    ?_, hterminal, hF, hFi, hPL⟩
  intro t j s hs hout
  by_cases hin : Q j s ∈ Ioo (-1 : ℝ) 1 ×ˢ Ioo (-ε) (d + ε)
  · exact hres t _ (hcover ⟨⟨mem_iUnion.mpr ⟨j, mem_image_of_mem (Q j) hs⟩, hin⟩, hout⟩)
  · exact hfix t _ (fun h => hin (hDU (interior_subset h)))

end PoincareConjecture.M76.Dehn
