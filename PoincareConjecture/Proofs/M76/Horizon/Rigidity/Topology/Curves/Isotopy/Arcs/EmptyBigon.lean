import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Arcs.TranslatedComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Topology.Curves.Isotopy.Bigons.CompleteFamily



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

local notation "P2" => (ℝ × ℝ)
local notation "Z" => ((Prod.snd : P2 → ℝ) ⁻¹' ({0} : Set ℝ))

theorem exists_empty_returning_bigon_of_lift {r : ℝ → P2}
    (hr : FinitePiecewiseAffineOn r (Icc 0 1)) (hi : InjOn r (Icc 0 1))
    (hheight : ∀ t ∈ Icc (0 : ℝ) 1, (r t).2 ∈ Icc (-1 : ℝ) 1)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, (r t).2 ∈ Ioo (-1 : ℝ) 1)
    (hbottom : (r 0).2 = -1) (htop : (r 1).2 = 1)
    (htranslate : ∀ (s t : ℝ), s ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      ∀ k : ℤ, r s = r t + (32 * (k : ℝ), 0) → s = t ∧ k = 0)
    {c d : ℝ} (hbelow0 : (r 0).1 < c) (hbelow1 : (r 1).1 < c)
    (habove : ∃ t ∈ Icc (0 : ℝ) 1, c < (r t).1)
    (hband : ∀ t ∈ Icc (0 : ℝ) 1, (r t).1 - c ≤ d)
    (h0 : ∀ k : ℤ, (r 0).1 ≠ c + 32 * (k : ℝ))
    (h1 : ∀ k : ℤ, (r 1).1 ≠ c + 32 * (k : ℝ))
    (hfinite : ∀ k : ℤ, {t ∈ Icc (0 : ℝ) 1 | (r t).1 = c + 32 * (k : ℝ)}.Finite)
    (hreg : ∀ (k : ℤ) (x : ℝ), x ∈ Icc (0 : ℝ) 1 → (r x).1 = c + 32 * (k : ℝ) →
      ∃ u v m : ℝ, u < x ∧ x < v ∧ m ≠ 0 ∧
        ∀ y ∈ Icc u v, (r y).1 - (c + 32 * (k : ℝ)) = m * (y - x)) :
    ∃ (k : ℤ) (a b : ℝ) (u v : P2) (B : Set P2),
      0 ≤ a ∧ a < b ∧ b ≤ 1 ∧ u.1 < v.1 ∧
      {u, v} = ({annularLiftAboveAxis r (c + 32 * (k : ℝ)) a,
        annularLiftAboveAxis r (c + 32 * (k : ℝ)) b} : Set P2) ∧
      IsFinitePLBallPair P2 B
        ((annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc a b) ∪ segment ℝ u v) ∧
      IsCompact B ∧ B ⊆ Ioo (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) d ∧
      B ∩ Z = segment ℝ u v ∧
      B ∩ (⋃ j : ℤ, annularLiftAboveAxis r (c + 32 * (j : ℝ)) '' Icc (0 : ℝ) 1) =
        annularLiftAboveAxis r (c + 32 * (k : ℝ)) '' Icc a b ∧
      (⋃ j : ℤ, annularLiftAboveAxis r (c + 32 * (j : ℝ)) '' Icc (0 : ℝ) 1) ∩
        segment ℝ u v = {u, v} := by
  classical
  choose J hJ hdis hcover using fun k => exists_complete_upper_arc_family hr hi
    hheight hproper hbottom htop (h0 k) (h1 k) (hfinite k) (hreg k)
  let Q (k : ℤ) := annularLiftAboveAxis r (c + 32 * (k : ℝ))
  let C : Set P2 := Ioo (-1 : ℝ) 1 ×ˢ Icc (0 : ℝ) d
  let K := (finite_annular_translates_meeting_strip hr c d).toFinset
  let I := Σ k : {k : ℤ // k ∈ K}, {p : P2 // p ∈ J k.val}
  let W (i : I) : Set P2 := Q i.1.val '' Icc i.2.val.1 i.2.val.2
  let a (i : I) : P2 := Q i.1.val i.2.val.1
  let b (i : I) : P2 := Q i.1.val i.2.val.2
  have hdata (i : I) := hJ i.1.val i.2.val i.2.property
  have hsub (i : I) : Icc i.2.val.1 i.2.val.2 ⊆ Icc (0 : ℝ) 1 :=
    fun t ht => ⟨(hdata i).1.trans ht.1, ht.2.trans (hdata i).2.2.1⟩
  have hdisI : Pairwise fun i j : I => Disjoint (W i) (W j) := by
    intro i j hij
    by_cases hk : i.1 = j.1
    · have hp : i.2.val ≠ j.2.val := by
        intro hp
        apply hij
        exact Sigma.ext hk (by cases i; cases j; cases hk; exact heq_of_eq (Subtype.ext hp))
      simpa only [W, Q, hk] using hdis i.1.val i.2.val i.2.property j.2.val
        (by simpa only [hk] using j.2.property) hp
    · exact (annular_translated_upper_images_disjoint htranslate c
        (fun h => hk (Subtype.ext h))).mono (image_mono (hsub i)) (image_mono (hsub j))
  obtain ⟨t, ht, hct⟩ := habove
  have htQ : Q 0 t ∈ annularUpperHalfStrip := by
    change ((r t).2 ∈ Icc (-1 : ℝ) 1) ∧ 0 ≤ (r t).1 - (c + 32 * ((0 : ℤ) : ℝ))
    exact ⟨hheight t ht, by simp only [Int.cast_zero, mul_zero, add_zero]; linarith⟩
  obtain ⟨p, hp, s, hs, hst⟩ := mem_iUnion₂.mp
    ((hcover 0).subset ⟨mem_image_of_mem (Q 0) ht, htQ⟩)
  have hK0 : (0 : ℤ) ∈ K := (finite_annular_translates_meeting_strip hr c d).mem_toFinset.mpr
    ⟨t, ht, by simpa only [Int.cast_zero, mul_zero, add_zero] using
      (show (r t).1 - c ∈ Icc 0 d from ⟨by linarith, hband t ht⟩)⟩
  let seed : I := ⟨⟨0, hK0⟩, ⟨p, hp⟩⟩
  have hseedproper {y : ℝ} (hy : y ∈ Icc p.1 p.2) : y ∈ Ioo (0 : ℝ) 1 := by
    have hyI := hsub seed hy
    have hyD := (hdata seed).2.2.2.2.2.1 (mem_image_of_mem (Q 0) hy)
    have hfy : c ≤ (r y).1 := by
      have hh := hyD.2
      change 0 ≤ (r y).1 - (c + 32 * ((0 : ℤ) : ℝ)) at hh
      simp only [Int.cast_zero, mul_zero, add_zero] at hh
      linarith
    constructor
    · exact lt_of_le_of_ne hyI.1 (by intro h; rw [← h] at hfy; linarith)
    · exact lt_of_le_of_ne hyI.2 (by intro h; rw [h] at hfy; linarith)
  have hseedC : W seed ⊆ C := by
    rintro _ ⟨y, hy, rfl⟩
    have hyD := (hdata seed).2.2.2.2.2.1 (mem_image_of_mem (Q 0) hy)
    refine ⟨hproper y (hseedproper hy), hyD.2, ?_⟩
    simpa only [Q, annularLiftAboveAxis, seed, Int.cast_zero, mul_zero, add_zero] using
      hband y (hsub seed hy)
  have hseedaxis : a seed ∈ Z ∧ b seed ∈ Z := by
    have hfront := (hdata seed).2.2.2.2.2.2
    have hend (y : P2) (hy : y ∈ ({a seed, b seed} : Set P2)) : y ∈ Z := by
      have hyW := (hdata seed).2.2.2.1.1 hy
      have hyC := hseedC hyW
      have hyF := (hfront.symm.subset hy).2
      rcases (mem_frontier_annularUpperHalfStrip ((hdata seed).2.2.2.2.2.1 hyW)).mp hyF with h | h | h
      · exact (hyC.1.1.ne' h).elim
      · exact (hyC.1.2.ne h).elim
      · exact h
    exact ⟨hend _ (by simp), hend _ (by simp)⟩
  obtain ⟨i, u, v, B, huv, hpairs, hB, hBc, hBC, hBaxis, hBall, hbase⟩ :=
    exists_returning_disk_avoiding_complete_upper_family W a b
      (fun i => (hdata i).2.2.2.1) (fun i => (hdata i).2.2.2.2.1)
      (fun i => (hdata i).2.2.2.2.2.2) (fun i => (hdata i).2.2.2.2.2.1)
      (fun _ hx => hx.2) (fun _ hx => (mem_frontier_annularUpperHalfStrip hx.1).mpr
        (Or.inr (Or.inr hx.2))) hdisI seed hseedaxis
      ((convex_Ioo _ _).prod (convex_Icc _ _)) hseedC
      (fun _ hx => ⟨Ioo_subset_Icc_self hx.1, hx.2.1⟩)
  have hcapture {z : P2} (hzC : z ∈ C)
      (hz : z ∈ ⋃ k : ℤ, Q k '' Icc (0 : ℝ) 1) : z ∈ ⋃ j : I, W j := by
    obtain ⟨k, t, ht, rfl⟩ := mem_iUnion.mp hz
    have hk : k ∈ K := (finite_annular_translates_meeting_strip hr c d).mem_toFinset.mpr
      ⟨t, ht, hzC.2⟩
    have hzD : Q k t ∈ annularUpperHalfStrip := ⟨Ioo_subset_Icc_self hzC.1, hzC.2.1⟩
    obtain ⟨p, hp, hpz⟩ := mem_iUnion₂.mp ((hcover k).subset ⟨mem_image_of_mem (Q k) ht, hzD⟩)
    exact mem_iUnion.mpr ⟨⟨⟨k, hk⟩, ⟨p, hp⟩⟩, hpz⟩
  have hwhole : B ∩ (⋃ k : ℤ, Q k '' Icc (0 : ℝ) 1) = W i := by
    apply Subset.antisymm
    · exact fun z hz => hBall.subset ⟨hz.1, hcapture (hBC hz.1) hz.2⟩
    · intro z hz
      exact ⟨hB.1 (Or.inl hz), mem_iUnion.mpr ⟨i.1.val, image_mono (hsub i) hz⟩⟩
  refine ⟨i.1.val, i.2.val.1, i.2.val.2, u, v, B, (hdata i).1,
    (hdata i).2.1, (hdata i).2.2.1, huv, hpairs, hB, hBc, hBC, hBaxis, hwhole, ?_⟩
  apply Subset.antisymm
  · intro z hz
    exact hbase.subset ⟨hcapture (hBC (hB.1 (Or.inr hz.2))) hz.1, hz.2⟩
  · intro z hz
    have hz' := hbase.symm.subset hz
    obtain ⟨j, hj⟩ := mem_iUnion.mp hz'.1
    exact ⟨mem_iUnion.mpr ⟨j.1.val, image_mono (hsub j) hj⟩, hz'.2⟩

end PoincareConjecture.M76.Dehn
