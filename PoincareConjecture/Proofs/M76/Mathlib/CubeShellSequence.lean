import PoincareConjecture.Proofs.M76.Mathlib.CubeShellHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.SquareShellSequenceIncidence
import PoincareConjecture.Proofs.M76.Mathlib.LocallyFinitePLFamilyGluing











set_option autoImplicit false

open Set Filter Topology Geometry

namespace CubeShell




theorem iUnion_sequence_shells_eq {a : ℕ → ℝ} {c : ℝ}
    (ha : StrictAnti a) (hc : ∀ n, c < a n) (hlim : Tendsto a atTop (𝓝 c)) :
    (⋃ n, shell (a (n + 1)) (a n)) = {x : Ambient | ‖x‖ ∈ Ioc c (a 0)} := by
  ext x
  change (x ∈ ⋃ n, shell (a (n + 1)) (a n)) ↔ ‖x‖ ∈ Ioc c (a 0)
  conv_rhs => rw [← ha.iUnion_adjacent_Icc_eq_Ioc hc hlim]
  simp only [mem_iUnion, shell, mem_ofPred_eq]




theorem exists_sequence_shell_neighborhood {a : ℕ → ℝ} {c : ℝ}
    (ha : StrictAnti a) (hlim : Tendsto a atTop (𝓝 c))
    {x : Ambient} (hx : ‖x‖ ∈ Ioo c (a 0)) :
    ∃ J : Finset ℕ, x ∈ interior (⋃ i ∈ J, shell (a (i + 1)) (a i)) := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (hlim.eventually (isOpen_Iio.mem_nhds hx.1))
  have hunion : (⋃ i ∈ Finset.range (N + 1), shell (a (i + 1)) (a i)) =
      shell (a (N + 1)) (a 0) := by
    ext p
    change (p ∈ ⋃ i ∈ Finset.range (N + 1), shell (a (i + 1)) (a i)) ↔
      ‖p‖ ∈ Icc (a (N + 1)) (a 0)
    conv_rhs => rw [← ha.iUnion_adjacent_Icc N]
    simp only [mem_iUnion, shell, mem_ofPred_eq]
  refine ⟨Finset.range (N + 1), ?_⟩
  rw [hunion]
  apply mem_interior_iff_mem_nhds.mpr
  have hopen : IsOpen {y : Ambient | ‖y‖ ∈ Ioo (a (N + 1)) (a 0)} :=
    isOpen_Ioo.preimage continuous_norm
  apply Filter.mem_of_superset (hopen.mem_nhds
    ⟨hN (N + 1) (Nat.le_succ N), hx.2⟩)
  exact fun _ hy => ⟨hy.1.le, hy.2.le⟩




theorem sequence_shell_overlap_iff {a b : ℕ → ℝ}
    (ha : StrictAnti a) (hb : StrictAnti b)
    (e : ∀ n, shell (a (n + 1)) (a n) ≃ₜ shell (b (n + 1)) (b n))
    (he : ∀ n (x : shell (a (n + 1)) (a n)),
      ‖(e n x : Ambient)‖ =
        SquareShell.radiusMap (a (n + 1)) (a n) (b (n + 1)) (b n) ‖(x : Ambient)‖)
    (n m : ℕ) (x : shell (a (n + 1)) (a n)) :
    (x : Ambient) ∈ shell (a (m + 1)) (a m) ↔
      (e n x : Ambient) ∈ shell (b (m + 1)) (b m) := by
  have houter : ‖(x : Ambient)‖ = a n ↔ ‖(e n x : Ambient)‖ = b n := by
    rw [he]
    exact (SquareShell.radiusMap_eq_right_iff (ha (Nat.lt_succ_self n))
      (hb (Nat.lt_succ_self n))).symm
  have hinner : ‖(x : Ambient)‖ = a (n + 1) ↔
      ‖(e n x : Ambient)‖ = b (n + 1) := by
    rw [he]
    exact (SquareShell.radiusMap_eq_left_iff (ha (Nat.lt_succ_self n))
      (hb (Nat.lt_succ_self n))).symm
  change ‖(x : Ambient)‖ ∈ Icc (a (m + 1)) (a m) ↔
    ‖(e n x : Ambient)‖ ∈ Icc (b (m + 1)) (b m)
  rw [ha.mem_adjacent_Icc_iff x.property, hb.mem_adjacent_Icc_iff (e n x).property,
    houter, hinner]



theorem sequence_shell_agree {a b : ℕ → ℝ} (ha : StrictAnti a)
    (e : ∀ n, shell (a (n + 1)) (a n) ≃ₜ shell (b (n + 1)) (b n))
    (hinner : ∀ n (x : shell (a (n + 1)) (a n)), ‖(x : Ambient)‖ = a (n + 1) →
      (e n x : Ambient) = (b (n + 1) / a (n + 1)) • (x : Ambient))
    (houter : ∀ n (x : shell (a (n + 1)) (a n)), ‖(x : Ambient)‖ = a n →
      (e n x : Ambient) = (b n / a n) • (x : Ambient))
    (n m : ℕ) (x : Ambient) (hn : x ∈ shell (a (n + 1)) (a n))
    (hm : x ∈ shell (a (m + 1)) (a m)) :
    (e n ⟨x, hn⟩ : Ambient) = e m ⟨x, hm⟩ := by
  rcases (ha.mem_adjacent_Icc_iff hn).mp hm with heq | ⟨hi, hr⟩ | ⟨hi, hr⟩
  · subst m
    rfl
  · have hr' : ‖x‖ = a (m + 1) := hr.trans (congrArg a hi).symm
    rw [houter n ⟨x, hn⟩ hr, hinner m ⟨x, hm⟩ hr']
    change (b n / a n) • x = (b (m + 1) / a (m + 1)) • x
    rw [hi]
  · have hr' : ‖x‖ = a m := hr.trans (congrArg a hi)
    rw [hinner n ⟨x, hn⟩ hr, houter m ⟨x, hm⟩ hr']
    change (b (n + 1) / a (n + 1)) • x = (b m / a m) • x
    rw [hi]




theorem sequence_shell_open_membership {a b : ℕ → ℝ} {c d : ℝ}
    (ha : StrictAnti a) (hb : StrictAnti b) (hc : ∀ n, c < a n) (hd : ∀ n, d < b n)
    (e : ∀ n, shell (a (n + 1)) (a n) ≃ₜ shell (b (n + 1)) (b n))
    (he : ∀ n (x : shell (a (n + 1)) (a n)),
      ‖(e n x : Ambient)‖ =
        SquareShell.radiusMap (a (n + 1)) (a n) (b (n + 1)) (b n) ‖(x : Ambient)‖)
    (n : ℕ) (x : shell (a (n + 1)) (a n)) :
    ‖(x : Ambient)‖ ∈ Ioo c (a 0) ↔ ‖(e n x : Ambient)‖ ∈ Ioo d (b 0) := by
  have hlo : c < ‖(x : Ambient)‖ := (hc (n + 1)).trans_le x.property.1
  have hhi : d < ‖(e n x : Ambient)‖ := (hd (n + 1)).trans_le (e n x).property.1
  by_cases hn : n = 0
  · subst n
    have hmono := SquareShell.strictMono_radiusMap
      (ha (Nat.lt_succ_self 0)) (hb (Nat.lt_succ_self 0))
    have hend := (SquareShell.radiusMap_endpoints
      (c := b 1) (d := b 0) (ha (Nat.lt_succ_self 0))).2
    constructor
    · intro hx
      refine ⟨hhi, ?_⟩
      calc
        ‖(e 0 x : Ambient)‖ =
            SquareShell.radiusMap (a 1) (a 0) (b 1) (b 0) ‖(x : Ambient)‖ := he 0 x
        _ < SquareShell.radiusMap (a 1) (a 0) (b 1) (b 0) (a 0) := hmono hx.2
        _ = b 0 := hend
    · intro hx
      refine ⟨hlo, ?_⟩
      apply hmono.lt_iff_lt.mp
      calc
        SquareShell.radiusMap (a 1) (a 0) (b 1) (b 0) ‖(x : Ambient)‖ =
            ‖(e 0 x : Ambient)‖ := (he 0 x).symm
        _ < b 0 := hx.2
        _ = SquareShell.radiusMap (a 1) (a 0) (b 1) (b 0) (a 0) := hend.symm
  · exact iff_of_true
      ⟨hlo, x.property.2.trans_lt (ha (Nat.pos_of_ne_zero hn))⟩
      ⟨hhi, (e n x).property.2.trans_lt (hb (Nat.pos_of_ne_zero hn))⟩






theorem exists_sequence_openPartialHomeomorph {a b : ℕ → ℝ} {c d : ℝ}
    (hc : 0 ≤ c) (hd : 0 ≤ d) (ha : StrictAnti a) (hb : StrictAnti b)
    (habove : ∀ n, c < a n) (hbabove : ∀ n, d < b n)
    (halim : Tendsto a atTop (𝓝 c)) (hblim : Tendsto b atTop (𝓝 d)) :
    ∃ H : OpenPartialHomeomorph Ambient Ambient,
      H.source = {x | ‖x‖ ∈ Ioo c (a 0)} ∧
      H.target = {y | ‖y‖ ∈ Ioo d (b 0)} ∧
      H ∈ piecewiseAffineGroupoid Ambient ∧
      ∀ n (x : Ambient), x ∈ shell (a (n + 1)) (a n) →
        ‖H x‖ = SquareShell.radiusMap (a (n + 1)) (a n) (b (n + 1)) (b n) ‖x‖ ∧
        (a (n + 1) = b (n + 1) → a n = b n → H x = x) := by
  have hex (n : ℕ) := exists_fixed_radius_homeomorph
    (hc.trans_lt (habove (n + 1))) (ha (Nat.lt_succ_self n))
    (hd.trans_lt (hbabove (n + 1))) (hb (Nat.lt_succ_self n))
  choose e he hdata hfixed using hex
  have hradius := fun n x => (hdata n x).1
  let U : Set Ambient := {x | ‖x‖ ∈ Ioo c (a 0)}
  let V : Set Ambient := {x | ‖x‖ ∈ Ioo d (b 0)}
  have hU : IsOpen U := isOpen_Ioo.preimage continuous_norm
  have hV : IsOpen V := isOpen_Ioo.preimage continuous_norm
  have hUS : U ⊆ ⋃ n, shell (a (n + 1)) (a n) := by
    rw [iUnion_sequence_shells_eq ha habove halim]
    exact fun _ hx => ⟨hx.1, hx.2.le⟩
  have hVT : V ⊆ ⋃ n, shell (b (n + 1)) (b n) := by
    rw [iUnion_sequence_shells_eq hb hbabove hblim]
    exact fun _ hy => ⟨hy.1, hy.2.le⟩
  obtain ⟨H, hHS, hHT, hPL, _, hHval, _⟩ :=
    Homeomorph.exists_openPartialHomeomorph_of_finitePL_family
      (fun n => shell (a (n + 1)) (a n)) (fun n => shell (b (n + 1)) (b n)) e he
      (sequence_shell_overlap_iff ha hb e hradius)
      (sequence_shell_agree ha e (fun n x => (hdata n x).2.1)
        (fun n x => (hdata n x).2.2)) U V hU hV hUS hVT
      (sequence_shell_open_membership ha hb habove hbabove e hradius)
      (fun _ hx => exists_sequence_shell_neighborhood ha halim hx)
      (fun _ hy => exists_sequence_shell_neighborhood hb hblim hy)
  refine ⟨H, hHS, hHT, ?_, ?_⟩
  · apply (mem_piecewiseAffineGroupoid_iff_forward H).mpr
    rw [hHS]
    exact hPL
  · intro n x hx
    exact ⟨(congrArg norm (hHval n ⟨x, hx⟩)).trans (hdata n ⟨x, hx⟩).1,
      fun hl hu => (hHval n ⟨x, hx⟩).trans (hfixed n hl hu ⟨x, hx⟩)⟩

end CubeShell
