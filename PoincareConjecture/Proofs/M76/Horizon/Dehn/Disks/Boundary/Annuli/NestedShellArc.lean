import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.NestedShellCrosscuts
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Boundary.Annuli.ShellInnerArc
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Arcs.Mathlib.JoinedPLIntervals

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

private theorem join_interval_pairs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U V : Set E} {a b c : E} (hU : IsFinitePLBallPair ℝ U {a, b})
    (hV : IsFinitePLBallPair ℝ V {b, c}) (hab : a ≠ b) (hbc : b ≠ c)
    (hUV : U ∩ V = {b}) : IsFinitePLBallPair ℝ (U ∪ V) {a, c} := by
  obtain ⟨p, hp, hp0, hp1⟩ := hU.exists_unitInterval_chart_with_endpoints hab
  obtain ⟨q, hq, hq0, hq1⟩ := hV.exists_unitInterval_chart_with_endpoints hbc
  exact isFinitePLBallPair_joined_intervals p q hp hq hp0 hp1 hq0 hq1 hUV

theorem exists_nested_shell_arc {S T : Set (ℝ × ℝ)}
    (hS : IsFinitePLBallPair (ℝ × ℝ) S (frontier S))
    (hSc : IsCompact S) (hSne : (interior S).Nonempty) (hTc : IsCompact T)
    (hST : S ⊆ interior T) :
    ∃ (a b x y : ℝ × ℝ) (L W R : Set (ℝ × ℝ)),
      a ∈ frontier S ∧ b ∈ frontier S ∧ a ≠ b ∧
      x ∈ frontier T ∧ y ∈ frontier T ∧ x ≠ y ∧
      IsFinitePLBallPair ℝ L {x, a} ∧ IsFinitePLBallPair ℝ W {a, b} ∧
      IsFinitePLBallPair ℝ R {b, y} ∧
      IsFinitePLBallPair ℝ ((L ∪ W) ∪ R) {x, y} ∧
      W ⊆ S ∧ W ∩ frontier S = {a, b} ∧
      W \ {a, b} ⊆ S \ frontier S ∧
      L ∩ S = {a} ∧ R ∩ S = {b} ∧ Disjoint L R ∧
      ((L ∪ W) ∪ R) ∩ S = W ∧
      ((L ∪ W) ∪ R) \ {x, y} ⊆ T \ frontier T := by
  obtain ⟨a, ha, b, hb, l, r, hl, hr, hab, hx, hy, hLbefore, hRbefore,
    hLoff, hRoff, hdis⟩ := exists_nested_horizontal_crosscuts hSc hSne hTc hST
  let x : ℝ × ℝ := (a.1 - l, a.2)
  let y : ℝ × ℝ := (b.1 + r, b.2)
  let FL : ℝ →ᴬ[ℝ] ℝ × ℝ :=
    ((ContinuousAffineMap.const ℝ ℝ a.1) - ContinuousAffineMap.id ℝ ℝ).prod
      (ContinuousAffineMap.const ℝ ℝ a.2)
  let FR : ℝ →ᴬ[ℝ] ℝ × ℝ :=
    ((ContinuousAffineMap.const ℝ ℝ b.1) + ContinuousAffineMap.id ℝ ℝ).prod
      (ContinuousAffineMap.const ℝ ℝ b.2)
  let L := FL '' Icc 0 l
  let R := FR '' Icc 0 r
  have hFL (t : ℝ) : FL t = (a.1 - t, a.2) := rfl
  have hFR (t : ℝ) : FR t = (b.1 + t, b.2) := rfl
  have hFL0 : FL 0 = a := by simp [hFL]
  have hFR0 : FR 0 = b := by simp [hFR]
  have haS := hSc.isClosed.frontier_subset ha
  have hbS := hSc.isClosed.frontier_subset hb
  have hab' : a ≠ b := fun heq ↦ (ne_of_lt hab) (congrArg Prod.fst heq)
  have hxa : x ≠ a := by
    intro heq
    have hh := congrArg Prod.fst heq
    dsimp [x] at hh
    linarith
  have hby : b ≠ y := by
    intro heq
    have hh := congrArg Prod.fst heq
    dsimp [y] at hh
    linarith
  have hxy : x ≠ y := by
    intro heq
    have hh := congrArg Prod.fst heq
    dsimp [x, y] at hh
    linarith
  have hL : IsFinitePLBallPair ℝ L {x, a} := by
    have hh := (isFinitePLBallPair_Icc hl).affine_image FL (by
      intro u _ v _ heq
      have hh := congrArg Prod.fst heq
      dsimp [FL] at hh
      linarith)
    simpa only [image_pair, hFL0, show FL l = x from rfl, pair_comm] using hh
  have hR : IsFinitePLBallPair ℝ R {b, y} := by
    have hh := (isFinitePLBallPair_Icc hr).affine_image FR (by
      intro u _ v _ heq
      have hh := congrArg Prod.fst heq
      dsimp [FR] at hh
      linarith)
    simpa only [image_pair, hFR0, show FR r = y from rfl] using hh
  have hLS : L ∩ S = {a} := by
    ext z
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hz⟩
      have hu0 : u = 0 := le_antisymm (le_of_not_gt (fun hh ↦ hLoff u hh hz)) hu.1
      simp only [hu0, hFL0, mem_singleton_iff]
    · rintro rfl
      exact ⟨⟨0, ⟨le_rfl, hl.le⟩, hFL0⟩, haS⟩
  have hRS : R ∩ S = {b} := by
    ext z
    constructor
    · rintro ⟨⟨u, hu, rfl⟩, hz⟩
      have hu0 : u = 0 := le_antisymm (le_of_not_gt (fun hh ↦ hRoff u hh hz)) hu.1
      simp only [hu0, hFR0, mem_singleton_iff]
    · rintro rfl
      exact ⟨⟨0, ⟨le_rfl, hr.le⟩, hFR0⟩, hbS⟩
  obtain ⟨W, hW, hWS, hWfront, hWproper⟩ :=
    exists_proper_interval_between_boundary_points hS ha hb hab'
  have hLW : L ∩ W = {a} := by
    apply Subset.antisymm ((inter_subset_inter_right _ hWS).trans hLS.subset)
    rintro z rfl
    exact ⟨hL.1 (Or.inr rfl), hW.1 (Or.inl rfl)⟩
  have hLWR : (L ∪ W) ∩ R = {b} := by
    apply Subset.antisymm
    · rintro z ⟨hz | hz, hzR⟩
      · exact (Set.disjoint_left.mp hdis hz hzR).elim
      · exact hRS.subset ⟨hzR, hWS hz⟩
    · rintro z rfl
      exact ⟨Or.inr (hW.1 (Or.inr rfl)), hR.1 (Or.inl rfl)⟩
  have hxne : x ≠ b := by
    intro heq
    exact (Set.disjoint_left.mp hdis (hL.1 (Or.inl rfl))
      (heq.symm ▸ hR.1 (Or.inl rfl)))
  have hwhole := join_interval_pairs (join_interval_pairs hL hW hxa hab' hLW) hR hxne hby hLWR
  refine ⟨a, b, x, y, L, W, R, ha, hb, hab', hx, hy, hxy, hL, hW, hR,
    hwhole, hWS, hWfront, hWproper, hLS, hRS, hdis, ?_, ?_⟩
  · ext z
    constructor
    · rintro ⟨(hz | hz) | hz, hzS⟩
      · have heq : z = a := hLS.subset ⟨hz, hzS⟩
        exact heq ▸ hW.1 (Or.inl rfl)
      · exact hz
      · have heq : z = b := hRS.subset ⟨hz, hzS⟩
        exact heq ▸ hW.1 (Or.inr rfl)
    · exact fun hz ↦ ⟨Or.inl (Or.inr hz), hWS hz⟩
  · intro z hz
    have hzint : z ∈ interior T := by
      rcases hz.1 with (hzL | hzW) | hzR
      · obtain ⟨u, hu, rfl⟩ := hzL
        have hul : u < l := lt_of_le_of_ne hu.2 (by
          intro heq
          exact hz.2 (Or.inl (show FL u = x by rw [heq]; rfl)))
        exact hLbefore u ⟨hu.1, hul⟩
      · exact hST (hWS hzW)
      · obtain ⟨u, hu, rfl⟩ := hzR
        have hur : u < r := lt_of_le_of_ne hu.2 (by
          intro heq
          exact hz.2 (Or.inr (show FR u = y by rw [heq]; rfl)))
        exact hRbefore u ⟨hu.1, hur⟩
    exact ⟨interior_subset hzint, fun hfront ↦ hfront.2 hzint⟩

end PoincareConjecture.M76.Dehn
