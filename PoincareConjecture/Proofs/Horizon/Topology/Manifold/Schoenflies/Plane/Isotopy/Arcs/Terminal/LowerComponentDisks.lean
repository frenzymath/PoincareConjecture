import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.ComponentDiskUniqueness
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Plane.Isotopy.Arcs.Terminal.RegularLevelSeeds

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.PlaneArcs.Terminal

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev S1 := sphere (0 : E2) 1
private abbrev S2 := sphere (0 : EuclideanSpace Real (Fin 3)) 1

theorem exists_lower_component_disks_of_separated_circle_pair
    {h : S2 → Real} (hh : ContMDiff (𝓡 2) 𝓘(Real, Real) ∞ h) {b : Real}
    (hregular : ∀ q, h q = b → mfderiv (𝓡 2) 𝓘(Real, Real) h q ≠ 0)
    (C : Fin 2 → S1 → S2) (hC : ∀ i, ContMDiff (𝓡 1) (𝓡 2) ∞ (C i))
    (hCi : ∀ i, Injective (C i))
    (hCd : ∀ i q, Injective (mfderiv (𝓡 1) (𝓡 2) (C i) q))
    (hlevel : {q | h q = b} = range (C 0) ∪ range (C 1))
    (l : S2 → Real) (hl : Continuous l)
    (hzero : ∀ q, h q ≤ b → l q ≠ 0)
    (hneg : ∀ q, l (C 0 q) < 0) (hpos : ∀ q, 0 < l (C 1 q))
    (habove : ∃ q, b < h q) :
    ∃ p : Fin 2 → S2, ∃ d : Fin 2 → OpenPartialHomeomorph E2 S2,
      (∀ i, h (p i) < b ∧ closedBall 0 1 ⊆ (d i).source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ (d i) (d i).source ∧
        ContMDiffOn (𝓡 2) (𝓡 2) ∞ (d i).symm (d i).target ∧
        d i '' closedBall 0 1 = closure (connectedComponentIn (h ⁻¹' Iio b) (p i)) ∧
        d i '' ball 0 1 = connectedComponentIn (h ⁻¹' Iio b) (p i) ∧
        d i '' sphere (0 : E2) 1 = range (C i)) ∧
      l (p 0) < 0 ∧ 0 < l (p 1) ∧
      (∀ q ∈ d 0 '' closedBall 0 1, l q < 0) ∧
      (∀ q ∈ d 1 '' closedBall 0 1, 0 < l q) ∧
      Disjoint (d 0 '' closedBall 0 1) (d 1 '' closedBall 0 1) ∧
      d 0 '' closedBall 0 1 ∪ d 1 '' closedBall 0 1 = h ⁻¹' Iic b ∧
      d 0 '' ball 0 1 ∪ d 1 '' ball 0 1 = h ⁻¹' Iio b := by
  let W (p : S2) := connectedComponentIn (h ⁻¹' Iio b) p
  have hcl (p : S2) : closure (W p) ⊆ h ⁻¹' Iic b :=
    closure_minimal
      ((connectedComponentIn_subset _ _).trans (fun _ hx => le_of_lt (show h _ < b from hx)))
      (isClosed_Iic.preimage hh.continuous)
  have hclneg {p : S2} (hp : h p < b) (hpl : l p < 0) :
      ∀ q ∈ closure (W p), l q < 0 := by
    have hn : W p ⊆ {q | l q ≤ 0} := by
      intro q hq
      exact (isPreconnected_connectedComponentIn.gt_of_ne hl.continuousOn
        (fun z hz => hzero z (hcl p (subset_closure hz)))
        ⟨p, mem_connectedComponentIn hp, hpl⟩ hq).le
    have hclosed := closure_minimal hn (isClosed_le hl continuous_const)
    intro q hq
    exact lt_of_le_of_ne (hclosed hq) (hzero q (hcl p hq))
  have hclpos {p : S2} (hp : h p < b) (hpl : 0 < l p) :
      ∀ q ∈ closure (W p), 0 < l q := by
    have hn : W p ⊆ {q | 0 ≤ l q} := by
      intro q hq
      exact (isPreconnected_connectedComponentIn.lt_of_ne hl.continuousOn
        (fun z hz => hzero z (hcl p (subset_closure hz)))
        ⟨p, mem_connectedComponentIn hp, hpl⟩ hq).le
    have hclosed := closure_minimal hn (isClosed_le continuous_const hl)
    intro q hq
    exact lt_of_le_of_ne (hclosed hq) (hzero q (hcl p hq)).symm
  have hClevel (i : Fin 2) (q : S1) : h (C i q) = b := by
    have hm : C i q ∈ range (C 0) ∪ range (C 1) := by
      fin_cases i
      · exact Or.inl (mem_range_self q)
      · exact Or.inr (mem_range_self q)
    have hm' : C i q ∈ {q | h q = b} := hlevel.symm ▸ hm
    exact hm'
  let u : S1 := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨⟨p₀, _, hp₀, hl₀⟩, _⟩ := exists_regular_level_seeds_with_negative_separator
    hh (hregular _ (hClevel 0 u)) (hClevel 0 u) isOpen_univ (mem_univ _)
      l hl (hneg u)
  obtain ⟨⟨p₁, _, hp₁, hl₁⟩, _⟩ := exists_regular_level_seeds_with_positive_separator
    hh (hregular _ (hClevel 1 u)) (hClevel 1 u) isOpen_univ (mem_univ _)
      l hl (hpos u)
  obtain ⟨j₀, d₀, hs₀, hd₀, hdi₀, hc₀, ho₀, hb₀⟩ :=
    exists_sublevel_component_disk_of_separated_circle_pair hh.continuous C hC hCi hCd
      hlevel l hl hzero hneg hpos habove hp₀
  obtain ⟨j₁, d₁, hs₁, hd₁, hdi₁, hc₁, ho₁, hb₁⟩ :=
    exists_sublevel_component_disk_of_separated_circle_pair hh.continuous C hC hCi hCd
      hlevel l hl hzero hneg hpos habove hp₁
  have hb₀' : d₀ '' sphere (0 : E2) 1 = range (C 0) := by
    fin_cases j₀
    · exact hb₀
    · have hm : C 1 u ∈ closure (W p₀) := hc₀ ▸
        image_mono sphere_subset_closedBall (hb₀.symm ▸ mem_range_self u)
      exact (not_lt_of_ge (hpos u).le (hclneg hp₀ hl₀ _ hm)).elim
  have hb₁' : d₁ '' sphere (0 : E2) 1 = range (C 1) := by
    fin_cases j₁
    · have hm : C 0 u ∈ closure (W p₁) := hc₁ ▸
        image_mono sphere_subset_closedBall (hb₁.symm ▸ mem_range_self u)
      exact (not_lt_of_ge (hneg u).le (hclpos hp₁ hl₁ _ hm)).elim
    · exact hb₁
  let p : Fin 2 → S2 := ![p₀, p₁]
  let d : Fin 2 → OpenPartialHomeomorph E2 S2 := ![d₀, d₁]
  have hgeom (i : Fin 2) : h (p i) < b ∧ closedBall 0 1 ⊆ (d i).source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ (d i) (d i).source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ (d i).symm (d i).target ∧
      d i '' closedBall 0 1 = closure (W (p i)) ∧
      d i '' ball 0 1 = W (p i) ∧ d i '' sphere (0 : E2) 1 = range (C i) := by
    fin_cases i
    · exact ⟨hp₀, hs₀, hd₀, hdi₀, hc₀, ho₀, hb₀'⟩
    · exact ⟨hp₁, hs₁, hd₁, hdi₁, hc₁, ho₁, hb₁'⟩
  have hfront (i : Fin 2) : frontier (closure (W (p i))) = range (C i) := by
    rw [← (d i).image_sphere_eq_frontier (hgeom i).2.1 (hgeom i).2.2.2.2.1]
    exact (hgeom i).2.2.2.2.2.2
  have hclass (x : S2) (hx : h x < b) : ∃ i, W x = W (p i) := by
    obtain ⟨i, D, hs, _, _, hc, _, hb⟩ :=
      exists_sublevel_component_disk_of_separated_circle_pair hh.continuous C hC hCi hCd
        hlevel l hl hzero hneg hpos habove hx
    have hfx : frontier (closure (W x)) = range (C i) := by
      rw [← D.image_sphere_eq_frontier hs hc]
      exact hb
    exact ⟨i, (sublevel_components_eq_of_common_circle_frontier hh.continuous
      (hC i) (hCi i) (hCd i) (hClevel i) habove hx (hgeom i).1
      hfx.subset (hfront i).subset).1⟩
  have hopen : d₀ '' ball 0 1 ∪ d₁ '' ball 0 1 = h ⁻¹' Iio b := by
    apply Subset.antisymm
    · intro x hx
      rcases hx with hx | hx
      · exact connectedComponentIn_subset _ _ (ho₀ ▸ hx)
      · exact connectedComponentIn_subset _ _ (ho₁ ▸ hx)
    · intro x hx
      obtain ⟨i, hi⟩ := hclass x hx
      have hm : x ∈ d i '' ball 0 1 := (hgeom i).2.2.2.2.2.1.symm ▸
        (hi ▸ mem_connectedComponentIn hx)
      fin_cases i
      · exact Or.inl hm
      · exact Or.inr hm
  have hclosed : d₀ '' closedBall 0 1 ∪ d₁ '' closedBall 0 1 = h ⁻¹' Iic b := by
    apply Subset.antisymm
    · intro x hx
      rcases hx with hx | hx
      · exact hcl p₀ (hc₀ ▸ hx)
      · exact hcl p₁ (hc₁ ▸ hx)
    · intro x hx
      rcases lt_or_eq_of_le (show h x ≤ b from hx) with hlt | heq
      · rcases hopen.symm ▸ (show x ∈ h ⁻¹' Iio b from hlt) with hx | hx
        · exact Or.inl (image_mono ball_subset_closedBall hx)
        · exact Or.inr (image_mono ball_subset_closedBall hx)
      · have hm : x ∈ range (C 0) ∪ range (C 1) :=
          hlevel ▸ (show x ∈ {q | h q = b} from heq)
        rcases hm with hm | hm
        · exact Or.inl (image_mono sphere_subset_closedBall (hb₀'.symm ▸ hm))
        · exact Or.inr (image_mono sphere_subset_closedBall (hb₁'.symm ▸ hm))
  have hn (x : S2) (hx : x ∈ d₀ '' closedBall 0 1) : l x < 0 :=
    hclneg hp₀ hl₀ x (hc₀ ▸ hx)
  have hp' (x : S2) (hx : x ∈ d₁ '' closedBall 0 1) : 0 < l x :=
    hclpos hp₁ hl₁ x (hc₁ ▸ hx)
  refine ⟨p, d, hgeom, hl₀, hl₁, hn, hp', ?_, hclosed, hopen⟩
  exact disjoint_left.mpr (fun x hx₀ hx₁ => not_lt_of_ge (hp' x hx₁).le (hn x hx₀))

end Poincare.Manifold.Schoenflies.PlaneArcs.Terminal
