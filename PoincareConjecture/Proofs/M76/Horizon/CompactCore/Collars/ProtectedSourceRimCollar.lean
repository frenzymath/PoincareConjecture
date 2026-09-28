import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Collars.RadialRimInsertion
import PoincareConjecture.Proofs.M76.Wall.ProtectedFrontierBicollar

set_option autoImplicit false

open Set Metric unitInterval NormedSpace BrownCollar

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "Q" => sphere (0 : V2) 1
local notation "D" => closedBall (0 : V2) 1

theorem PLDomain.exists_protected_source_rim_collar
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {K Y F : Set X}
    (hK : PLDomain e K) (hY : IsOpen Y) (hF : IsCompact F)
    (hne : F.Nonempty) (hcut : Y ∩ frontier K = F)
    (gamma : C(Q, F)) (f : C(D, Y))
    (hf : ∀ u : Q, (f ⟨u, sphere_subset_closedBall u.property⟩ : X) = (gamma u : X)) :
    ∃ H : C(I × D, Y),
      (∀ x : D, H (0, x) = f x) ∧
      (∀ (t : I) (u : Q),
        (H (t, ⟨u, sphere_subset_closedBall u.property⟩) : X) = (gamma u : X)) ∧
      ∀ x : D, (1 / 2 : ℝ) < ‖(x : V2)‖ → ‖(x : V2)‖ < 1 →
        (H (1, x) : X) ∈ interior K := by
  obtain ⟨V, _, _, hVY, G, hbase, hside, hzero⟩ :=
    hK.exists_protected_frontier_bicollar hY hF hne hcut
  let height : I → Ioo (-1 : ℝ) 1 := fun s =>
    ⟨(s : ℝ) / 2, by constructor <;> linarith [s.property.1, s.property.2]⟩
  have hheight : Continuous height := by fun_prop
  let c : C(Q × I, Y) :=
    ⟨fun z => ⟨G (gamma z.1, height z.2), hVY (G (gamma z.1, height z.2)).property⟩,
      (continuous_subtype_val.comp (G.continuous.comp
        ((gamma.continuous.comp continuous_fst).prodMk
          (hheight.comp continuous_snd)))).subtype_mk _⟩
  have hc (u : Q) : c (u, 0) = f ⟨u, sphere_subset_closedBall u.property⟩ := by
    apply Subtype.ext
    change (G (gamma u, height 0) : X) = _
    have hh : height 0 = (⟨0, by norm_num⟩ : Ioo (-1 : ℝ) 1) := by
      apply Subtype.ext
      norm_num [height]
    rw [hh]
    exact (hbase (gamma u)).trans (hf u).symm
  obtain ⟨H, hH0, hHr, hHann⟩ := exists_radial_rim_insertion f c hc
  refine ⟨H, hH0, fun t u => (congrArg Subtype.val (hHr t u)).trans (hf u), ?_⟩
  intro x hx0 hx1
  obtain ⟨⟨r, u⟩, rfl⟩ := surjective_unitSphereRadialMap V2 x
  rw [norm_unitSphereRadialMap] at hx0 hx1
  rw [hHann r u hx0.le]
  have hdepth : 0 < (rimCollarDepth 1 r : ℝ) := by
    change 0 < max 0 (min ((r : ℝ) - rimCollarThreshold 1) (1 - (r : ℝ)))
    apply lt_max_of_lt_right
    apply lt_min
    · norm_num [rimCollarThreshold]
      linarith
    · linarith
  have hpos : 0 < (height (rimCollarDepth 1 r) : ℝ) := by
    change 0 < (rimCollarDepth 1 r : ℝ) / 2
    positivity
  have hmem : (c (u, rimCollarDepth 1 r) : X) ∈ K :=
    (hside (gamma u, height (rimCollarDepth 1 r))).mpr hpos.le
  have hnotF : (c (u, rimCollarDepth 1 r) : X) ∉ F := by
    intro hh
    exact (ne_of_gt hpos) ((hzero (gamma u, height (rimCollarDepth 1 r))).mp hh)
  have hnotfront : (c (u, rimCollarDepth 1 r) : X) ∉ frontier K := by
    intro hh
    exact hnotF (hcut.subset ⟨(c (u, rimCollarDepth 1 r)).property, hh⟩)
  exact (mem_interior_iff_notMem_frontier hmem).mpr hnotfront

end PoincareConjecture.M76
