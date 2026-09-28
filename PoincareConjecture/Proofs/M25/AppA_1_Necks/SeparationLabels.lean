import PoincareConjecture.Proofs.M25.AppA_1_Necks.GraphSeparation
import PoincareConjecture.Proofs.M25.AppA_1_Necks.SphereContainment
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OverlapSlab
import Mathlib.Topology.LocallyConstant.Basic

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

theorem exists_near_center_separation_agreement :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N N' : EpsilonNeck g),
      N.epsilon ≤ epsilon0 → N'.epsilon ≤ epsilon0 →
      N'.center ∈ N.region (-(1 : ℝ) / 2) (1 / 2) →
      (N.IsSeparating ↔ N'.IsSeparating) := by
  obtain ⟨epsilonG, hGpos, hGcap, hgraph⟩ :=
    exists_middle_central_sphere_graph.{u} (κ := 1 / 2) (by norm_num)
  obtain ⟨epsilonS, hSpos, _, hslab⟩ :=
    exists_middle_overlap_slab.{u} (L := 1) (κ := 1 / 2)
      (by norm_num) (by norm_num)
  obtain ⟨epsilonC, hCpos, _, hcontained⟩ := exists_contained_slice_graph.{u}
  refine ⟨min epsilonG (min epsilonS epsilonC),
    lt_min hGpos (lt_min hSpos hCpos), (min_le_left _ _).trans hGcap, ?_⟩
  intro M _ _ _ _ _ _ g N N' hN hN' hcenter
  have hNG : N.epsilon ≤ epsilonG := hN.trans (min_le_left _ _)
  have hN'G : N'.epsilon ≤ epsilonG := hN'.trans (min_le_left _ _)
  have hNS : N.epsilon ≤ epsilonS :=
    hN.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hN'S : N'.epsilon ≤ epsilonS :=
    hN'.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hNC : N.epsilon ≤ epsilonC :=
    hN.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hN'C : N'.epsilon ≤ epsilonC :=
    hN'.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hheight : |(N.coordinate_inverse N'.center).2| < (1 : ℝ) / 2 := by
    apply abs_lt.mpr
    constructor <;> linarith [hcenter.2.1, hcenter.2.2]
  have hepsilon : N.epsilon ≤ 1 := by linarith [hNG.trans hGcap]
  have hinverse : (1 : ℝ) ≤ N.epsilon⁻¹ := by
    have h : (1 : ℝ) ≤ 1 / N.epsilon :=
      (le_div_iff₀ N.epsilon_pos).mpr (by simpa only [one_mul] using hepsilon)
    simpa only [one_div] using h
  have hmiddle : |(N.coordinate_inverse N'.center).2| ≤
      (1 - (1 : ℝ) / 2) * N.epsilon⁻¹ := by nlinarith
  obtain ⟨_, ⟨f, hf, hfdom, hfrange⟩, _⟩ :=
    hgraph N N' hNG hN'G hcenter.1 hmiddle
  have hslab' := hslab N N' hNS hN'S hcenter.1 hmiddle
  have hslice (q : UnitTwoSphere) : N.coordinate_map (q, 0) ∈ N'.carrier := by
    have hz : (q, (0 : ℝ)) ∈ univ ×ˢ
        Icc ((N.coordinate_inverse N'.center).2 - 1)
          ((N.coordinate_inverse N'.center).2 + 1) := by
      refine ⟨mem_univ _, ?_, ?_⟩ <;> linarith [hcenter.2.1, hcenter.2.2]
    exact (hslab' hz).2
  obtain ⟨⟨f', hf', hf'dom, hf'range⟩, _⟩ :=
    hcontained N' N hN'C hNC 0 N.zero_mem_interval hslice
  rw [N.coordinate_zero_range] at hf'range
  constructor
  · intro hsep
    exact N.isSeparating_of_central_sphere_graph N' hsep f hf.continuous
      hfdom hfrange.symm
  · intro hsep
    exact N'.isSeparating_of_central_sphere_graph N hsep f' hf'.continuous
      hf'dom hf'range.symm

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.NeckOnlyCover

theorem exists_locally_constant_separation_label :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 →
      ∃ label : LocallyConstant H.X Bool,
        ∀ N ∈ H.necks, ∀ hx : N.center ∈ H.X,
          (label ⟨N.center, hx⟩ = true ↔ N.IsSeparating) := by
  classical
  obtain ⟨epsilon0, hpos, hcap, hagree⟩ :=
    EpsilonNeck.exists_near_center_separation_agreement.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ instT3 g H hH
  let : T2Space M := @T25Space.t2Space M _ (@T3Space.t25Space M _ instT3)
  have hchoice (x : H.X) : ∃ N : EpsilonNeck g, N ∈ H.necks ∧ N.center = x.val :=
    H.pointwise_center_cover x.val x.property
  choose neck hmem hcenter using hchoice
  have hepsilon (x : H.X) : (neck x).epsilon ≤ epsilon0 := by
    rw [H.neck_epsilon (neck x) (hmem x)]
    exact hH
  have hself (N : EpsilonNeck g) : N.center ∈ N.region (-(1 : ℝ) / 2) (1 / 2) := by
    have hc := (N.mem_central_sphere_iff N.center).mp N.center_on_central_sphere
    refine ⟨hc.1, ?_⟩
    rw [hc.2]
    norm_num
  let b : H.X → Bool := fun x => decide ((neck x).IsSeparating)
  have hb : IsLocallyConstant b := by
    apply (IsLocallyConstant.iff_exists_open b).mpr
    intro x
    refine ⟨(Subtype.val : H.X → M) ⁻¹'
      (neck x).region (-(1 : ℝ) / 2) (1 / 2),
      ((neck x).isOpen_region _ _).preimage continuous_subtype_val, ?_, ?_⟩
    · change x.val ∈ (neck x).region (-(1 : ℝ) / 2) (1 / 2)
      simpa only [hcenter x] using hself (neck x)
    · intro y hy
      have hnear : (neck y).center ∈ (neck x).region (-(1 : ℝ) / 2) (1 / 2) := by
        rw [hcenter y]
        exact hy
      change decide ((neck y).IsSeparating) = decide ((neck x).IsSeparating)
      exact decide_eq_decide.mpr
        (hagree (neck x) (neck y) (hepsilon x) (hepsilon y) hnear).symm
  refine ⟨⟨b, hb⟩, ?_⟩
  intro N hN hx
  have hNsmall : N.epsilon ≤ epsilon0 := by
    rw [H.neck_epsilon N hN]
    exact hH
  have hnear : N.center ∈ (neck ⟨N.center, hx⟩).region (-(1 : ℝ) / 2) (1 / 2) := by
    simpa only [hcenter ⟨N.center, hx⟩] using hself (neck ⟨N.center, hx⟩)
  change decide ((neck ⟨N.center, hx⟩).IsSeparating) = true ↔ N.IsSeparating
  exact decide_eq_true_iff.trans
    (hagree (neck ⟨N.center, hx⟩) N (hepsilon _) hNsmall hnear)

theorem exists_uniform_separation_labels :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (H : NeckOnlyCover g), H.epsilon ≤ epsilon0 → H.X = univ →
        (∀ N ∈ H.necks, N.IsSeparating) ∨
          (∀ N ∈ H.necks, N.IsNonseparating) := by
  classical
  obtain ⟨epsilon0, hpos, hcap, hlabel⟩ := exists_locally_constant_separation_label.{u}
  refine ⟨epsilon0, hpos, hcap, ?_⟩
  intro M _ _ _ _ _ _ g H hH hwhole
  obtain ⟨label, hlabel⟩ := hlabel H hH
  let : PreconnectedSpace H.X := Subtype.preconnectedSpace H.connected_X.isPreconnected
  obtain ⟨x0, hx0⟩ := H.connected_X.nonempty
  by_cases hvalue : label ⟨x0, hx0⟩ = true
  · left
    intro N hN
    have hx : N.center ∈ H.X := by rw [hwhole]; exact mem_univ _
    apply (hlabel N hN hx).mp
    exact (label.apply_eq_of_preconnectedSpace ⟨N.center, hx⟩ ⟨x0, hx0⟩).trans hvalue
  · right
    intro N hN
    have hx : N.center ∈ H.X := by rw [hwhole]; exact mem_univ _
    have hnot : ¬ N.IsSeparating := by
      intro hsep
      apply hvalue
      exact (label.apply_eq_of_preconnectedSpace ⟨x0, hx0⟩ ⟨N.center, hx⟩).trans
        ((hlabel N hN hx).mpr hsep)
    by_contra hn
    exact hnot ((N.m25_isSeparating_iff_not_isNonseparating).mpr hn)

end PoincareConjecture.NeckOnlyCover
