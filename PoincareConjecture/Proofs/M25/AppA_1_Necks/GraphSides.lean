import PoincareConjecture.Proofs.M25.AppA_1_Necks.Coordinates
import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseGraphComplement

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.EpsilonNeck

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  {g : RiemannianMetric 3 M}

theorem graph_sides_of_axial_level (N N' : EpsilonNeck g)
    (H : M → ℝ) (hH : Continuous H)
    (hinside : ∀ x ∈ N.carrier, H x = (N.coordinate_inverse x).2)
    {t : ℝ} (ht : t ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹)
    (hlevel : ∀ x ∈ N'.carrier,
      H x = t ↔ x ∈ range (fun q : UnitTwoSphere => N.coordinate_map (q, t)))
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hdom : ∀ q, f q ∈ Ioo (-N'.epsilon⁻¹) N'.epsilon⁻¹)
    (hnegative : ∀ q, f q < 0)
    (hgraph : range (fun q : UnitTwoSphere => N.coordinate_map (q, t)) =
      range (fun q : UnitTwoSphere => N'.coordinate_map (q, f q)))
    (hcenter : t < H N'.center) :
    ∀ x ∈ N'.carrier,
      (H x < t ↔ (N'.coordinate_inverse x).2 < f (N'.coordinate_inverse x).1) ∧
      (t < H x ↔ f (N'.coordinate_inverse x).1 < (N'.coordinate_inverse x).2) := by
  classical
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let Dminus : Set RoundCylinderSpace := {z | -N'.epsilon⁻¹ < z.2 ∧ z.2 < f z.1}
  let Dplus : Set RoundCylinderSpace := {z | f z.1 < z.2 ∧ z.2 < N'.epsilon⁻¹}
  let Wminus := N'.coordinate_map '' Dminus
  let Wplus := N'.coordinate_map '' Dplus
  have hminusD : Dminus ⊆ N'.cylinderDomain := by
    intro z hz
    exact ⟨mem_univ _, hz.1, hz.2.trans (hdom z.1).2⟩
  have hplusD : Dplus ⊆ N'.cylinderDomain := by
    intro z hz
    exact ⟨mem_univ _, (hdom z.1).1.trans hz.1, hz.2⟩
  have hminus : IsConnected Wminus :=
    (isConnected_between_continuous_graphs continuous_const hf (fun q => (hdom q).1)).image
      N'.coordinate_map (N'.coordinate_map_smooth.continuousOn.mono hminusD)
  have hplus : IsConnected Wplus :=
    (isConnected_between_continuous_graphs hf continuous_const (fun q => (hdom q).2)).image
      N'.coordinate_map (N'.coordinate_map_smooth.continuousOn.mono hplusD)
  have hminusU : Wminus ⊆ N'.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact N'.coordinate_map_mem (hminusD hz)
  have hplusU : Wplus ⊆ N'.carrier := by
    rintro x ⟨z, hz, rfl⟩
    exact N'.coordinate_map_mem (hplusD hz)
  have hmemMinus {x : M} (hx : x ∈ N'.carrier) :
      x ∈ Wminus ↔ (N'.coordinate_inverse x).2 < f (N'.coordinate_inverse x).1 := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [N'.coordinate_inverse_map z (hminusD hz).2] using hz.2
    · intro h
      exact ⟨N'.coordinate_inverse x, ⟨(N'.coordinate_inverse_mem x hx).2.1, h⟩,
        N'.coordinate_map_inverse hx⟩
  have hmemPlus {x : M} (hx : x ∈ N'.carrier) :
      x ∈ Wplus ↔ f (N'.coordinate_inverse x).1 < (N'.coordinate_inverse x).2 := by
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa only [N'.coordinate_inverse_map z (hplusD hz).2] using hz.1
    · intro h
      exact ⟨N'.coordinate_inverse x, ⟨h, (N'.coordinate_inverse_mem x hx).2.2⟩,
        N'.coordinate_map_inverse hx⟩
  have hequal {x : M} (hx : x ∈ N'.carrier) :
      H x = t ↔ (N'.coordinate_inverse x).2 = f (N'.coordinate_inverse x).1 := by
    rw [hlevel x hx, hgraph]
    constructor
    · rintro ⟨q, rfl⟩
      rw [N'.coordinate_inverse_map (q, f q) (hdom q)]
    · intro hs
      refine ⟨(N'.coordinate_inverse x).1, ?_⟩
      change N'.coordinate_map ((N'.coordinate_inverse x).1, f (N'.coordinate_inverse x).1) = x
      rw [← hs]
      exact N'.coordinate_map_inverse hx
  have hminusNe : ∀ x ∈ Wminus, H x ≠ t := by
    intro x hx heq
    exact (ne_of_lt ((hmemMinus (hminusU hx)).mp hx))
      ((hequal (hminusU hx)).mp heq)
  have hplusNe : ∀ x ∈ Wplus, H x ≠ t := by
    intro x hx heq
    exact (ne_of_gt ((hmemPlus (hplusU hx)).mp hx))
      ((hequal (hplusU hx)).mp heq)
  have hcentral := (N'.mem_central_sphere_iff N'.center).mp N'.center_on_central_sphere
  have hcenterPlus : N'.center ∈ Wplus := by
    apply (hmemPlus hcentral.1).mpr
    rw [hcentral.2]
    exact hnegative _
  have hplusSign : ∀ x ∈ Wplus, t < H x := by
    intro x hx
    exact hplus.isPreconnected.lt_of_ne hH.continuousOn hplusNe
      ⟨N'.center, hcenterPlus, hcenter⟩ hx
  let q₀ := (N.coordinate_inverse N.center).1
  have hpointU : N.coordinate_map (q₀, t) ∈ N'.carrier := by
    have hg : N.coordinate_map (q₀, t) ∈ range (fun q => N'.coordinate_map (q, f q)) :=
      hgraph ▸ mem_range_self q₀
    obtain ⟨q, hq⟩ := hg
    rw [← hq]
    exact N'.coordinate_map_mem ⟨mem_univ _, hdom q⟩
  have hraw : (q₀, t) ∈ closure (univ ×ˢ Ioo (-N.epsilon⁻¹) t) := by
    rw [closure_prod_eq, closure_univ, closure_Ioo ht.1.ne]
    exact ⟨mem_univ _, ht.1.le, le_rfl⟩
  have hpoint : N.coordinate_map (q₀, t) ∈
      closure (N.coordinate_map '' (univ ×ˢ Ioo (-N.epsilon⁻¹) t)) :=
    mem_closure_image (N.coordinate_map_smooth.continuousOn.continuousAt
      (N.cylinderDomain_open.mem_nhds ⟨mem_univ _, ht⟩)) hraw
  obtain ⟨w, hwU, z, hz, rfl⟩ :=
    mem_closure_iff.mp hpoint N'.carrier N'.carrier_open hpointU
  have hzD : z ∈ N.cylinderDomain := ⟨mem_univ _, hz.2.1, hz.2.2.trans ht.2⟩
  have hwH : H (N.coordinate_map z) < t := by
    rw [hinside _ (N.coordinate_map_mem hzD), N.coordinate_inverse_map z hzD.2]
    exact hz.2.2
  have hwMinus : N.coordinate_map z ∈ Wminus := by
    apply (hmemMinus hwU).mpr
    rcases lt_trichotomy (N'.coordinate_inverse (N.coordinate_map z)).2
        (f (N'.coordinate_inverse (N.coordinate_map z)).1) with h | h | h
    · exact h
    · exact False.elim (hwH.ne ((hequal hwU).mpr h))
    · exact False.elim (lt_asymm hwH (hplusSign _ ((hmemPlus hwU).mpr h)))
  have hminusSign : ∀ x ∈ Wminus, H x < t := by
    intro x hx
    exact hminus.isPreconnected.gt_of_ne hH.continuousOn hminusNe
      ⟨N.coordinate_map z, hwMinus, hwH⟩ hx
  intro x hx
  have hlow (h : (N'.coordinate_inverse x).2 < f (N'.coordinate_inverse x).1) : H x < t :=
    hminusSign x ((hmemMinus hx).mpr h)
  have hhigh (h : f (N'.coordinate_inverse x).1 < (N'.coordinate_inverse x).2) : t < H x :=
    hplusSign x ((hmemPlus hx).mpr h)
  constructor
  · refine ⟨?_, hlow⟩
    intro h
    rcases lt_trichotomy (N'.coordinate_inverse x).2
        (f (N'.coordinate_inverse x).1) with hlt | heq | hgt
    · exact hlt
    · exact False.elim (h.ne ((hequal hx).mpr heq))
    · exact False.elim (lt_asymm h (hhigh hgt))
  · refine ⟨?_, hhigh⟩
    intro h
    rcases lt_trichotomy (N'.coordinate_inverse x).2
        (f (N'.coordinate_inverse x).1) with hlt | heq | hgt
    · exact False.elim (lt_asymm h (hlow hlt))
    · exact False.elim (h.ne ((hequal hx).mpr heq).symm)
    · exact hgt

end PoincareConjecture.EpsilonNeck
