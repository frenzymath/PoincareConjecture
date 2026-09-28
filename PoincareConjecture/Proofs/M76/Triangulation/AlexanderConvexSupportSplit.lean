import PoincareConjecture.Proofs.M76.Triangulation.IntrinsicCollarCappedSpheres
import PoincareConjecture.Proofs.M76.Triangulation.AlexanderRegularSlabWindow
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursivePointedChildren
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveOrdinaryChildren
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderFiniteHeightSignEvents
import PoincareConjecture.Proofs.M76.Mathlib.PlanarDiskConvexContainment
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionSphericalTransport












set_option autoImplicit false

open Set Geometry

namespace Geometry.AlexanderSectionProfile

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]







theorem exists_recursive_sphere_split_in_convex_open_at_zero
    (W : AlexanderSectionProfile E) (hdim : Module.finrank ℝ E = 3)
    (hbranching : W.HasBranchingCollars)
    (hnonisolated : W.HasNonisolatedHeightSigns)
    (hevents : W.HasFiniteHeightSignEvents) (hcharge : W.charge 0 ≠ 0)
    {D : Set F} (hD : IsCompact D) (hcv : Convex ℝ D)
    (hne : (interior D).Nonempty) (hdimD : Module.finrank ℝ F = 3)
    (e : W.carrier ≃ₜ frontier D) (he : e.IsFinitePL)
    {U : Set E} (hU : IsOpen U) (hUcv : Convex ℝ U) (hWU : W.carrier ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E, W.height.linear v = 1 ∧ ∃ d s s' rim : Set E,
      IsFinitePLBallPair (ℝ × ℝ) d rim ∧
      IsFinitePLBallPair (ℝ × ℝ) s rim ∧
      IsFinitePLBallPair (ℝ × ℝ) s' rim ∧
      d ⊆ {x | W.height x = 0} ∧ d ∩ W.carrier = rim ∧
      s ∪ s' = W.carrier ∧ s ∩ s' = rim ∧
      s ∩ d = rim ∧ s' ∩ d = rim ∧ d ⊆ U ∧
      ∃ δ : ℝ, δ ∈ Ioo 0 ε ∧ ∃ H G : E ≃ₜ E,
        (∀ K : SimplicialComplex ℝ E, K.faces.Finite →
          FinitePiecewiseAffineOn (H : E → E) K.space) ∧
        (∀ K : SimplicialComplex ℝ E, K.faces.Finite →
          FinitePiecewiseAffineOn (G : E → E) K.space) ∧
        (∀ x, x ∉ U → H x = x ∧ G x = x) ∧
        (∀ x, δ ≤ |W.height x| → H x = x ∧ G x = x) ∧
        H '' U = U ∧ G '' U = U ∧
        ∃ L R : AlexanderSectionProfile E,
          L.carrier = H '' (s ∪ d) ∧ R.carrier = G '' (s' ∪ d) ∧
          L.height = W.height ∧ R.height = W.height ∧
          L.carrier ⊆ U ∧ R.carrier ⊆ U ∧
          L.complexity + R.complexity < W.complexity ∧
          L.HasBranchingCollars ∧ R.HasBranchingCollars ∧
          L.HasNonisolatedHeightSigns ∧ R.HasNonisolatedHeightSigns ∧
          L.HasFiniteHeightSignEvents ∧ R.HasFiniteHeightSignEvents ∧
          (∃ eL : L.carrier ≃ₜ frontier (TriangularRoofModel.halfBall 1), eL.IsFinitePL) ∧
          (∃ eR : R.carrier ≃ₜ frontier (TriangularRoofModel.halfBall 1), eR.IsFinitePL) := by
  classical
  obtain ⟨C, hC, hsigns⟩ := hevents
  obtain ⟨m, n, P, q, hm, hP, hfull, hpair, hbranch, hcount, _, hcollars⟩ :=
    hbranching 0 hcharge
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  obtain ⟨β, _, γ, _, ⟨M₀⟩, ⟨Mneg₀⟩⟩ := hcollars 1 zero_lt_one
  have hzero : W.height - AffineMap.const ℝ E 0 = W.height := by
    ext x
    change W.height x - 0 = W.height x
    exact sub_zero _
  have M : AlexanderCollarSlab W.carrier W.height q β := hzero ▸ M₀
  have Mneg : AlexanderCollarSlab W.carrier (-W.height) q γ := hzero ▸ Mneg₀
  obtain ⟨δ, hδ, hgap⟩ := W.exists_event_support_gap hC hε
  have hgapCharge (c : ℝ) (hc : W.charge c ≠ 0) (hc0 : c ≠ 0) : δ < |c| :=
    hgap c (Or.inr hc) hc0
  obtain ⟨η, _, M', Mneg', _, _, _, _, _, _, havoid, hregular, hregularNeg, hlocal⟩ :=
    W.exists_regular_collared_section_window he hD hcv hne hdimD hC hsigns M Mneg hδ.1
  obtain ⟨j, d, s₀, s₁, N, hd, hs₀, hs₁, hdplane, hcap, hunion, hinter,
      _, _, hN, hsection, hdN, _, _, _, _, _⟩ :=
    M'.exists_intrinsic_capped_spheres hdim n P hP hpair hfull hD hcv hne hdimD e he
  obtain ⟨ec⟩ := (P j).nonempty_boundary_homeomorph_circle (hP j).2 (hP j).1
  obtain ⟨x, hxP, hxq⟩ :=
    (isConnected_sdiff_singleton_of_homeomorph_circle ((P j).boundary ℝ) ec q).nonempty
  have hx : x ∈ W.carrier ∩ {y | W.height y = 0} :=
    hfull.symm.subset (mem_iUnion.mpr ⟨j, hxP⟩)
  obtain ⟨v, hv⟩ := M'.exists_unit_height_direction hx hxq
  have hA : W.height.linear ≠ 0 := by
    intro hz
    rw [hz, LinearMap.zero_apply] at hv
    exact zero_ne_one hv
  have hdU : d ⊆ U := hd.subset_convex_of_planar_polygon_boundary
    (P j) (hP j).2 (hP j).1 W.height hA hdim hdplane hUcv (by
      rintro y ⟨i, rfl⟩
      exact hWU (hfull.symm.subset (mem_iUnion.mpr ⟨j, (P j).vertex_mem_boundary i⟩)).1)
  have hcontacts {s : Set E} (hs : IsFinitePLBallPair (ℝ × ℝ) s ((P j).boundary ℝ))
      (hsW : s ⊆ W.carrier) : s ∩ d = (P j).boundary ℝ := by
    apply Subset.antisymm
    · exact fun _ hx => hcap.subset ⟨hx.2, hsW hx.1⟩
    · exact fun _ hx => ⟨hs.1 hx, hd.1 hx⟩
  have hchild {s : Set E} (H : E ≃ₜ E) (hsW : s ⊆ W.carrier)
      (hHU : H '' U = U) : H '' (s ∪ d) ⊆ U :=
    (image_mono (union_subset (hsW.trans hWU) hdU)).trans hHU.subset
  by_cases hqP : q ∈ (P j).boundary ℝ
  · obtain ⟨s, s', _, hs, hs', hss, hssinter, H, G,
        hglobalH, hglobalG, _, _, _, _, _, _, hfix, hslab, _, _, _, _, _, _, _,
        _, hglobalSigns, _, hmodelH, hmodelG, L, R, hL, hR, hLA, hRA,
        hdecrease, _, _, _, _, _, _, hhereditary, hbranchingChildren⟩ :=
      W.exists_pointed_decreasing_deformations_with_level_bounds M' Mneg'
        n P hP hpair hbranch hfull hcount j hqP hd hs₀ hs₁ hunion hinter
        hdplane hcap N hN hsection hdN hU hdU hδ.1
    obtain ⟨hLbranch, hRbranch⟩ := hbranchingChildren hbranching hgapCharge
    obtain ⟨hLsigns, hRsigns⟩ := hhereditary hnonisolated hlocal
    obtain ⟨hC', hHsigns, hGsigns⟩ := hglobalSigns C hC
      (fun c hc hc0 hcmem => havoid c hc hc0 (Or.inl hcmem)) hsigns
    have hLevents : L.HasFiniteHeightSignEvents := by
      refine ⟨insert 0 C, hC', ?_⟩
      simpa only [hL, hLA] using hHsigns
    have hRevents : R.HasFiniteHeightSignEvents := by
      refine ⟨insert 0 C, hC', ?_⟩
      simpa only [hR, hRA] using hGsigns
    have hHU : H '' U = U := H.image_eq_self_of_eqOn_compl (fun x hx => (hfix x hx).1)
    have hGU : G '' U = U := G.image_eq_self_of_eqOn_compl (fun x hx => (hfix x hx).2)
    have hsW : s ⊆ W.carrier := subset_union_left.trans hss.subset
    have hs'W : s' ⊆ W.carrier := subset_union_right.trans hss.subset
    refine ⟨v, hv, d, s, s', (P j).boundary ℝ, hd, hs, hs', hdplane, hcap, hss, hssinter,
      hcontacts hs hsW, hcontacts hs' hs'W, hdU, δ, hδ, H, G,
      hglobalH, hglobalG, hfix, hslab, hHU, hGU,
      L, R, hL, hR, hLA, hRA, ?_, ?_, hdecrease, hLbranch, hRbranch,
      hLsigns, hRsigns, hLevents, hRevents, ?_, ?_⟩
    · rw [hL]
      exact hchild H hsW hHU
    · rw [hR]
      exact hchild G hs'W hGU
    · rw [hL]
      exact hmodelH
    · rw [hR]
      exact hmodelG
  · obtain ⟨s, s', _, hs, hs', hss, hssinter, H, G,
        hglobalH, hglobalG, _, _, _, _, _, _, hfix, hslab, _, _, _, _, _,
        hbirthH, hbirthG, _, hmodelH, hmodelG, L, R, hL, hR, hLA, hRA,
        hdecrease, _, _, _, _, _, _, _, _, hhereditary, hbranchingChildren⟩ :=
      W.exists_ordinary_decreasing_deformations_with_level_bounds M' Mneg'
        hregular hregularNeg hlocal n P hP hpair hbranch hfull hcount j hqP
        hd hs₀ hs₁ hunion hinter hdplane hcap N hN hsection hdN hU hdU hδ.1
    obtain ⟨hLbranch, hRbranch⟩ := hbranchingChildren hbranching hgapCharge
    obtain ⟨hLsigns, hRsigns⟩ := hhereditary hnonisolated
    obtain ⟨_, _, p, _, _, _, _, _, _, hglobalSignsH⟩ := hbirthH
    obtain ⟨_, _, r, _, _, _, _, _, _, hglobalSignsG⟩ := hbirthG
    obtain ⟨hCL, hHsigns⟩ := hglobalSignsH C hC hsigns
    obtain ⟨hCR, hGsigns⟩ := hglobalSignsG C hC hsigns
    have hLevents : L.HasFiniteHeightSignEvents := by
      refine ⟨insert 0 (insert (W.height (H p)) C), hCL, ?_⟩
      simpa only [hL, hLA] using hHsigns
    have hRevents : R.HasFiniteHeightSignEvents := by
      refine ⟨insert 0 (insert (W.height (G r)) C), hCR, ?_⟩
      simpa only [hR, hRA] using hGsigns
    have hHU : H '' U = U := H.image_eq_self_of_eqOn_compl (fun x hx => (hfix x hx).1)
    have hGU : G '' U = U := G.image_eq_self_of_eqOn_compl (fun x hx => (hfix x hx).2)
    have hsW : s ⊆ W.carrier := subset_union_left.trans hss.subset
    have hs'W : s' ⊆ W.carrier := subset_union_right.trans hss.subset
    refine ⟨v, hv, d, s, s', (P j).boundary ℝ, hd, hs, hs', hdplane, hcap, hss, hssinter,
      hcontacts hs hsW, hcontacts hs' hs'W, hdU, δ, hδ, H, G,
      hglobalH, hglobalG, hfix, hslab, hHU, hGU,
      L, R, hL, hR, hLA, hRA, ?_, ?_, hdecrease, hLbranch, hRbranch,
      hLsigns, hRsigns, hLevents, hRevents, ?_, ?_⟩
    · rw [hL]
      exact hchild H hsW hHU
    · rw [hR]
      exact hchild G hs'W hGU
    · rw [hL]
      exact hmodelH
    · rw [hR]
      exact hmodelG

end Geometry.AlexanderSectionProfile
