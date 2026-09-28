import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.HorizontalSeparated
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Caps.Closing.Collar.TerminalLiftPreparation

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Caps.Closing

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem exists_simultaneous_relative_cap_germs_preserving_height
    {ι : Type*} [Finite ι] (A B R : ι → Set E3) (W : Set E3) (height : E3 → Real)
    (hRB : ∀ i, R i ⊆ B i)
    (hmoves : ∀ i, ∃ (K U : Set E3), IsCompact K ∧ IsOpen U ∧ R i ⊆ U ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x ∉ K, G x = x) ∧ (∀ x, height (G x) = height x) ∧ EqOn G id W ∧
        (∀ j, j ≠ i → EqOn G id (A j) ∧ EqOn G id (B j)) ∧
        (G '' A i) ∩ U = B i ∩ U) :
    ∃ K : Set E3, IsCompact K ∧
      ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ x ∉ K, H x = x) ∧ (∀ x, height (H x) = height x) ∧ EqOn H id W ∧
        ∀ i, ∃ U : Set E3, IsOpen U ∧ R i ⊆ U ∧ (H '' A i) ∩ U = B i ∩ U := by
  classical
  let := Fintype.ofFinite ι
  have hfinite (s : Finset ι) :
      ∃ K : Set E3, IsCompact K ∧
        ∃ H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ x ∉ K, H x = x) ∧ (∀ x, height (H x) = height x) ∧ EqOn H id W ∧
          (∀ i, i ∉ s → EqOn H id (A i)) ∧
          ∀ i ∈ s, ∃ U : Set E3, IsOpen U ∧ R i ⊆ U ∧
            (H '' A i) ∩ U = B i ∩ U := by
    induction s using Finset.induction_on with
    | empty =>
      exact ⟨∅, isCompact_empty, Diffeomorph.refl _ _ _,
        fun _ _ => rfl, fun _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl, by simp⟩
    | @insert i s his ih =>
      obtain ⟨K, hK, H, hfix, hheight, hW, hsource, hmatched⟩ := ih
      obtain ⟨L, V, hL, hV, hRV, G, hGfix, hGheight, hGW, hother, hGmatch⟩ := hmoves i
      have hHA : H '' A i = A i := by rw [image_congr (hsource i his), image_id]
      refine ⟨K ∪ L, hK.union hL, H.trans G, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        change G (H x) = x
        rw [hfix x (fun h => hx (Or.inl h)), hGfix x (fun h => hx (Or.inr h))]
      · intro x
        exact (hGheight (H x)).trans (hheight x)
      · intro x hx
        change G (H x) = x
        rw [hW hx, id_eq, hGW hx]
        rfl
      · intro j hj x hx
        have hjs : j ∉ s := fun h => hj (Finset.mem_insert_of_mem h)
        have hji : j ≠ i := fun h => hj (h ▸ Finset.mem_insert_self i s)
        change G (H x) = x
        rw [hsource j hjs hx, id_eq, (hother j hji).1 hx]
        rfl
      · intro j hj
        rcases Finset.mem_insert.mp hj with hji | hjs
        · subst j
          refine ⟨V, hV, hRV, ?_⟩
          change (G ∘ H) '' A i ∩ V = _
          rw [image_comp, hHA]
          exact hGmatch
        · have hji : j ≠ i := fun h => his (h ▸ hjs)
          obtain ⟨U, hU, hRU, heq⟩ := hmatched j hjs
          have hGB : G '' B j = B j := by rw [image_congr (hother j hji).2, image_id]
          refine ⟨G '' U, G.toHomeomorph.isOpenMap _ hU, ?_, ?_⟩
          · intro x hx
            exact ⟨x, hRU hx, (hother j hji).2 (hRB j hx)⟩
          · change (G ∘ H) '' A j ∩ G '' U = _
            rw [image_comp, ← image_inter (f := (G : E3 → E3)) G.injective,
              heq, image_inter (f := (G : E3 → E3)) G.injective, hGB]
  obtain ⟨K, hK, H, hfix, hheight, hW, _, hmatched⟩ := hfinite Finset.univ
  exact ⟨K, hK, H, hfix, hheight, hW, fun i => hmatched i (Finset.mem_univ i)⟩

open SaddleLevel

variable {f : S2 → E3} {M : SphereMorseReduction f} {g : S2 → E3}
  {P : SphereSurgeryPath (M.v : E3) (fun q => M.D (f q)) g}
  {p : S2} {e : OpenPartialHomeomorph E2 S2}

theorem exists_simultaneous_horizontal_terminal_cap_germs
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand) :
    ∃ S : Set E3, IsCompact S ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧
        (∀ z, inner Real (M.v : E3) (G z) = inner Real (M.v : E3) z) ∧
        EqOn G id (data.toTerminalSaddleGeometry.flatten ⁻¹'
          data.toTerminalSaddleGeometry.modelBand) ∧
        (∀ D ∈ data.ends.caps, EqOn (G ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
        ∀ i, ∃ U : Set E3, IsOpen U ∧
          (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
            sphere (0 : E2) 1 ⊆ U ∧
          (G '' (data.toTerminalSaddleGeometry.flatten.symm ''
            (H '' data.toTerminalSaddleGeometry.C i))) ∩ U =
            (data.toTerminalSaddleGeometry.flatten.symm ''
              data.toTerminalSaddleGeometry.modelCaps i) ∩ U := by
  let W := (data.toTerminalSaddleGeometry.flatten ⁻¹' data.toTerminalSaddleGeometry.modelBand) ∪
    ⋃ D : {D // D ∈ data.ends.caps}, g '' (D.1.chart '' closedBall (0 : E2) 1)
  have hRB (i : Fin 3) :
      (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
        sphere (0 : E2) 1 ⊆ data.toTerminalSaddleGeometry.flatten.symm ''
          data.toTerminalSaddleGeometry.modelCaps i := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨data.toTerminalSaddleGeometry.flatten
      (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)), ?_,
      data.toTerminalSaddleGeometry.flatten.symm_apply_apply _⟩
    have hh : data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ∈
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand := by
      rw [data.model_boundary i]
      exact mem_image_of_mem _ hy
    exact hh.1
  have hmoves (i : Fin 3) := exists_separated_horizontal_terminal_cap_germ_within
    data hg Φ χ H hH hχ hplanar hlabels i isOpen_univ (subset_univ _)
  obtain ⟨S, hS, G, hfix, hheight, hW, hcap⟩ :=
    exists_simultaneous_relative_cap_germs_preserving_height
      (fun i => data.toTerminalSaddleGeometry.flatten.symm ''
        (H '' data.toTerminalSaddleGeometry.C i))
      (fun i => data.toTerminalSaddleGeometry.flatten.symm '' data.toTerminalSaddleGeometry.modelCaps i)
      (fun i => (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
        sphere (0 : E2) 1) W (inner Real (M.v : E3)) hRB (fun i => by
        obtain ⟨S, U, hS, _, hU, _, hcU, _, G, hfix, hheight, hband, hcore, hother, hcap, _⟩ := hmoves i
        refine ⟨S, U, hS, hU, hcU, G, hfix, hheight, ?_, hother, hcap⟩
        intro z hz
        rcases hz with hz | hz
        · exact hband hz
        · obtain ⟨D, q, hq, rfl⟩ := mem_iUnion.mp hz
          exact hcore D.1 D.2 hq)
  refine ⟨S, hS, G, hfix, hheight, hW.mono subset_union_left, ?_, hcap⟩
  intro D hD q hq
  exact hW (Or.inr (mem_iUnion.mpr ⟨⟨D, hD⟩, mem_image_of_mem g hq⟩))

theorem exists_surface_germ_of_cap_germ
    {ι : Type*} [Finite ι] {A B : ι → Set E3} {S T W R U : Set E3} (i : ι)
    (hA : ∀ j, IsCompact (A j)) (hB : ∀ j, IsCompact (B j))
    (hAd : Pairwise (fun j k => Disjoint (A j) (A k)))
    (hBd : Pairwise (fun j k => Disjoint (B j) (B k)))
    (hRA : R ⊆ A i) (hRB : R ⊆ B i)
    (hS : S = W ∪ ⋃ j, A j) (hT : T = W ∪ ⋃ j, B j)
    (hU : IsOpen U) (hRU : R ⊆ U) (hcap : A i ∩ U = B i ∩ U) :
    ∃ V : Set E3, IsOpen V ∧ R ⊆ V ∧
      A i ∩ V = B i ∩ V ∧ S ∩ V = T ∩ V := by
  let K : Set E3 := ⋃ j : {j : ι // j ≠ i}, A j ∪ B j
  have hK : IsClosed K := isClosed_iUnion_of_finite
    (fun j => (hA j).isClosed.union (hB j).isClosed)
  have hRK : Disjoint R K := by
    apply disjoint_left.mpr
    intro x hx hKx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hKx
    rcases hj with hj | hj
    · exact disjoint_left.mp (hAd j.property.symm) (hRA hx) hj
    · exact disjoint_left.mp (hBd j.property.symm) (hRB hx) hj
  have hother (j : ι) (hji : j ≠ i) (x : E3) (hx : x ∉ K) : x ∉ A j ∧ x ∉ B j := by
    exact ⟨fun h => hx (mem_iUnion.mpr ⟨⟨j, hji⟩, Or.inl h⟩),
      fun h => hx (mem_iUnion.mpr ⟨⟨j, hji⟩, Or.inr h⟩)⟩
  refine ⟨U ∩ Kᶜ, hU.inter hK.isOpen_compl,
    fun x hx => ⟨hRU hx, fun h => disjoint_left.mp hRK hx h⟩, ?_, ?_⟩
  · rw [← inter_assoc, hcap, inter_assoc]
  · ext x
    constructor
    · rintro ⟨hx, hxV⟩
      refine ⟨?_, hxV⟩
      rcases hS ▸ hx with hxW | hxA
      · exact hT ▸ Or.inl hxW
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hxA
        by_cases hji : j = i
        · subst j
          exact hT ▸ Or.inr (mem_iUnion.mpr ⟨i, (hcap ▸
            (show x ∈ A i ∩ U from ⟨hj, hxV.1⟩)).1⟩)
        · exact False.elim ((hother j hji x hxV.2).1 hj)
    · rintro ⟨hx, hxV⟩
      refine ⟨?_, hxV⟩
      rcases hT ▸ hx with hxW | hxB
      · exact hS ▸ Or.inl hxW
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hxB
        by_cases hji : j = i
        · subst j
          exact hS ▸ Or.inr (mem_iUnion.mpr ⟨i, (hcap.symm ▸
            (show x ∈ B i ∩ U from ⟨hj, hxV.1⟩)).1⟩)
        · exact False.elim ((hother j hji x hxV.2).2 hj)

theorem exists_simultaneous_horizontal_terminal_germs
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (χ : Real → Real) (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand) :
    ∃ S : Set E3, IsCompact S ∧
      ∃ G : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
        (∀ z ∉ S, G z = z) ∧
        (∀ z, inner Real (M.v : E3) (G z) = inner Real (M.v : E3) z) ∧
        EqOn G id (data.toTerminalSaddleGeometry.flatten ⁻¹'
          data.toTerminalSaddleGeometry.modelBand) ∧
        (∀ D ∈ data.ends.caps, EqOn (G ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
        ∀ i, ∃ U : Set E3, IsOpen U ∧
          (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
            sphere (0 : E2) 1 ⊆ U ∧
          (G '' (data.toTerminalSaddleGeometry.flatten.symm ''
            (H '' data.toTerminalSaddleGeometry.C i))) ∩ U =
            (data.toTerminalSaddleGeometry.flatten.symm ''
              data.toTerminalSaddleGeometry.modelCaps i) ∩ U ∧
          (G '' (data.toTerminalSaddleGeometry.flatten.symm ''
            (H '' (data.toTerminalSaddleGeometry.flatten '' range g)))) ∩ U =
            (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U := by
  obtain ⟨S, hS, G, hfix, hheight, hband, hcore, hcap⟩ :=
    exists_simultaneous_horizontal_terminal_cap_germs data hg Φ χ H hH hχ hplanar hlabels
  let J := data.toTerminalSaddleGeometry.flatten.symm
  let W := J '' data.toTerminalSaddleGeometry.modelBand
  have hGW : EqOn G id W := by
    rintro _ ⟨z, hz, rfl⟩
    apply hband
    change data.toTerminalSaddleGeometry.flatten
      (data.toTerminalSaddleGeometry.flatten.symm z) ∈ data.toTerminalSaddleGeometry.modelBand
    rwa [Diffeomorph.apply_symm_apply]
  have hGband : G '' W = W := by rw [image_congr hGW, image_id]
  have hcancel (X : Set E3) : J '' (data.toTerminalSaddleGeometry.flatten '' X) = X := by
    rw [image_image]
    change (fun x => data.toTerminalSaddleGeometry.flatten.symm
      (data.toTerminalSaddleGeometry.flatten x)) '' X = X
    simp only [Diffeomorph.symm_apply_apply, image_id']
  refine ⟨S, hS, G, hfix, hheight, hband, hcore, ?_⟩
  intro i
  obtain ⟨U, hU, hcU, hcapU⟩ := hcap i
  have hrim (y : E2) (hy : y ∈ sphere (0 : E2) 1) :
      data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ∈
          data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand := by
    rw [data.model_boundary i]
    exact mem_image_of_mem _ hy
  apply exists_surface_germ_of_cap_germ i
    (A := fun j => G '' (J '' (H '' data.toTerminalSaddleGeometry.C j)))
    (B := fun j => J '' data.toTerminalSaddleGeometry.modelCaps j) (W := W)
    (S := G '' (J '' (H '' (data.toTerminalSaddleGeometry.flatten '' range g))))
    (T := data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1)
    (fun j => (((isCompact_actual_terminal_cap data hg j).image H.continuous).image
      J.continuous).image G.continuous)
    (fun j => (isCompact_model_terminal_cap data j).image J.continuous)
    (fun j k hjk => disjoint_image_of_injective G.injective
      (disjoint_image_of_injective J.injective
        (disjoint_image_of_injective H.injective (data.actual_disjoint hjk))))
    (fun j k hjk => disjoint_image_of_injective J.injective (data.model_disjoint hjk))
    ?_ ?_ ?_ ?_ hU hcU hcapU
  · rintro _ ⟨y, hy, rfl⟩
    have hx : data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ∈
          H '' data.toTerminalSaddleGeometry.C i :=
      ((terminal_cap_band_inter_image data Φ χ H hH hχ hplanar hlabels i).symm ▸ hrim y hy).1
    refine ⟨data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y),
      ⟨data.toTerminalSaddleGeometry.flatten
        (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)), hx,
        data.toTerminalSaddleGeometry.flatten.symm_apply_apply _⟩, ?_⟩
    exact hband (hrim y hy).2
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨data.toTerminalSaddleGeometry.flatten
      (data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)),
      (hrim y hy).1, data.toTerminalSaddleGeometry.flatten.symm_apply_apply _⟩
  · rw [data.actual_decomposition, image_union, image_iUnion,
      terminal_band_image data Φ χ H hH hχ hplanar, image_union, image_iUnion,
      image_union, image_iUnion, hGband]
  · rw [← hcancel (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1),
      data.model_decomposition, image_union, image_iUnion]

theorem exists_prepared_horizontal_terminal_germs
    (data : TerminalSaddleData M P p e) (hg : g ∈ M.tree.leaves)
    (Φ : Real → Real → Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞)
    (hzero : ∀ z x, Φ 0 z x = x)
    (hΦ : ContDiff Real ∞ (fun q : Real × Real × E2 => Φ q.1 q.2.1 q.2.2))
    (hΦinv : ContDiff Real ∞ (fun q : Real × Real × E2 => (Φ q.1 q.2.1).symm q.2.2))
    (χ : Real → Real) (hχsmooth : ContDiff Real ∞ χ)
    (H : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞)
    (hH : ∀ y, H y = planarHeightMap Φ (χ (y 2)) y)
    (hχ : ∀ z ∈ data.toTerminalSaddleGeometry.I, χ z = 1)
    (hplanar : ∀ z ∈ data.toTerminalSaddleGeometry.I,
      Φ 1 z '' data.toTerminalSaddleGeometry.A z = data.toTerminalSaddleGeometry.B z)
    (hlabels : ∀ i, planarHeightMap Φ 1 ''
      (data.toTerminalSaddleGeometry.C i ∩ data.toTerminalSaddleGeometry.actualBand) =
        data.toTerminalSaddleGeometry.modelCaps i ∩ data.toTerminalSaddleGeometry.modelBand) :
    ∃ E : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
      (∀ y, inner Real (M.v : E3) (E y) = inner Real (M.v : E3) y) ∧
      (∀ D ∈ data.ends.caps, EqOn (E ∘ g) g (D.chart '' closedBall (0 : E2) 1)) ∧
      (∀ i, ∃ U : Set E3, IsOpen U ∧
        (fun y => data.toTerminalSaddleGeometry.filledModel (data.modelDisk i y)) ''
          sphere (0 : E2) 1 ⊆ U ∧
        ((E ∘ g) '' terminalEndCap data.ends (data.labels i)) ∩ U =
          (data.toTerminalSaddleGeometry.flatten.symm ''
            data.toTerminalSaddleGeometry.modelCaps i) ∩ U ∧
        (E '' range g) ∩ U =
          (data.toTerminalSaddleGeometry.filledModel '' sphere (0 : E3) 1) ∩ U) ∧
      ∃ K : Set E3, IsCompact K ∧
        ∃ F : Diffeomorph (𝓡 3) (𝓡 3) E3 E3 ∞,
          (∀ y ∉ K, F y = y) ∧ EqOn F id data.toTerminalSaddleGeometry.modelBand ∧
          (∀ q : S2, F (H (data.toTerminalSaddleGeometry.flatten (g q))) =
            data.toTerminalSaddleGeometry.flatten (E (g q))) ∧
          ∀ i, F '' (H '' data.toTerminalSaddleGeometry.C i) =
            (data.toTerminalSaddleGeometry.flatten ∘ E ∘ g) ''
              terminalEndCap data.ends (data.labels i) := by
  let d := data.toTerminalSaddleGeometry
  obtain ⟨τ, _, hτχ, L, hL, hLheight, hLcore, _, K, hK, F₀, hF₀fix, hF₀slab, hpoint, _⟩ :=
    exists_terminal_lift_preserving_inserted_caps data hg Φ hzero hΦ hΦinv χ hχsmooth H hH
  have hflat (y : E3) : d.flatten y 2 = inner Real (M.v : E3) y :=
    (data.frame_height (data.D y)).trans (data.D_height y)
  have hflati (y : E3) : inner Real (M.v : E3) (d.flatten.symm y) = y 2 := by
    rw [← hflat, d.flatten.apply_symm_apply]
  let Hτ := d.flatten.symm.trans (L.trans d.flatten)
  have hHτ (y : E3) : Hτ y = planarHeightMap Φ (τ (y 2)) y := by
    change d.flatten (L (d.flatten.symm y)) = _
    rw [hL, hflati, d.flatten.apply_symm_apply, d.flatten.apply_symm_apply]
  have hτ : ∀ z ∈ d.I, τ z = 1 := fun z hz => (hτχ hz).trans (hχ z hz)
  obtain ⟨S, hS, G, hGfix, hGheight, hGband, hGcore, hgerms⟩ :=
    exists_simultaneous_horizontal_terminal_germs data hg Φ τ Hτ hHτ hτ hplanar hlabels
  let E := L.trans G
  let F := F₀.trans (d.flatten.symm.trans (G.trans d.flatten))
  have hE (y : E3) : E y = G (L y) := rfl
  have hF (y : E3) : F y = d.flatten (G (d.flatten.symm (F₀ y))) := rfl
  have hFpoint (q : S2) : F (H (d.flatten (g q))) = d.flatten (E (g q)) := by
    rw [hF, hpoint, d.flatten.symm_apply_apply, hE]
  have hprepared_cap (i : Fin 3) :
      G '' (d.flatten.symm '' (Hτ '' d.C i)) =
        (E ∘ g) '' terminalEndCap data.ends (data.labels i) := by
    change G '' (d.flatten.symm '' (Hτ '' ((d.flatten ∘ g) '' _))) = _
    rw [image_image, image_image, image_image]
    apply image_congr
    intro q _
    change G (d.flatten.symm (d.flatten (L (d.flatten.symm (d.flatten (g q)))))) = G (L (g q))
    rw [d.flatten.symm_apply_apply, d.flatten.symm_apply_apply]
  have hprepared_surface : G '' (d.flatten.symm '' (Hτ '' (d.flatten '' range g))) =
      E '' range g := by
    rw [image_image, image_image, image_image]
    apply image_congr
    intro y _
    change G (d.flatten.symm (d.flatten (L (d.flatten.symm (d.flatten y))))) = G (L y)
    rw [d.flatten.symm_apply_apply, d.flatten.symm_apply_apply]
  refine ⟨E, fun y => (hGheight (L y)).trans (hLheight y), ?_, ?_,
    K ∪ d.flatten '' S, hK.union (hS.image d.flatten.continuous), F, ?_, ?_, hFpoint, ?_⟩
  · intro D hD q hq
    change G (L (g q)) = g q
    have hh : L (g q) = g q := hLcore D hD hq
    rw [hh]
    exact hGcore D hD hq
  · intro i
    obtain ⟨U, hU, hcU, hcap, hsurface⟩ := hgerms i
    exact ⟨U, hU, hcU, by rwa [hprepared_cap i] at hcap,
      by rwa [hprepared_surface] at hsurface⟩
  · intro y hy
    rw [hF, hF₀fix y (fun hh => hy (Or.inl hh))]
    have hnot : d.flatten.symm y ∉ S := fun hh =>
      hy (Or.inr ⟨d.flatten.symm y, hh, d.flatten.apply_symm_apply y⟩)
    rw [hGfix _ hnot, d.flatten.apply_symm_apply]
  · intro y hy
    have hyslab : y 2 ∈ d.I := by
      obtain ⟨z, hz, hyz⟩ := mem_iUnion₂.mp hy
      exact hyz.2.symm ▸ hz
    rw [hF, hF₀slab hyslab, id_eq]
    have hbandmem : d.flatten.symm y ∈ d.flatten ⁻¹' d.modelBand := by
      change d.flatten (d.flatten.symm y) ∈ d.modelBand
      rwa [d.flatten.apply_symm_apply]
    rw [hGband hbandmem, id_eq, d.flatten.apply_symm_apply]
  · intro i
    change F '' (H '' ((d.flatten ∘ g) '' _)) = _
    rw [image_image, image_image]
    exact image_congr (fun q _ => hFpoint q)

end Poincare.Manifold.Schoenflies.Saddle.Caps.Closing
