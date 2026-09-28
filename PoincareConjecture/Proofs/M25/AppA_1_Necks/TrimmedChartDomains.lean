import PoincareConjecture.Proofs.M25.AppA_1_Necks.OrderedChainCuts
import PoincareConjecture.Proofs.M25.AppA_1_Necks.OrderedGraphSides
import Mathlib.Geometry.Manifold.ContMDiff.Constructions

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.BalancedNeckChain

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ}

open Classical in

theorem trimmed_chart_domains
    (C : BalancedNeckChain g epsilon)
    (hsep : ∀ i ∈ C.shape.active, (C.neck i).IsSeparating)
    (e : ℤ → OpenPartialHomeomorph RoundCylinderSpace M)
    (A : ℤ → Diffeomorph (𝓡 2) (𝓡 2)
      UnitTwoSphere UnitTwoSphere ∞)
    (D : ℤ → Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
      ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞)
    (he : ∀ i ∈ C.shape.active,
      (e i).source = univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹ ∧
      (e i).target = (C.neck i).carrier ∧
      (∀ z ∈ univ ×ˢ Ioo (-epsilon⁻¹) epsilon⁻¹,
        ((C.neck i).coordinate_inverse (e i z)).2 = z.2))
    (hfirst : ∀ i : ℤ, ∀ z : RoundCylinderSpace, (D i z).1 = A i z.1)
    (hcut : ∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
      ∀ q : UnitTwoSphere,
        D i (q, 23 * epsilon⁻¹ / 32) ∈
          univ ×ˢ Ioo (-epsilon⁻¹) (epsilon⁻¹ / 2) ∧
        D i (q, 23 * epsilon⁻¹ / 32) =
          (e (i + 1)).symm (e i (q, 23 * epsilon⁻¹ / 32)) ∧
        e (i + 1) (D i (q, 23 * epsilon⁻¹ / 32)) =
          e i (q, 23 * epsilon⁻¹ / 32)) :
    let L := epsilon⁻¹
    let a := 23 * L / 32
    let b := 25 * L / 32
    let q0 : ℤ → UnitTwoSphere := fun i =>
      ((C.neck i).coordinate_inverse (C.neck i).center).1
    let S : ℤ → ℝ → Set M := fun i t =>
      range (fun q : UnitTwoSphere => (C.neck i).coordinate_map (q, t))
    let negSide : ℤ → ℝ → Set M := fun i t =>
      connectedComponentIn (S i t)ᶜ
        ((C.neck i).coordinate_map (q0 i, (t - L) / 2))
    let posSide : ℤ → ℝ → Set M := fun i t =>
      connectedComponentIn (S i t)ᶜ
        ((C.neck i).coordinate_map (q0 i, (t + L) / 2))
    let W : ℤ → Set M := fun i => if i ∈ C.shape.active then
      ((C.neck i).carrier ∩
        (if i - 1 ∈ C.shape.active then posSide (i - 1) a else univ)) ∩
        (if i + 1 ∈ C.shape.active then negSide i b else univ) else ∅
    let f : ℤ → UnitTwoSphere → ℝ := fun i q =>
      (D (i - 1) ((A (i - 1)).symm q, a)).2
    let lo : ℤ → UnitTwoSphere → ℝ := fun i q =>
      if i - 1 ∈ C.shape.active then f i q else -L
    let hi : ℤ → ℝ := fun i => if i + 1 ∈ C.shape.active then b else L
    let Q : ℤ → Set RoundCylinderSpace := fun i =>
      {z | lo i z.1 < z.2 ∧ z.2 < hi i}
    (∀ i : ℤ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f i)) ∧
    (∀ i ∈ C.shape.active, i - 1 ∈ C.shape.active →
      (∀ q : UnitTwoSphere, f i q ∈ Ioo (-L) (L / 2)) ∧
      S (i - 1) a = range (fun q : UnitTwoSphere => e i (q, f i q))) ∧
    (∀ i ∈ C.shape.active,
      (e i).symm '' W i = Q i ∧
      (e i).source ∩ (e i) ⁻¹' W i = Q i ∧
      Q i ⊆ (e i).source ∧
      (∀ q : UnitTwoSphere, lo i q < 3 * L / 4 ∧ 3 * L / 4 < hi i) ∧
      (∀ q : UnitTwoSphere, e i (q, 3 * L / 4) ∈ W i)) := by
  classical
  let L : ℝ := epsilon⁻¹
  let a : ℝ := 23 * L / 32
  let b : ℝ := 25 * L / 32
  let q0 : ℤ → UnitTwoSphere := fun i =>
    ((C.neck i).coordinate_inverse (C.neck i).center).1
  let S : ℤ → ℝ → Set M := fun i t =>
    range (fun q : UnitTwoSphere => (C.neck i).coordinate_map (q, t))
  let negSide : ℤ → ℝ → Set M := fun i t =>
    connectedComponentIn (S i t)ᶜ
      ((C.neck i).coordinate_map (q0 i, (t - L) / 2))
  let posSide : ℤ → ℝ → Set M := fun i t =>
    connectedComponentIn (S i t)ᶜ
      ((C.neck i).coordinate_map (q0 i, (t + L) / 2))
  let W : ℤ → Set M := fun i => if i ∈ C.shape.active then
    ((C.neck i).carrier ∩
      (if i - 1 ∈ C.shape.active then posSide (i - 1) a else univ)) ∩
      (if i + 1 ∈ C.shape.active then negSide i b else univ) else ∅
  let f : ℤ → UnitTwoSphere → ℝ := fun i q =>
    (D (i - 1) ((A (i - 1)).symm q, a)).2
  let lo : ℤ → UnitTwoSphere → ℝ := fun i q =>
    if i - 1 ∈ C.shape.active then f i q else -L
  let hi : ℤ → ℝ := fun i => if i + 1 ∈ C.shape.active then b else L
  let Q : ℤ → Set RoundCylinderSpace := fun i =>
    {z | lo i z.1 < z.2 ∧ z.2 < hi i}
  change (∀ i : ℤ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f i)) ∧
    (∀ i ∈ C.shape.active, i - 1 ∈ C.shape.active →
      (∀ q : UnitTwoSphere, f i q ∈ Ioo (-L) (L / 2)) ∧
      S (i - 1) a = range (fun q : UnitTwoSphere => e i (q, f i q))) ∧
    (∀ i ∈ C.shape.active,
      (e i).symm '' W i = Q i ∧
      (e i).source ∩ (e i) ⁻¹' W i = Q i ∧
      Q i ⊆ (e i).source ∧
      (∀ q : UnitTwoSphere, lo i q < 3 * L / 4 ∧ 3 * L / 4 < hi i) ∧
      (∀ q : UnitTwoSphere, e i (q, 3 * L / 4) ∈ W i))
  obtain ⟨i0, hi0⟩ := C.active_nonempty
  have hepos : 0 < epsilon := C.epsilon_eq i0 hi0 ▸ (C.neck i0).epsilon_pos
  have hL : 0 < L := inv_pos.mpr hepos
  have ha : a ∈ Ioo (-L) L := by
    dsimp only [a]
    constructor <;> linarith
  have haquarter : a ∈ Ioo (L / 2) L := by
    dsimp only [a]
    constructor <;> linarith
  have hb : b ∈ Ioo (-L) L := by
    dsimp only [b]
    constructor <;> linarith
  have hcommon (i : ℤ) (hci : i ∈ C.shape.active) :
      (C.neck i).cylinderDomain = univ ×ˢ Ioo (-L) L := by
    simp only [EpsilonNeck.cylinderDomain, C.epsilon_eq i hci, L]
  have hes (i : ℤ) (hci : i ∈ C.shape.active) :
      (e i).source = (C.neck i).cylinderDomain :=
    (he i hci).1.trans (hcommon i hci).symm
  have heheight (i : ℤ) (hci : i ∈ C.shape.active) (z : RoundCylinderSpace)
      (hz : z ∈ (e i).source) :
      ((C.neck i).coordinate_inverse (e i z)).2 = z.2 :=
    (he i hci).2.2 z ((he i hci).1 ▸ hz)
  have hemap (i : ℤ) (hci : i ∈ C.shape.active) (z : RoundCylinderSpace)
      (hz : z ∈ (e i).source) : e i z ∈ (C.neck i).carrier :=
    (he i hci).2.1 ▸ (e i).map_source hz
  have hf (i : ℤ) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (f i) :=
    contMDiff_snd.comp ((D (i - 1)).contMDiff.comp
      ((A (i - 1)).symm.contMDiff.prodMk contMDiff_const))
  have hcutAt (i : ℤ) (hci : i ∈ C.shape.active)
      (hprev : i - 1 ∈ C.shape.active) (q : UnitTwoSphere) :
      D (i - 1) (q, a) ∈ univ ×ˢ Ioo (-L) (L / 2) ∧
      D (i - 1) (q, a) = (e i).symm (e (i - 1) (q, a)) ∧
      e i (D (i - 1) (q, a)) = e (i - 1) (q, a) := by
    simpa only [sub_add_cancel] using
      hcut (i - 1) hprev (by simpa only [sub_add_cancel] using hci) q
  have hslice (i : ℤ) (hci : i ∈ C.shape.active) :
      S i a = range (fun q : UnitTwoSphere => e i (q, a)) := by
    have han : a ∈ Ioo (-(C.neck i).epsilon⁻¹) (C.neck i).epsilon⁻¹ := by
      simpa only [C.epsilon_eq i hci] using ha
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      let x := (C.neck i).coordinate_map (q, a)
      have hx : x ∈ (C.neck i).carrier :=
        (C.neck i).coordinate_map_mem ⟨mem_univ _, han⟩
      have hxt : x ∈ (e i).target := (he i hci).2.1.symm ▸ hx
      have hinv : (e i).symm x ∈ (e i).source := (e i).map_target hxt
      have hh := heheight i hci ((e i).symm x) hinv
      rw [(e i).right_inv hxt] at hh
      have hh0 : ((C.neck i).coordinate_inverse x).2 = a :=
        congrArg Prod.snd ((C.neck i).coordinate_inverse_map (q, a) han)
      have hv : ((e i).symm x).2 = a := hh.symm.trans hh0
      refine ⟨((e i).symm x).1, ?_⟩
      change e i (((e i).symm x).1, a) = x
      rw [show (((e i).symm x).1, a) = (e i).symm x from Prod.ext rfl hv.symm]
      exact (e i).right_inv hxt
    · rintro ⟨q, rfl⟩
      have hz : (q, a) ∈ (e i).source :=
        (he i hci).1.symm ▸ ⟨mem_univ _, ha⟩
      have hx := hemap i hci (q, a) hz
      have hh := heheight i hci (q, a) hz
      refine ⟨((C.neck i).coordinate_inverse (e i (q, a))).1, ?_⟩
      change (C.neck i).coordinate_map
        (((C.neck i).coordinate_inverse (e i (q, a))).1, a) = e i (q, a)
      rw [show (((C.neck i).coordinate_inverse (e i (q, a))).1, a) =
        (C.neck i).coordinate_inverse (e i (q, a)) from Prod.ext rfl hh.symm]
      exact (C.neck i).coordinate_map_inverse hx
  have hgraph (i : ℤ) (hci : i ∈ C.shape.active)
      (hprev : i - 1 ∈ C.shape.active) :
      (∀ q : UnitTwoSphere, f i q ∈ Ioo (-L) (L / 2)) ∧
      S (i - 1) a = range (fun q : UnitTwoSphere => e i (q, f i q)) := by
    refine ⟨fun q => (hcutAt i hci hprev ((A (i - 1)).symm q)).1.2, ?_⟩
    rw [hslice (i - 1) hprev]
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      refine ⟨A (i - 1) q, ?_⟩
      have hp : D (i - 1) (q, a) =
          (A (i - 1) q, f i (A (i - 1) q)) := by
        apply Prod.ext
        · exact hfirst (i - 1) (q, a)
        · simp only [f, Diffeomorph.symm_apply_apply]
      change e i (A (i - 1) q, f i (A (i - 1) q)) = e (i - 1) (q, a)
      rw [← hp]
      exact (hcutAt i hci hprev q).2.2
    · rintro ⟨q, rfl⟩
      refine ⟨(A (i - 1)).symm q, ?_⟩
      have hp : D (i - 1) ((A (i - 1)).symm q, a) = (q, f i q) := by
        apply Prod.ext
        · rw [hfirst, Diffeomorph.apply_symm_apply]
        · rfl
      have hv := (hcutAt i hci hprev ((A (i - 1)).symm q)).2.2
      rw [hp] at hv
      exact hv.symm
  have hpositive (i : ℤ) (hci : i ∈ C.shape.active)
      (hprev : i - 1 ∈ C.shape.active) (x : M) (hx : x ∈ (C.neck i).carrier) :
      x ∈ posSide (i - 1) a ↔ f i ((e i).symm x).1 < ((e i).symm x).2 := by
    have hn : i - 1 + 1 ∈ C.shape.active := by
      simpa only [sub_add_cancel] using hci
    have hquarter : (C.neck (i - 1)).region ((C.neck (i - 1)).epsilon⁻¹ / 2)
        (C.neck (i - 1)).epsilon⁻¹ ⊆ (C.neck i).carrier := by
      simpa only [sub_add_cancel, C.epsilon_eq (i - 1) hprev] using
        (C.overlap_contains_quarters (i - 1) hprev hn).1
    have hoverlap : (C.neck (i - 1)).carrier ∩ (C.neck i).carrier ⊆
        (C.neck (i - 1)).region (-(C.neck (i - 1)).epsilon⁻¹ / 2)
          (C.neck (i - 1)).epsilon⁻¹ ∩
        (C.neck i).region (-(C.neck i).epsilon⁻¹) ((C.neck i).epsilon⁻¹ / 2) := by
      simpa only [sub_add_cancel, C.epsilon_eq (i - 1) hprev, C.epsilon_eq i hci] using
        C.overlap_within_three_quarters (i - 1) hprev hn
    have hheight : ∀ z ∈ (C.neck i).cylinderDomain,
        ((C.neck i).coordinate_inverse (e i z)).2 = z.2 := by
      intro z hz
      exact heheight i hci z ((hes i hci).symm ▸ hz)
    have hta : a ∈ Ioo ((C.neck (i - 1)).epsilon⁻¹ / 2)
        (C.neck (i - 1)).epsilon⁻¹ := by
      simpa only [C.epsilon_eq (i - 1) hprev] using haquarter
    have hfdom (q : UnitTwoSphere) :
        f i q ∈ Ioo (-(C.neck i).epsilon⁻¹) (C.neck i).epsilon⁻¹ := by
      rw [C.epsilon_eq i hci]
      have hq := (hgraph i hci hprev).1 q
      exact ⟨hq.1, by change f i q < L; linarith [hq.2]⟩
    obtain ⟨_, hsides⟩ :=
      (C.neck (i - 1)).graph_sides_in_height_preserving_chart (C.neck i)
        (hsep (i - 1) hprev) hquarter hoverlap (e i) (hes i hci)
        (he i hci).2.1 hheight hta (f i) (hf i).continuous hfdom
        (hgraph i hci hprev).2
    simpa only [posSide, S, q0, L, C.epsilon_eq (i - 1) hprev] using (hsides x hx).2
  obtain ⟨H, _, hH, _, _, hSides, _⟩ := C.exists_ordered_saturated_heights hsep
  have hnegative (i : ℤ) (hci : i ∈ C.shape.active)
      (x : M) (hx : x ∈ (C.neck i).carrier) :
      x ∈ negSide i b ↔ ((C.neck i).coordinate_inverse x).2 < b := by
    have hside : negSide i b =
        connectedComponent (C.neck i).center ∩ (H i) ⁻¹' Iio b :=
      (hSides i hci b hb).1
    rw [hside]
    change (x ∈ connectedComponent (C.neck i).center ∧ H i x < b) ↔
      ((C.neck i).coordinate_inverse x).2 < b
    rw [(hH i hci).2.1 x hx]
    exact and_iff_right ((C.neck i).m25_carrier_subset_connectedComponent hx)
  have hQsource (i : ℤ) (hci : i ∈ C.shape.active) : Q i ⊆ (e i).source := by
    intro z hz
    change lo i z.1 < z.2 ∧ z.2 < hi i at hz
    have hlow : -L < z.2 := by
      by_cases hprev : i - 1 ∈ C.shape.active
      · have hfz := (hgraph i hci hprev).1 z.1
        have hlt : f i z.1 < z.2 := by simpa only [lo, if_pos hprev] using hz.1
        exact hfz.1.trans hlt
      · simpa only [lo, if_neg hprev] using hz.1
    have hupp : z.2 < L := by
      by_cases hnext : i + 1 ∈ C.shape.active
      · have hlt : z.2 < b := by simpa only [hi, if_pos hnext] using hz.2
        exact hlt.trans hb.2
      · simpa only [hi, if_neg hnext] using hz.2
    exact (he i hci).1.symm ▸ ⟨mem_univ _, hlow, hupp⟩
  have hmem (i : ℤ) (hci : i ∈ C.shape.active)
      (z : RoundCylinderSpace) (hz : z ∈ (e i).source) :
      e i z ∈ W i ↔ z ∈ Q i := by
    have hx := hemap i hci z hz
    have hstrip : z.2 ∈ Ioo (-L) L := ((he i hci).1 ▸ hz).2
    have hincoming :
        e i z ∈ (if i - 1 ∈ C.shape.active then posSide (i - 1) a else univ) ↔
          lo i z.1 < z.2 := by
      by_cases hprev : i - 1 ∈ C.shape.active
      · have hs := hpositive i hci hprev (e i z) hx
        simpa only [if_pos hprev, lo, (e i).left_inv hz] using hs
      · simpa only [if_neg hprev, lo, mem_univ, true_iff] using hstrip.1
    have houtgoing :
        e i z ∈ (if i + 1 ∈ C.shape.active then negSide i b else univ) ↔
          z.2 < hi i := by
      by_cases hnext : i + 1 ∈ C.shape.active
      · have hs := hnegative i hci (e i z) hx
        simpa only [if_pos hnext, hi, heheight i hci z hz] using hs
      · simpa only [if_neg hnext, hi, mem_univ, true_iff] using hstrip.2
    simpa only [W, if_pos hci, mem_inter_iff, hx, true_and, Q, mem_ofPred_eq] using
      and_congr hincoming houtgoing
  have hWcarrier (i : ℤ) (hci : i ∈ C.shape.active) : W i ⊆ (C.neck i).carrier := by
    intro x hx
    have hx' :
        (x ∈ (C.neck i).carrier ∧
          x ∈ (if i - 1 ∈ C.shape.active then posSide (i - 1) a else univ)) ∧
          x ∈ (if i + 1 ∈ C.shape.active then negSide i b else univ) := by
      simpa only [W, if_pos hci, mem_inter_iff] using hx
    exact hx'.1.1
  have hmid (i : ℤ) (hci : i ∈ C.shape.active) (q : UnitTwoSphere) :
      lo i q < 3 * L / 4 ∧ 3 * L / 4 < hi i := by
    constructor
    · by_cases hprev : i - 1 ∈ C.shape.active
      · have hq := ((hgraph i hci hprev).1 q).2
        simp only [lo, if_pos hprev]
        linarith
      · simp only [lo, if_neg hprev]
        linarith
    · by_cases hnext : i + 1 ∈ C.shape.active
      · simp only [hi, if_pos hnext, b]
        linarith
      · simp only [hi, if_neg hnext]
        linarith
  refine ⟨hf, hgraph, ?_⟩
  intro i hci
  refine ⟨?_, ?_, hQsource i hci, hmid i hci, ?_⟩
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxt : x ∈ (e i).target := (he i hci).2.1.symm ▸ hWcarrier i hci hx
      have hz := (e i).map_target hxt
      apply (hmem i hci ((e i).symm x) hz).mp
      simpa only [(e i).right_inv hxt] using hx
    · intro hz
      have hs := hQsource i hci hz
      exact ⟨e i z, (hmem i hci z hs).mpr hz, (e i).left_inv hs⟩
  · ext z
    constructor
    · rintro ⟨hz, hw⟩
      exact (hmem i hci z hz).mp hw
    · intro hz
      have hs := hQsource i hci hz
      exact ⟨hs, (hmem i hci z hs).mpr hz⟩
  · intro q
    have hq : (q, 3 * L / 4) ∈ Q i := hmid i hci q
    exact (hmem i hci (q, 3 * L / 4) (hQsource i hci hq)).mpr hq

end PoincareConjecture.BalancedNeckChain
