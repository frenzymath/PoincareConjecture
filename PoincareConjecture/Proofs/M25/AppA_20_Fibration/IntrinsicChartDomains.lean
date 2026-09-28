import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicCuts
import PoincareConjecture.Proofs.M25.Mathlib.FiberwiseGraphComplement
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


theorem intrinsic_trimmed_chart_domains
    (C : BalancedNeckChain g epsilon)
    {a0 b0 : ℤ} (hshape : C.shape = ChainShape.finite a0 b0)
    (H : ℤ → M → ℝ)
    (hH : ∀ i ∈ C.shape.active,
      ContinuousOn (H i) (⋃ j ∈ C.shape.active, (C.neck j).carrier) ∧
      (∀ x ∈ (C.neck i).carrier,
        H i x = ((C.neck i).coordinate_inverse x).2) ∧
      (∀ x ∈ (⋃ j ∈ C.shape.active, (C.neck j).carrier),
        x ∉ (C.neck i).carrier →
          H i x = -epsilon⁻¹ ∨ H i x = epsilon⁻¹))
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
    let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
    let a := 23 * L / 32
    let b := 25 * L / 32
    let q0 : ℤ → UnitTwoSphere := fun i =>
      ((C.neck i).coordinate_inverse (C.neck i).center).1
    let S : ℤ → ℝ → Set M := fun i t =>
      range (fun q : UnitTwoSphere => (C.neck i).coordinate_map (q, t))
    let negSide : ℤ → ℝ → Set M := fun i t =>
      connectedComponentIn (U \ S i t)
        ((C.neck i).coordinate_map (q0 i, (t - L) / 2))
    let posSide : ℤ → ℝ → Set M := fun i t =>
      connectedComponentIn (U \ S i t)
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
  let : ConnectedSpace UnitTwoSphere := by
    apply isConnected_iff_connectedSpace.mp
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank]; norm_num) 0 (by norm_num)
  let L : ℝ := epsilon⁻¹
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let a : ℝ := 23 * L / 32
  let b : ℝ := 25 * L / 32
  let q0 : ℤ → UnitTwoSphere := fun i =>
    ((C.neck i).coordinate_inverse (C.neck i).center).1
  let S : ℤ → ℝ → Set M := fun i t =>
    range (fun q : UnitTwoSphere => (C.neck i).coordinate_map (q, t))
  let negSide : ℤ → ℝ → Set M := fun i t =>
    connectedComponentIn (U \ S i t)
      ((C.neck i).coordinate_map (q0 i, (t - L) / 2))
  let posSide : ℤ → ℝ → Set M := fun i t =>
    connectedComponentIn (U \ S i t)
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
    constructor <;> linarith only [hL]
  have haquarter : a ∈ Ioo (L / 2) L := by
    dsimp only [a]
    constructor <;> linarith only [hL]
  have hb : b ∈ Ioo (-L) L := by
    dsimp only [b]
    constructor <;> linarith only [hL]
  have hNU (i : ℤ) (hci : i ∈ C.shape.active) : (C.neck i).carrier ⊆ U :=
    fun _ hx => mem_iUnion₂.mpr ⟨i, hci, hx⟩
  obtain ⟨_, _, hnext, hcuts, _⟩ :=
    C.intrinsic_ordered_cuts_of_relative_heights hshape H hH
  have hlevel (i : ℤ) (hci : i ∈ C.shape.active) (t : ℝ)
      (ht : t ∈ Ioo (-L) L) : U ∩ (H i) ⁻¹' {t} = S i t :=
    (hcuts i hci t ht).1
  have hnegEq (i : ℤ) (hci : i ∈ C.shape.active) (t : ℝ)
      (ht : t ∈ Ioo (-L) L) : negSide i t = U ∩ (H i) ⁻¹' Iio t :=
    (hcuts i hci t ht).2.1
  have hposEq (i : ℤ) (hci : i ∈ C.shape.active) (t : ℝ)
      (ht : t ∈ Ioo (-L) L) : posSide i t = U ∩ (H i) ⁻¹' Ioi t :=
    (hcuts i hci t ht).2.2.1
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
    have hplateau (y : M) (hy : y ∈ (C.neck i).carrier)
        (hyold : y ∉ (C.neck (i - 1)).carrier) : H (i - 1) y = L := by
      exact (hnext (i - 1) hprev hn).2 y
        ⟨by simpa only [sub_add_cancel] using hy, hyold⟩
    have hoverlap (y : M) (hyold : y ∈ (C.neck (i - 1)).carrier)
        (hy : y ∈ (C.neck i).carrier) : ((C.neck i).coordinate_inverse y).2 < L / 2 := by
      have h := (C.overlap_within_three_quarters (i - 1) hprev hn
        ⟨hyold, by simpa only [sub_add_cancel] using hy⟩).2.2.2
      simpa only [sub_add_cancel] using h
    have hinv {y : M} (hy : y ∈ (C.neck i).carrier) : (e i).symm y ∈ (e i).source :=
      (e i).map_target ((he i hci).2.1.symm ▸ hy)
    have hinvStrip {y : M} (hy : y ∈ (C.neck i).carrier) :
        ((e i).symm y).2 ∈ Ioo (-L) L := ((he i hci).1 ▸ hinv hy).2
    have hfdom (q : UnitTwoSphere) : f i q ∈ Ioo (-L) L :=
      ⟨((hgraph i hci hprev).1 q).1,
        (((hgraph i hci hprev).1 q).2).trans (by linarith only [hL])⟩
    have hgraphSource (q : UnitTwoSphere) : (q, f i q) ∈ (e i).source :=
      (he i hci).1.symm ▸ ⟨mem_univ _, hfdom q⟩
    let Dminus : Set RoundCylinderSpace := {z | -L < z.2 ∧ z.2 < f i z.1}
    let Dplus : Set RoundCylinderSpace := {z | f i z.1 < z.2 ∧ z.2 < L}
    let Wminus := (e i) '' Dminus
    let Wplus := (e i) '' Dplus
    have hminusSource : Dminus ⊆ (e i).source := by
      intro z hz
      exact (he i hci).1.symm ▸ ⟨mem_univ _, hz.1, hz.2.trans (hfdom z.1).2⟩
    have hplusSource : Dplus ⊆ (e i).source := by
      intro z hz
      exact (he i hci).1.symm ▸ ⟨mem_univ _, (hfdom z.1).1.trans hz.1, hz.2⟩
    have hminus : IsConnected Wminus :=
      (isConnected_between_continuous_graphs continuous_const (hf i).continuous
        (fun q => (hfdom q).1)).image (e i) ((e i).continuousOn.mono hminusSource)
    have hplus : IsConnected Wplus :=
      (isConnected_between_continuous_graphs (hf i).continuous continuous_const
        (fun q => (hfdom q).2)).image (e i) ((e i).continuousOn.mono hplusSource)
    have hminusCarrier : Wminus ⊆ (C.neck i).carrier := by
      rintro y ⟨z, hz, rfl⟩
      exact hemap i hci z (hminusSource hz)
    have hplusCarrier : Wplus ⊆ (C.neck i).carrier := by
      rintro y ⟨z, hz, rfl⟩
      exact hemap i hci z (hplusSource hz)
    have hminusU : Wminus ⊆ U := hminusCarrier.trans (hNU i hci)
    have hplusU : Wplus ⊆ U := hplusCarrier.trans (hNU i hci)
    have hmemMinus {y : M} (hy : y ∈ (C.neck i).carrier) :
        y ∈ Wminus ↔ ((e i).symm y).2 < f i ((e i).symm y).1 := by
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [(e i).left_inv (hminusSource hz)] using hz.2
      · intro hs
        exact ⟨(e i).symm y, ⟨(hinvStrip hy).1, hs⟩,
          (e i).right_inv ((he i hci).2.1.symm ▸ hy)⟩
    have hmemPlus {y : M} (hy : y ∈ (C.neck i).carrier) :
        y ∈ Wplus ↔ f i ((e i).symm y).1 < ((e i).symm y).2 := by
      constructor
      · rintro ⟨z, hz, rfl⟩
        simpa only [(e i).left_inv (hplusSource hz)] using hz.1
      · intro hs
        exact ⟨(e i).symm y, ⟨hs, (hinvStrip hy).2⟩,
          (e i).right_inv ((he i hci).2.1.symm ▸ hy)⟩
    have hlev {y : M} (hy : y ∈ (C.neck i).carrier) :
        H (i - 1) y = a ↔ y ∈ S (i - 1) a := by
      constructor
      · intro hs
        exact hlevel (i - 1) hprev a ha ▸ ⟨hNU i hci hy, hs⟩
      · intro hs
        have hyLevel : y ∈ U ∩ (H (i - 1)) ⁻¹' {a} :=
          (hlevel (i - 1) hprev a ha).symm ▸ hs
        exact hyLevel.2
    have hequal {y : M} (hy : y ∈ (C.neck i).carrier) :
        H (i - 1) y = a ↔ ((e i).symm y).2 = f i ((e i).symm y).1 := by
      rw [hlev hy, (hgraph i hci hprev).2]
      constructor
      · rintro ⟨q, rfl⟩
        rw [(e i).left_inv (hgraphSource q)]
      · intro hs
        refine ⟨((e i).symm y).1, ?_⟩
        change e i (((e i).symm y).1, f i ((e i).symm y).1) = y
        rw [← hs]
        exact (e i).right_inv ((he i hci).2.1.symm ▸ hy)
    have hminusNe : ∀ y ∈ Wminus, H (i - 1) y ≠ a := by
      intro y hy heq
      exact (ne_of_lt ((hmemMinus (hminusCarrier hy)).mp hy))
        ((hequal (hminusCarrier hy)).mp heq)
    have hplusNe : ∀ y ∈ Wplus, H (i - 1) y ≠ a := by
      intro y hy heq
      exact (ne_of_gt ((hmemPlus (hplusCarrier hy)).mp hy))
        ((hequal (hplusCarrier hy)).mp heq)
    let yplus := e i (q0 i, 3 * L / 4)
    have hypSource : (q0 i, 3 * L / 4) ∈ (e i).source := by
      exact (he i hci).1.symm ▸ ⟨mem_univ _,
        (show -L < 3 * L / 4 by linarith only [hL]),
        (show 3 * L / 4 < L by linarith only [hL])⟩
    have hypCarrier : yplus ∈ (C.neck i).carrier := hemap i hci _ hypSource
    have hypNot : yplus ∉ (C.neck (i - 1)).carrier := by
      intro hy
      have h := hoverlap yplus hy hypCarrier
      rw [heheight i hci _ hypSource] at h
      change 3 * L / 4 < L / 2 at h
      linarith only [hL, h]
    have hypPlus : yplus ∈ Wplus := by
      refine ⟨(q0 i, 3 * L / 4), ?_, rfl⟩
      change f i (q0 i) < 3 * L / 4 ∧ 3 * L / 4 < L
      have hq := ((hgraph i hci hprev).1 (q0 i)).2
      constructor <;> linarith only [hL, hq]
    have hplusSign : ∀ y ∈ Wplus, a < H (i - 1) y := by
      intro y hy
      apply hplus.isPreconnected.lt_of_ne ((hH (i - 1) hprev).1.mono hplusU)
        hplusNe ?_ hy
      refine ⟨yplus, hypPlus, ?_⟩
      rw [hplateau yplus hypCarrier hypNot]
      exact ha.2
    let r := (L / 2 + a) / 2
    have hr : r ∈ Ioo (L / 2) a := by
      dsimp only [r]
      constructor <;> linarith only [haquarter.1]
    have hrdom : r ∈ Ioo (-L) L :=
      ⟨by linarith only [hL, hr.1], hr.2.trans ha.2⟩
    have hrnative : r ∈ Ioo (-(C.neck (i - 1)).epsilon⁻¹)
        (C.neck (i - 1)).epsilon⁻¹ := by
      simpa only [C.epsilon_eq (i - 1) hprev] using hrdom
    let yminus := (C.neck (i - 1)).coordinate_map (q0 (i - 1), r)
    have hymOld : yminus ∈ (C.neck (i - 1)).carrier :=
      (C.neck (i - 1)).coordinate_map_mem ⟨mem_univ _, hrnative⟩
    have hymQuarter : yminus ∈ (C.neck (i - 1)).region (L / 2) L := by
      refine ⟨hymOld, ?_⟩
      rw [(C.neck (i - 1)).coordinate_inverse_map _ hrnative]
      exact ⟨hr.1, hr.2.trans ha.2⟩
    have hymCarrier : yminus ∈ (C.neck i).carrier := by
      simpa only [sub_add_cancel] using
        (C.overlap_contains_quarters (i - 1) hprev hn).1 hymQuarter
    have hymHeight : H (i - 1) yminus < a := by
      rw [(hH (i - 1) hprev).2.1 _ hymOld,
        (C.neck (i - 1)).coordinate_inverse_map _ hrnative]
      exact hr.2
    have hymMinus : yminus ∈ Wminus := by
      apply (hmemMinus hymCarrier).mpr
      rcases lt_trichotomy ((e i).symm yminus).2
          (f i ((e i).symm yminus).1) with hlo | heq | hhi
      · exact hlo
      · exact False.elim (hymHeight.ne ((hequal hymCarrier).mpr heq))
      · exact False.elim (lt_asymm hymHeight (hplusSign _ ((hmemPlus hymCarrier).mpr hhi)))
    have hminusSign : ∀ y ∈ Wminus, H (i - 1) y < a := by
      intro y hy
      exact hminus.isPreconnected.gt_of_ne ((hH (i - 1) hprev).1.mono hminusU)
        hminusNe ⟨yminus, hymMinus, hymHeight⟩ hy
    rw [hposEq (i - 1) hprev a ha]
    change (x ∈ U ∧ a < H (i - 1) x) ↔ _
    rw [and_iff_right (hNU i hci hx)]
    constructor
    · intro hs
      rcases lt_trichotomy ((e i).symm x).2 (f i ((e i).symm x).1) with hlo | heq | hhi
      · exact False.elim (lt_asymm hs (hminusSign x ((hmemMinus hx).mpr hlo)))
      · exact False.elim (hs.ne ((hequal hx).mpr heq).symm)
      · exact hhi
    · intro hs
      exact hplusSign x ((hmemPlus hx).mpr hs)
  have hnegative (i : ℤ) (hci : i ∈ C.shape.active)
      (x : M) (hx : x ∈ (C.neck i).carrier) :
      x ∈ negSide i b ↔ ((C.neck i).coordinate_inverse x).2 < b := by
    rw [hnegEq i hci b hb]
    change (x ∈ U ∧ H i x < b) ↔ ((C.neck i).coordinate_inverse x).2 < b
    rw [(hH i hci).2.1 x hx]
    exact and_iff_right (hNU i hci hx)
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
        linarith only [hL, hq]
      · simp only [lo, if_neg hprev]
        linarith only [hL]
    · by_cases hnext : i + 1 ∈ C.shape.active
      · simp only [hi, if_pos hnext, b]
        linarith only [hL]
      · simp only [hi, if_neg hnext]
        linarith only [hL]
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
