import PoincareConjecture.Proofs.M25.AppA_1_Necks.ChainChartImages
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.BalancedNeckChain

open Classical in

theorem exists_smooth_chain_partial_chart :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon), epsilon ≤ epsilon0 →
      (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
      ∀ k ∈ C.shape.active,
      let L := epsilon⁻¹
      let a := 23 * L / 32
      let b := 25 * L / 32
      let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
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
      ∃ (e : ℤ → OpenPartialHomeomorph RoundCylinderSpace M)
        (F : ℤ → Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
          ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞)
        (B : ℤ → Diffeomorph (𝓡 2) (𝓡 2)
          UnitTwoSphere UnitTwoSphere ∞)
        (P : OpenPartialHomeomorph M RoundCylinderSpace),
      let ell : UnitTwoSphere → ℝ := fun r => match C.shape with
        | .finite first _ => (F first ((B first).symm r, -L)).2
        | .forward first => (F first ((B first).symm r, -L)).2
        | .backward _ => -L
        | .biInfinite => -L
      let upper : UnitTwoSphere → ℝ := fun r => match C.shape with
        | .finite _ last => (F last ((B last).symm r, L)).2
        | .forward _ => L
        | .backward last => (F last ((B last).symm r, L)).2
        | .biInfinite => L
      let V : Set RoundCylinderSpace := match C.shape with
        | .finite _ _ => {z | ell z.1 < z.2 ∧ z.2 < upper z.1}
        | .forward _ => {z | ell z.1 < z.2}
        | .backward _ => {z | z.2 < upper z.1}
        | .biInfinite => univ
      let Vlocal : ℤ → Set RoundCylinderSpace := fun i => F i '' ((e i).symm '' W i)
      F k = Diffeomorph.refl ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace ∞ ∧
      B k = Diffeomorph.refl (𝓡 2) UnitTwoSphere ∞ ∧
      (∀ i ∈ C.shape.active,
        (e i).source = univ ×ˢ Ioo (-L) L ∧ (e i).target = (C.neck i).carrier ∧
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (e i) (e i).source ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (e i).symm (e i).target ∧
        (∀ z ∈ (e i).source,
          ((C.neck i).coordinate_inverse (e i z)).2 = z.2) ∧
        (∀ q : UnitTwoSphere, e i (q, 0) = (C.neck i).coordinate_map (q, 0)) ∧
        (∀ q : UnitTwoSphere, e i (q, 3 * L / 4) ∈ W i)) ∧
      (∀ i : ℤ, ∀ z : RoundCylinderSpace,
        (F i z).1 = B i z.1 ∧ ((F i).symm z).1 = (B i).symm z.1) ∧
      (∀ i : ℤ, ∀ q : UnitTwoSphere, StrictMono (fun s : ℝ => (F i (q, s)).2)) ∧
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ ell ∧
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ upper ∧
      (∀ r : UnitTwoSphere, ell r ≤ -L ∧ L ≤ upper r) ∧
      P.source = U ∧ P.target = V ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ P P.source ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ P.symm P.target ∧
      (∀ i : ℤ,
        EqOn P (fun x => F i ((e i).symm x)) (W i) ∧
        EqOn P.symm (fun z => e i ((F i).symm z)) (Vlocal i) ∧
        P '' W i = Vlocal i ∧
        P.source ∩ P ⁻¹' Vlocal i = W i) := by
  classical
  obtain ⟨epsilon0, hepos, hecap, hatlas⟩ := exists_trimmed_chain_image_atlas.{u}
  refine ⟨epsilon0, hepos, hecap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C hepsilon hsep k hk
  let L : ℝ := epsilon⁻¹
  let a : ℝ := 23 * L / 32
  let b : ℝ := 25 * L / 32
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
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
  obtain ⟨e, F, B, hData⟩ := hatlas C hepsilon hsep k hk
  obtain ⟨hFk, hBk, he, hfirst, hmono, hell, hupper, hbounds, _,
    hLocal, hWUnion, hVUnion, _, _, _, _, _, _, hAgree⟩ := hData
  change (⋃ i : ℤ, W i) = U at hWUnion
  let ell : UnitTwoSphere → ℝ := fun r => match C.shape with
    | .finite first _ => (F first ((B first).symm r, -L)).2
    | .forward first => (F first ((B first).symm r, -L)).2
    | .backward _ => -L
    | .biInfinite => -L
  let upper : UnitTwoSphere → ℝ := fun r => match C.shape with
    | .finite _ last => (F last ((B last).symm r, L)).2
    | .forward _ => L
    | .backward last => (F last ((B last).symm r, L)).2
    | .biInfinite => L
  let V : Set RoundCylinderSpace := match C.shape with
    | .finite _ _ => {z | ell z.1 < z.2 ∧ z.2 < upper z.1}
    | .forward _ => {z | ell z.1 < z.2}
    | .backward _ => {z | z.2 < upper z.1}
    | .biInfinite => univ
  let Pi : ℤ → OpenPartialHomeomorph M RoundCylinderSpace := fun i =>
    ((e i).symm.restr (W i)).trans (F i).toHomeomorph.toOpenPartialHomeomorph
  let T : ℤ → Set RoundCylinderSpace := fun i => (Pi i).target
  let Vlocal : ℤ → Set RoundCylinderSpace := fun i => F i '' ((e i).symm '' W i)
  have hsource (i : ℤ) : (Pi i).source = W i := (hLocal i).1
  have hforwardFormula (i : ℤ) (x : M) : Pi i x = F i ((e i).symm x) := rfl
  have hinverseFormula (i : ℤ) (z : RoundCylinderSpace) :
      (Pi i).symm z = e i ((F i).symm z) := rfl
  have hTUnion : (⋃ i : ℤ, T i) = V := by
    calc
      (⋃ i : ℤ, T i) = _ := iUnion_congr (fun i => (hLocal i).2.1)
      _ = V := hVUnion
  have hTimage (i : ℤ) : T i = Vlocal i := by
    calc
      T i = Pi i '' (Pi i).source := (Pi i).image_source_eq_target.symm
      _ = Pi i '' W i := by rw [hsource i]
      _ = Vlocal i := by
        change (fun x => F i ((e i).symm x)) '' W i = F i '' ((e i).symm '' W i)
        rw [image_image]
  have hforwardAgree (i j : ℤ) : EqOn (Pi i) (Pi j) (W i ∩ W j) :=
    (hAgree i j).1
  have hinverseAgree (i j : ℤ) : EqOn (Pi i).symm (Pi j).symm (T i ∩ T j) := by
    intro z hz
    exact (hAgree i j).2 ⟨(hLocal i).2.1 ▸ hz.1, (hLocal j).2.1 ▸ hz.2⟩
  have hWsub (i : ℤ) : W i ⊆ U := by
    intro x hx
    exact hWUnion ▸ mem_iUnion.mpr ⟨i, hx⟩
  have hTsub (i : ℤ) : T i ⊆ V := by
    intro z hz
    exact hTUnion ▸ mem_iUnion.mpr ⟨i, hz⟩
  have hchooseW (x : M) (hx : x ∈ U) : ∃ i : ℤ, x ∈ W i := by
    rw [← hWUnion] at hx
    exact mem_iUnion.mp hx
  have hchooseT (z : RoundCylinderSpace) (hz : z ∈ V) : ∃ i : ℤ, z ∈ T i := by
    rw [← hTUnion] at hz
    exact mem_iUnion.mp hz
  let forward : M → RoundCylinderSpace := fun x =>
    if hx : x ∈ U then Pi (Classical.choose (hchooseW x hx)) x else (q0 k, 0)
  let backward : RoundCylinderSpace → M := fun z =>
    if hz : z ∈ V then (Pi (Classical.choose (hchooseT z hz))).symm z
    else (C.neck k).center
  have hforward (i : ℤ) (x : M) (hx : x ∈ W i) : forward x = Pi i x := by
    have hxU := hWsub i hx
    dsimp only [forward]
    rw [dif_pos hxU]
    exact hforwardAgree (Classical.choose (hchooseW x hxU)) i
      ⟨Classical.choose_spec (hchooseW x hxU), hx⟩
  have hbackward (i : ℤ) (z : RoundCylinderSpace) (hz : z ∈ T i) :
      backward z = (Pi i).symm z := by
    have hzV := hTsub i hz
    dsimp only [backward]
    rw [dif_pos hzV]
    exact hinverseAgree (Classical.choose (hchooseT z hzV)) i
      ⟨Classical.choose_spec (hchooseT z hzV), hz⟩
  have hforwardMap : MapsTo forward U V := by
    intro x hx
    obtain ⟨i, hxi⟩ := hchooseW x hx
    rw [hforward i x hxi]
    exact hTsub i ((Pi i).map_source ((hsource i).symm ▸ hxi))
  have hbackwardMap : MapsTo backward V U := by
    intro z hz
    obtain ⟨i, hzi⟩ := hchooseT z hz
    rw [hbackward i z hzi]
    exact hWsub i (hsource i ▸ (Pi i).map_target hzi)
  have hleft (x : M) (hx : x ∈ U) : backward (forward x) = x := by
    obtain ⟨i, hxi⟩ := hchooseW x hx
    have hs : x ∈ (Pi i).source := (hsource i).symm ▸ hxi
    have ht : Pi i x ∈ T i := (Pi i).map_source hs
    rw [hforward i x hxi, hbackward i (Pi i x) ht]
    exact (Pi i).left_inv hs
  have hright (z : RoundCylinderSpace) (hz : z ∈ V) : forward (backward z) = z := by
    obtain ⟨i, hzi⟩ := hchooseT z hz
    have hs : (Pi i).symm z ∈ W i := hsource i ▸ (Pi i).map_target hzi
    rw [hbackward i z hzi, hforward i ((Pi i).symm z) hs]
    exact (Pi i).right_inv hzi
  have hWopen (i : ℤ) : IsOpen (W i) := hsource i ▸ (Pi i).open_source
  have hTopen (i : ℤ) : IsOpen (T i) := (Pi i).open_target
  have hUopen : IsOpen U := by
    rw [← hWUnion]
    exact isOpen_iUnion hWopen
  have hVopen : IsOpen V := by
    rw [← hTUnion]
    exact isOpen_iUnion hTopen
  have hforwardSmooth : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ forward U := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro x hx
    obtain ⟨i, hxi⟩ := hchooseW x hx
    refine ⟨W i, hWopen i, hxi, ?_⟩
    have hs : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (Pi i) (W i) :=
      hsource i ▸ (hLocal i).2.2.1
    exact hs.congr_mono (fun y hy => hforward i y hy.2) inter_subset_right
  have hbackwardSmooth : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ backward V := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro z hz
    obtain ⟨i, hzi⟩ := hchooseT z hz
    refine ⟨T i, hTopen i, hzi, ?_⟩
    have hs : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (Pi i).symm (T i) :=
      (hLocal i).2.2.2
    exact hs.congr_mono (fun y hy => hbackward i y hy.2) inter_subset_right
  let P : OpenPartialHomeomorph M RoundCylinderSpace :=
    { toPartialEquiv :=
        { toFun := forward
          invFun := backward
          source := U
          target := V
          map_source' := fun _ hx => hforwardMap hx
          map_target' := fun _ hz => hbackwardMap hz
          left_inv' := fun x hx => hleft x hx
          right_inv' := fun z hz => hright z hz }
      continuousOn_toFun := hforwardSmooth.continuousOn
      continuousOn_invFun := hbackwardSmooth.continuousOn
      open_source := hUopen
      open_target := hVopen }
  refine ⟨e, F, B, P, hFk, hBk, he, hfirst, hmono, hell, hupper, hbounds,
    rfl, rfl, hforwardSmooth, hbackwardSmooth, ?_⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    exact (hforward i x hx).trans (hforwardFormula i x)
  · intro z hz
    have ht : z ∈ T i := (hTimage i).symm ▸ hz
    exact (hbackward i z ht).trans (hinverseFormula i z)
  · ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      change forward x ∈ Vlocal i
      rw [hforward i x hx]
      exact hTimage i ▸ (Pi i).map_source ((hsource i).symm ▸ hx)
    · intro hz
      have ht : z ∈ T i := (hTimage i).symm ▸ hz
      have hx : (Pi i).symm z ∈ W i := hsource i ▸ (Pi i).map_target ht
      refine ⟨(Pi i).symm z, hx, ?_⟩
      change forward ((Pi i).symm z) = z
      rw [hforward i ((Pi i).symm z) hx]
      exact (Pi i).right_inv ht
  · ext x
    constructor
    · rintro ⟨hx, himage⟩
      change x ∈ U at hx
      change forward x ∈ Vlocal i at himage
      have ht : forward x ∈ T i := (hTimage i).symm ▸ himage
      have hback : backward (forward x) ∈ W i := by
        rw [hbackward i (forward x) ht]
        exact hsource i ▸ (Pi i).map_target ht
      simpa only [hleft x hx] using hback
    · intro hx
      refine ⟨hWsub i hx, ?_⟩
      change forward x ∈ Vlocal i
      rw [hforward i x hx]
      exact hTimage i ▸ (Pi i).map_source ((hsource i).symm ▸ hx)

end PoincareConjecture.BalancedNeckChain
