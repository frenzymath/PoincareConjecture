import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicChartDomains
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.IntrinsicTrimmedCover
import PoincareConjecture.Proofs.M25.AppA_1_Necks.IntrinsicExtendedChainBands
import PoincareConjecture.Proofs.M25.AppA_1_Necks.ChainFiberRecursion
import Mathlib.Data.Int.Init
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Algebra.Order.Archimedean.Defs











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.BalancedNeckChain

open Classical in


theorem exists_intrinsic_trimmed_chain_image_atlas :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) {a0 b0 : ℤ}
        (_ : C.shape = ChainShape.finite a0 b0), epsilon ≤ epsilon0 →
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
        connectedComponentIn (U \ S i t)
          ((C.neck i).coordinate_map (q0 i, (t - L) / 2))
      let posSide : ℤ → ℝ → Set M := fun i t =>
        connectedComponentIn (U \ S i t)
          ((C.neck i).coordinate_map (q0 i, (t + L) / 2))
      let W : ℤ → Set M := fun i => if i ∈ C.shape.active then
        ((C.neck i).carrier ∩
          (if i - 1 ∈ C.shape.active then posSide (i - 1) a else univ)) ∩
          (if i + 1 ∈ C.shape.active then negSide i b else univ) else ∅
      ∃ (e : ℤ → OpenPartialHomeomorph RoundCylinderSpace M)
        (F : ℤ → Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
          ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞)
        (B : ℤ → Diffeomorph (𝓡 2) (𝓡 2)
          UnitTwoSphere UnitTwoSphere ∞),
      let alpha : ℤ → UnitTwoSphere → ℝ := fun i r =>
        (F i ((B i).symm r, a)).2
      let beta : ℤ → UnitTwoSphere → ℝ := fun i r =>
        (F i ((B i).symm r, b)).2
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
      let lo : ℤ → UnitTwoSphere → ℝ := fun i r =>
        if i - 1 ∈ C.shape.active then alpha (i - 1) r else ell r
      let hi : ℤ → UnitTwoSphere → ℝ := fun i r =>
        if i + 1 ∈ C.shape.active then beta i r else upper r
      let Vlocal : ℤ → Set RoundCylinderSpace := fun i =>
        if i ∈ C.shape.active then {z | lo i z.1 < z.2 ∧ z.2 < hi i z.1} else ∅
      let V : Set RoundCylinderSpace := match C.shape with
        | .finite _ _ => {z | ell z.1 < z.2 ∧ z.2 < upper z.1}
        | .forward _ => {z | ell z.1 < z.2}
        | .backward _ => {z | z.2 < upper z.1}
        | .biInfinite => univ
      let P : ℤ → OpenPartialHomeomorph M RoundCylinderSpace := fun i =>
        ((e i).symm.restr (W i)).trans (F i).toHomeomorph.toOpenPartialHomeomorph
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
      (∀ i : ℤ, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (alpha i) ∧
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (beta i)) ∧
      (∀ i : ℤ, (P i).source = W i ∧ (P i).target = Vlocal i ∧
        ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (P i) (P i).source ∧
        ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (P i).symm (P i).target) ∧
      (⋃ i : ℤ, W i) = U ∧ (⋃ i : ℤ, Vlocal i) = V ∧
      (∀ i ∈ C.shape.active, ∀ r : UnitTwoSphere, alpha i r < beta i r) ∧
      (∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, i < j →
        ∀ r : UnitTwoSphere, beta i r < alpha j r) ∧
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active →
        W i ∩ W (i + 1) = (C.neck i).region a b ∧
        Vlocal i ∩ Vlocal (i + 1) = {z | alpha i z.1 < z.2 ∧ z.2 < beta i z.1}) ∧
      (∀ i ∈ C.shape.active, ∀ j ∈ C.shape.active, i + 1 < j →
        Disjoint (W i) (W j) ∧ Disjoint (Vlocal i) (Vlocal j)) ∧
      (∀ i ∈ C.shape.active, k ≤ i → ∀ r : UnitTwoSphere,
        a + ((i - k : ℤ) : ℝ) * (9 * L / 32) ≤ alpha i r) ∧
      (∀ i ∈ C.shape.active, i + 1 ∈ C.shape.active → i + 1 ≤ k →
        ∀ r : UnitTwoSphere,
          beta i r < L / 2 - ((k - i - 1 : ℤ) : ℝ) * (3 * L / 16)) ∧
      (∀ i j : ℤ,
        EqOn (P i) (P j) (W i ∩ W j) ∧
        EqOn (P i).symm (P j).symm (Vlocal i ∩ Vlocal j)) := by
  classical
  obtain ⟨epsilon1, he1, hc1, hcharts⟩ := exists_intrinsic_extended_chain_band_atlas.{u}
  obtain ⟨epsilon2, he2, _, hheights⟩ := exists_finite_relative_saturated_heights.{u}
  refine ⟨min epsilon1 epsilon2, lt_min he1 he2, (min_le_left _ _).trans hc1, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C a0 b0 hshape hepsilon k hk
  let L := epsilon⁻¹
  let U : Set M := ⋃ i ∈ C.shape.active, (C.neck i).carrier
  let a := 23 * L / 32
  let b := 25 * L / 32
  have hL : 0 < L := inv_pos.mpr (C.epsilon_eq k hk ▸ (C.neck k).epsilon_pos)
  have ha : L / 2 < a := by dsimp [a]; linarith
  have hab : a < b := by dsimp [a, b]; linarith
  have hb : b < L := by dsimp [b]; linarith
  let q0 : ℤ → UnitTwoSphere := fun i =>
    ((C.neck i).coordinate_inverse (C.neck i).center).1
  let S : ℤ → ℝ → Set M := fun i t =>
    range (fun q : UnitTwoSphere => (C.neck i).coordinate_map (q, t))
  let negSide : ℤ → ℝ → Set M := fun i t => connectedComponentIn (U \ S i t)
    ((C.neck i).coordinate_map (q0 i, (t - L) / 2))
  let posSide : ℤ → ℝ → Set M := fun i t => connectedComponentIn (U \ S i t)
    ((C.neck i).coordinate_map (q0 i, (t + L) / 2))
  let W : ℤ → Set M := fun i => if i ∈ C.shape.active then
    ((C.neck i).carrier ∩
      (if i - 1 ∈ C.shape.active then posSide (i - 1) a else univ)) ∩
      (if i + 1 ∈ C.shape.active then negSide i b else univ) else ∅
  obtain ⟨e, A, D, m, p, he, hDfirst, hDmono, hshift, hDlo, hDhi, hband⟩ :=
    hcharts C (hepsilon.trans (min_le_left _ _))
  obtain ⟨F, B, c, hFk, hBk, hrec, hfirst, hmono, _, hupper, hlower⟩ :=
    PoincareConjecture.exists_integer_cylinder_cocycle hL A D m p hDfirst hDmono
      hshift hDlo hDhi k
  obtain ⟨H, hH⟩ := hheights C hshape (hepsilon.trans (min_le_right _ _))
  obtain ⟨W', hWoff, hWon, hWopen, _, hWU, hWadj, hWfar, _⟩ :=
    C.intrinsic_trimmed_cut_cover hshape H hH a b ha hab hb
  have hWW : W' = W := by
    funext i
    by_cases hi : i ∈ C.shape.active
    · simpa only [W, if_pos hi] using hWon i hi
    · simpa only [W, if_neg hi] using hWoff i hi
  rw [hWW] at hWopen hWU hWadj hWfar
  have hWsub (i : ℤ) : W i ⊆ (e i).target := by
    by_cases hi : i ∈ C.shape.active
    · rw [(he i hi).2.1]
      intro x hx
      simp only [W, if_pos hi] at hx
      exact hx.1.1
    · simp [W, hi]
  have hbetween {i j n : ℤ} (hi : i ∈ C.shape.active) (hj : j ∈ C.shape.active)
      (hin : i ≤ n) (hnj : n ≤ j) : n ∈ C.shape.active := by
    cases hs : C.shape <;>
      simp only [hs, ChainShape.active, mem_Icc, mem_Ici, mem_Iic, mem_univ] at * <;> omega
  let graph : ℤ → UnitTwoSphere → ℝ := fun i q =>
    (D (i - 1) ((A (i - 1)).symm q, a)).2
  let vlo : ℤ → UnitTwoSphere → ℝ := fun i q =>
    if i - 1 ∈ C.shape.active then graph i q else -L
  let vhi : ℤ → ℝ := fun i => if i + 1 ∈ C.shape.active then b else L
  let Q : ℤ → Set RoundCylinderSpace := fun i => {z | vlo i z.1 < z.2 ∧ z.2 < vhi i}
  have hC7 := C.intrinsic_trimmed_chart_domains hshape H hH e A D
    (fun i hi => ⟨(he i hi).1, (he i hi).2.1, (he i hi).2.2.2.2.1⟩)
    hDfirst (fun i hi hn q => hband i hi hn (q, a) ⟨le_rfl, hab.le⟩)
  change (∀ i, ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (graph i)) ∧
    (∀ i ∈ C.shape.active, i - 1 ∈ C.shape.active →
      (∀ q, graph i q ∈ Ioo (-L) (L / 2)) ∧
      S (i - 1) a = range (fun q => e i (q, graph i q))) ∧
    (∀ i ∈ C.shape.active, (e i).symm '' W i = Q i ∧
      (e i).source ∩ (e i) ⁻¹' W i = Q i ∧ Q i ⊆ (e i).source ∧
      (∀ q, vlo i q < 3 * L / 4 ∧ 3 * L / 4 < vhi i) ∧
      (∀ q, e i (q, 3 * L / 4) ∈ W i)) at hC7
  obtain ⟨_, hgraph, hQ⟩ := hC7
  let q : ℤ → UnitTwoSphere → UnitTwoSphere := fun i r => (B i).symm r
  let T : ℤ → UnitTwoSphere → ℝ → ℝ := fun i r t => (F i (q i r, t)).2
  let alpha := fun i r => T i r a
  let beta := fun i r => T i r b
  let ell := fun r => match C.shape with
    | .finite first _ => T first r (-L)
    | .forward first => T first r (-L)
    | .backward _ => -L
    | .biInfinite => -L
  let upper := fun r => match C.shape with
    | .finite _ last => T last r L
    | .forward _ => L
    | .backward last => T last r L
    | .biInfinite => L
  let lo := fun i r => if i - 1 ∈ C.shape.active then alpha (i - 1) r else ell r
  let hi := fun i r => if i + 1 ∈ C.shape.active then beta i r else upper r
  let Vlocal : ℤ → Set RoundCylinderSpace := fun i =>
    if i ∈ C.shape.active then {z | lo i z.1 < z.2 ∧ z.2 < hi i z.1} else ∅
  let V : Set RoundCylinderSpace := match C.shape with
    | .finite _ _ => {z | ell z.1 < z.2 ∧ z.2 < upper z.1}
    | .forward _ => {z | ell z.1 < z.2}
    | .backward _ => {z | z.2 < upper z.1}
    | .biInfinite => univ
  let P := fun i => ((e i).symm.restr (W i)).trans
    (F i).toHomeomorph.toOpenPartialHomeomorph
  have hFrec (i : ℤ) (z : RoundCylinderSpace) : F i z = F (i + 1) (D i z) := by
    rw [(hrec i).1]; rfl
  have hbase (i : ℤ) (r : UnitTwoSphere) : A i (q i r) = q (i + 1) r := by
    apply (B (i + 1)).injective
    change ((A i).trans (B (i + 1))) ((B i).symm r) = B (i + 1) ((B (i + 1)).symm r)
    rw [← (hrec i).2, Diffeomorph.apply_symm_apply, Diffeomorph.apply_symm_apply]
  have hstepT (i : ℤ) (r : UnitTwoSphere) (t : ℝ) :
      T i r t = T (i + 1) r (D i (q i r, t)).2 := by
    have hpair : D i (q i r, t) = (q (i + 1) r, (D i (q i r, t)).2) :=
      Prod.ext ((hDfirst i (q i r, t)).trans (hbase i r)) rfl
    change (F i (q i r, t)).2 = _
    rw [hFrec, hpair]
  have hTi (i : ℤ) (z : RoundCylinderSpace) : T i z.1 ((F i).symm z).2 = z.2 := by
    have hp : (F i).symm z = (q i z.1, ((F i).symm z).2) :=
      Prod.ext (hfirst i z).2 rfl
    change (F i (q i z.1, ((F i).symm z).2)).2 = z.2
    rw [← hp, Diffeomorph.apply_symm_apply]
  have hTsmooth (i : ℤ) (t : ℝ) : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (T i · t) :=
    contMDiff_snd.comp ((F i).contMDiff.comp
      ((B i).symm.contMDiff.prodMk contMDiff_const))
  have hleftend (i : ℤ) (hi : i ∈ C.shape.active) (hp : i - 1 ∉ C.shape.active) :
      ∀ r, ell r = T i r (-L) := by
    cases hs : C.shape with
    | finite first last =>
      have hi' : i = first := by simp only [hs, ChainShape.active, mem_Icc] at hi hp; omega
      subst i; intro r; simp [ell, hs]
    | forward first =>
      have hi' : i = first := by simp only [hs, ChainShape.active, mem_Ici] at hi hp; omega
      subst i; intro r; simp [ell, hs]
    | backward last => simp only [hs, ChainShape.active, mem_Iic] at hi hp; omega
    | biInfinite => exact (hp (by simp [hs, ChainShape.active])).elim
  have hrightend (i : ℤ) (hi : i ∈ C.shape.active) (hn : i + 1 ∉ C.shape.active) :
      ∀ r, upper r = T i r L := by
    cases hs : C.shape with
    | finite first last =>
      have hi' : i = last := by simp only [hs, ChainShape.active, mem_Icc] at hi hn; omega
      subst i; intro r; simp [upper, hs]
    | forward first => simp only [hs, ChainShape.active, mem_Ici] at hi hn; omega
    | backward last =>
      have hi' : i = last := by simp only [hs, ChainShape.active, mem_Iic] at hi hn; omega
      subst i; intro r; simp [upper, hs]
    | biInfinite => exact (hn (by simp [hs, ChainShape.active])).elim
  have hloeq (i : ℤ) (hi : i ∈ C.shape.active) (r : UnitTwoSphere) :
      T i r (vlo i (q i r)) = lo i r := by
    by_cases hp : i - 1 ∈ C.shape.active
    · have hq : (A (i - 1)).symm (q i r) = q (i - 1) r := by
        apply (A (i - 1)).injective
        change A (i - 1) ((A (i - 1)).symm (q i r)) = A (i - 1) (q (i - 1) r)
        rw [Diffeomorph.apply_symm_apply]
        simpa only [sub_add_cancel] using (hbase (i - 1) r).symm
      simpa only [vlo, lo, if_pos hp, graph, hq, sub_add_cancel, alpha] using
        (hstepT (i - 1) r a).symm
    · simpa only [vlo, lo, if_neg hp] using (hleftend i hi hp r).symm
  have hhieq (i : ℤ) (hai : i ∈ C.shape.active) (r : UnitTwoSphere) :
      T i r (vhi i) = hi i r := by
    by_cases hn : i + 1 ∈ C.shape.active
    · simp only [vhi, hi, if_pos hn, beta]
    · simpa only [vhi, hi, if_neg hn] using (hrightend i hai hn r).symm
  have habpoint (i : ℤ) (r : UnitTwoSphere) : alpha i r < beta i r := hmono i (q i r) hab
  have hloalpha (i : ℤ) (hai : i ∈ C.shape.active) (r : UnitTwoSphere) :
      lo i r < alpha i r := by
    rw [← hloeq i hai r]
    apply hmono i (q i r)
    by_cases hp : i - 1 ∈ C.shape.active
    · have hg := (hgraph i hai hp).1 (q i r)
      simp only [vlo, if_pos hp]; linarith [hg.2]
    · simp only [vlo, if_neg hp]; linarith
  have hbetahi (i : ℤ) (hai : i ∈ C.shape.active) (r : UnitTwoSphere) :
      beta i r ≤ hi i r := by
    rw [← hhieq i hai r]
    apply (hmono i (q i r)).monotone
    dsimp only [vhi]
    split_ifs <;> linarith
  have hnext (i : ℤ) (hai : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active)
      (r : UnitTwoSphere) : beta i r < alpha (i + 1) r := by
    have hd := (hband i hai hn (q i r, b) ⟨hab.le, le_rfl⟩).1.2.2
    rw [show beta i r = T (i + 1) r (D i (q i r, b)).2 from hstepT i r b]
    exact hmono (i + 1) (q (i + 1) r) (by linarith)
  have horder (i : ℤ) (hai : i ∈ C.shape.active) (j : ℤ)
      (haj : j ∈ C.shape.active) (hij : i < j) (r : UnitTwoSphere) :
      beta i r < alpha j r := by
    have hh : ∀ n, i + 1 ≤ n → n ∈ C.shape.active → beta i r < alpha n r :=
      Int.leInduction (motive := fun n _ => n ∈ C.shape.active → beta i r < alpha n r)
        (fun hn => hnext i hai hn r) (fun n hin ih hn => by
          have hn' : n ∈ C.shape.active := hbetween hai hn (by omega) (by omega)
          exact (ih hn').trans ((habpoint n r).trans (hnext n hn' hn r)))
    exact hh j (by omega) haj
  have hVmem (i : ℤ) (z : RoundCylinderSpace) : z ∈ Vlocal i ↔
      i ∈ C.shape.active ∧ lo i z.1 < z.2 ∧ z.2 < hi i z.1 := by
    by_cases hai : i ∈ C.shape.active <;> simp [Vlocal, hai]
  have hQiff (i : ℤ) (hai : i ∈ C.shape.active) (z : RoundCylinderSpace) :
      (F i).symm z ∈ Q i ↔ z ∈ Vlocal i := by
    have hl : lo i z.1 < z.2 ↔ vlo i (q i z.1) < ((F i).symm z).2 := by
      calc
        _ ↔ T i z.1 (vlo i (q i z.1)) < T i z.1 ((F i).symm z).2 := by
          rw [hloeq i hai z.1, hTi i z]
        _ ↔ _ := (hmono i (q i z.1)).lt_iff_lt
    have hu : z.2 < hi i z.1 ↔ ((F i).symm z).2 < vhi i := by
      calc
        _ ↔ T i z.1 ((F i).symm z).2 < T i z.1 (vhi i) := by
          rw [hhieq i hai z.1, hTi i z]
        _ ↔ _ := (hmono i (q i z.1)).lt_iff_lt
    simpa only [Q, mem_ofPred_eq, (hfirst i z).2, hVmem, true_and, hai] using
      (and_congr hl hu).symm
  have hVimage (i : ℤ) : F i '' ((e i).symm '' W i) = Vlocal i := by
    by_cases hai : i ∈ C.shape.active
    · rw [(hQ i hai).1]
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact (hQiff i hai _).mp (by simpa only [Diffeomorph.symm_apply_apply] using hw)
      · intro hz
        exact ⟨(F i).symm z, (hQiff i hai z).mpr hz, (F i).apply_symm_apply z⟩
    · simp [W, Vlocal, hai]
  have hPsource (i : ℤ) : (P i).source = W i := by
    change (((e i).symm.restr (W i)).trans
      (F i).toHomeomorph.toOpenPartialHomeomorph).source = _
    rw [OpenPartialHomeomorph.trans_source,
      (e i).symm.restr_source' (W i) (hWopen i)]
    change ((e i).target ∩ W i) ∩ (e i).symm ⁻¹' univ = W i
    rw [preimage_univ, inter_univ, inter_eq_right.mpr (hWsub i)]
  have hPtarget (i : ℤ) : (P i).target = Vlocal i := by
    rw [← (P i).image_source_eq_target, hPsource]
    change (fun x => F i ((e i).symm x)) '' W i = _
    rw [← image_image]
    exact hVimage i
  have hPsmooth (i : ℤ) :
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (P i) (P i).source ∧
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (P i).symm (P i).target := by
    by_cases hai : i ∈ C.shape.active
    · constructor
      · rw [hPsource]
        exact (F i).contMDiff.comp_contMDiffOn
          ((he i hai).2.2.2.1.mono (by simpa only [← (he i hai).2.1] using hWsub i))
      · rw [hPtarget]
        apply (he i hai).2.2.1.comp (F i).symm.contMDiff.contMDiffOn
        intro z hz
        have hq := (hQiff i hai z).mpr hz
        change (F i).symm z ∈ univ ×ˢ Ioo (-L) L
        simpa only [(he i hai).1] using (hQ i hai).2.2.1 hq
    · have hw : W i = ∅ := by simp [W, hai]
      have hv : Vlocal i = ∅ := by simp [Vlocal, hai]
      rw [hPsource, hPtarget, hw, hv]
      exact ⟨contMDiffOn_empty, contMDiffOn_empty⟩
  have hpositive (i : ℤ) (hki : k ≤ i) (r : UnitTwoSphere) :
      a + ((i - k : ℤ) : ℝ) * (9 * L / 32) ≤ alpha i r := by
    have ht := (hupper i hki).1 (q i r) a (by dsimp [a]; linarith)
    have hc := (hupper i hki).2 (q i r)
    change _ ≤ (F i (q i r, a)).2
    rw [ht]
    simpa only [add_comm] using add_le_add_left hc a
  have hnegative (i : ℤ) (hai : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active)
      (hik : i + 1 ≤ k) (r : UnitTwoSphere) :
      beta i r < L / 2 - ((k - i - 1 : ℤ) : ℝ) * (3 * L / 16) := by
    have hd := (hband i hai hn (q i r, b) ⟨hab.le, le_rfl⟩).1.2.2
    have ht := (hlower (i + 1) hik).1 (q (i + 1) r) (D i (q i r, b)).2 (by linarith)
    have hc := (hlower (i + 1) hik).2 (q (i + 1) r)
    rw [show beta i r = T (i + 1) r (D i (q i r, b)).2 from hstepT i r b]
    change (F (i + 1) (q (i + 1) r, (D i (q i r, b)).2)).2 < _
    rw [ht]
    have heq : k - (i + 1) = k - i - 1 := by omega
    rw [heq] at hc
    linarith
  have hlowbase (i : ℤ) (hik : i ≤ k) (r : UnitTwoSphere) : T i r (-L) ≤ -L := by
    have hc := (hlower i hik).2 (q i r)
    have hn : 0 ≤ ((k - i : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hik
    have ht := (hlower i hik).1 (q i r) (-L) (by linarith)
    change (F i (q i r, -L)).2 ≤ _
    rw [ht]; nlinarith
  have huppbase (i : ℤ) (hki : k ≤ i) (r : UnitTwoSphere) : L ≤ T i r L := by
    have hc := (hupper i hki).2 (q i r)
    have hn : 0 ≤ ((i - k : ℤ) : ℝ) := by exact_mod_cast sub_nonneg.mpr hki
    have ht := (hupper i hki).1 (q i r) L (by linarith)
    change _ ≤ (F i (q i r, L)).2
    rw [ht]; nlinarith
  have hends : (∀ r, ell r ≤ -L ∧ L ≤ upper r) := by
    intro r
    cases hs : C.shape with
    | finite first last =>
      have hh : first ≤ k ∧ k ≤ last := by simpa only [hs, ChainShape.active, mem_Icc] using hk
      exact ⟨by simpa [ell, hs] using hlowbase first hh.1 r,
        by simpa [upper, hs] using huppbase last hh.2 r⟩
    | forward first =>
      have hh : first ≤ k := by simpa only [hs, ChainShape.active, mem_Ici] using hk
      exact ⟨by simpa [ell, hs] using hlowbase first hh r, by simp [upper, hs]⟩
    | backward last =>
      have hh : k ≤ last := by simpa only [hs, ChainShape.active, mem_Iic] using hk
      exact ⟨by simp [ell, hs], by simpa [upper, hs] using huppbase last hh r⟩
    | biInfinite => simp [ell, upper, hs]
  have hellsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ ell := by
    cases hs : C.shape <;> simp only [ell, hs] <;>
      first | exact hTsmooth _ _ | exact contMDiff_const
  have huppersmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ upper := by
    cases hs : C.shape <;> simp only [upper, hs] <;>
      first | exact hTsmooth _ _ | exact contMDiff_const
  have hVadj (i : ℤ) (hai : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active) :
      Vlocal i ∩ Vlocal (i + 1) = {z | alpha i z.1 < z.2 ∧ z.2 < beta i z.1} := by
    ext z
    have hleft := hloalpha i hai z.1
    have hright := (hnext i hai hn z.1).trans_le
      ((habpoint (i + 1) z.1).le.trans (hbetahi (i + 1) hn z.1))
    simp only [mem_inter_iff, hVmem, hai, hn, true_and, hi, if_pos hn,
      lo, add_sub_cancel_right, mem_ofPred_eq] at *
    constructor
    · intro hz; exact ⟨hz.2.1, hz.1.2⟩
    · intro hz; exact ⟨⟨hleft.trans hz.1, hz.2⟩, hz.1, hz.2.trans hright⟩
  have hVfar (i : ℤ) (hai : i ∈ C.shape.active) (j : ℤ)
      (haj : j ∈ C.shape.active) (hij : i + 1 < j) : Disjoint (Vlocal i) (Vlocal j) := by
    have hn := hbetween hai haj (by omega : i ≤ i + 1) (by omega)
    have hp := hbetween hai haj (by omega : i ≤ j - 1) (by omega)
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hl := (hVmem i z).mp hzi
    have hr := (hVmem j z).mp hzj
    have ho := horder i hai (j - 1) hp (by omega) z.1
    simp only [hi, if_pos hn] at hl
    simp only [lo, if_pos hp] at hr
    exact (lt_irrefl z.2) (hl.2.2.trans (ho.trans hr.2.1))
  have hblock (m : ℤ) (hm : m ∈ C.shape.active) :
      ∀ n, m ≤ n → n ∈ C.shape.active → ∀ r t,
        lo m r < t → t < hi n r → ∃ i ∈ C.shape.active, lo i r < t ∧ t < hi i r := by
    apply Int.leInduction (motive := fun n _ => n ∈ C.shape.active → ∀ r t,
      lo m r < t → t < hi n r → ∃ i ∈ C.shape.active, lo i r < t ∧ t < hi i r)
    · intro _ r t hl hu; exact ⟨m, hm, hl, hu⟩
    · intro n hmn ih hn r t hl hu
      have hn' := hbetween hm hn hmn (by omega)
      by_cases ht : t < beta n r
      · exact ih hn' r t hl (by simpa only [hi, if_pos hn] using ht)
      · refine ⟨n + 1, hn, ?_, hu⟩
        simpa only [lo, add_sub_cancel_right, if_pos hn'] using
          (habpoint n r).trans_le (le_of_not_gt ht)
  have hfirstbound (first : ℤ) (hf : first ∈ C.shape.active)
      (hmin : ∀ i ∈ C.shape.active, first ≤ i)
      (heq : ∀ r, ell r = T first r (-L)) :
      ∀ i ∈ C.shape.active, ∀ r, ell r ≤ lo i r := by
    intro i hai r
    by_cases hp : i - 1 ∈ C.shape.active
    · simp only [lo, if_pos hp]
      have hb0 : ell r < alpha first r := by rw [heq r]; exact hmono first (q first r) (by linarith)
      have hle := hmin (i - 1) hp
      rcases hle.eq_or_lt with heq' | hlt
      · simpa only [← heq'] using hb0.le
      · exact (hb0.trans ((habpoint first r).trans (horder first hf (i - 1) hp hlt r))).le
    · simp only [lo, if_neg hp, le_refl]
  have hlastbound (last : ℤ) (hl : last ∈ C.shape.active)
      (hmax : ∀ i ∈ C.shape.active, i ≤ last)
      (heq : ∀ r, upper r = T last r L) :
      ∀ i ∈ C.shape.active, ∀ r, hi i r ≤ upper r := by
    intro i hai r
    by_cases hn : i + 1 ∈ C.shape.active
    · simp only [hi, if_pos hn]
      have hb0 : beta last r < upper r := by rw [heq r]; exact hmono last (q last r) hb
      rcases (hmax i hai).eq_or_lt with heq' | hlt
      · simpa only [heq'] using hb0.le
      · exact ((horder i hai last hl hlt r).trans ((habpoint last r).trans hb0)).le
    · simp only [hi, if_neg hn, le_refl]
  have hrightescape (hact : ∀ n : ℤ, k ≤ n → n ∈ C.shape.active) (r : UnitTwoSphere) (t : ℝ) :
      ∃ n, k ≤ n ∧ n ∈ C.shape.active ∧ t < hi n r := by
    have hd : 0 < 9 * L / 32 := by positivity
    obtain ⟨n, hn⟩ := exists_int_gt (max (k : ℝ) ((t - a) / (9 * L / 32) + k))
    have hkn : k ≤ n := by exact_mod_cast (le_max_left _ _).trans hn.le
    have hfrac : (t - a) / (9 * L / 32) < (n : ℝ) - k := by
      linarith [lt_of_le_of_lt (le_max_right _ _) hn]
    have hmul := (div_lt_iff₀ hd).mp hfrac
    have he := hpositive n hkn r
    push_cast at he
    refine ⟨n, hkn, hact n hkn, ?_⟩
    exact (show t < alpha n r by nlinarith).trans_le
      ((habpoint n r).le.trans (hbetahi n (hact n hkn) r))
  have hleftescape (hact : ∀ n : ℤ, n ≤ k → n ∈ C.shape.active) (r : UnitTwoSphere) (t : ℝ) :
      ∃ m, m ≤ k ∧ m ∈ C.shape.active ∧ lo m r < t := by
    have hd : 0 < 3 * L / 16 := by positivity
    obtain ⟨m, hm⟩ := exists_int_lt (min (k : ℝ) ((t - L / 2) / (3 * L / 16) + k))
    have hmk : m ≤ k := by exact_mod_cast hm.le.trans (min_le_left _ _)
    have hfrac : (m : ℝ) - k < (t - L / 2) / (3 * L / 16) := by
      linarith [lt_of_lt_of_le hm (min_le_right _ _)]
    have hmul := (lt_div_iff₀ hd).mp hfrac
    have hma := hact m hmk
    have hpa := hact (m - 1) (by omega)
    have he := hnegative (m - 1) hpa (by simpa only [sub_add_cancel] using hma)
      (by omega) r
    push_cast at he
    refine ⟨m, hmk, hma, ?_⟩
    simp only [lo, if_pos hpa]
    exact (habpoint (m - 1) r).trans (by nlinarith)
  have hVunion : (⋃ i : ℤ, Vlocal i) = V := by
    ext z
    simp only [mem_iUnion, hVmem]
    cases hs : C.shape with
    | finite first last =>
      have hh : first ≤ k ∧ k ≤ last := by simpa only [hs, ChainShape.active, mem_Icc] using hk
      have hf : first ∈ C.shape.active := by simp only [hs, ChainShape.active, mem_Icc]; omega
      have hl : last ∈ C.shape.active := by simp only [hs, ChainShape.active, mem_Icc]; omega
      have hp : first - 1 ∉ C.shape.active := by simp only [hs, ChainShape.active, mem_Icc]; omega
      have hn : last + 1 ∉ C.shape.active := by simp only [hs, ChainShape.active, mem_Icc]; omega
      have hfb := hfirstbound first hf (by
        intro i hi; simp only [hs, ChainShape.active, mem_Icc] at hi; exact hi.1)
        (by intro r; simp [ell, hs])
      have hlb := hlastbound last hl (by
        intro i hi; simp only [hs, ChainShape.active, mem_Icc] at hi; exact hi.2)
        (by intro r; simp [upper, hs])
      simp only [V, hs, mem_ofPred_eq]
      rw [← hs]
      constructor
      · rintro ⟨i, hi, hzi, hiz⟩
        exact ⟨(hfb i hi z.1).trans_lt hzi, hiz.trans_le (hlb i hi z.1)⟩
      · intro hz
        exact hblock first hf last (by omega) hl z.1 z.2
          (by simpa only [lo, if_neg hp] using hz.1)
          (by simpa only [hi, if_neg hn] using hz.2)
    | forward first =>
      have hh : first ≤ k := by simpa only [hs, ChainShape.active, mem_Ici] using hk
      have hf : first ∈ C.shape.active := by simp [hs, ChainShape.active]
      have hp : first - 1 ∉ C.shape.active := by simp [hs, ChainShape.active]
      have hfb := hfirstbound first hf (by
        intro i hi; simpa only [hs, ChainShape.active, mem_Ici] using hi)
        (by intro r; simp [ell, hs])
      have hact : ∀ n : ℤ, k ≤ n → n ∈ C.shape.active := by
        intro n hn; simpa only [hs, ChainShape.active, mem_Ici] using hh.trans hn
      simp only [V, hs, mem_ofPred_eq]
      rw [← hs]
      constructor
      · rintro ⟨i, hi, hzi, _⟩; exact (hfb i hi z.1).trans_lt hzi
      · intro hz
        obtain ⟨n, hkn, hn, hzn⟩ := hrightescape hact z.1 z.2
        exact hblock first hf n (hh.trans hkn) hn z.1 z.2
          (by simpa only [lo, if_neg hp] using hz) hzn
    | backward last =>
      have hh : k ≤ last := by simpa only [hs, ChainShape.active, mem_Iic] using hk
      have hl : last ∈ C.shape.active := by simp [hs, ChainShape.active]
      have hn : last + 1 ∉ C.shape.active := by simp [hs, ChainShape.active]
      have hlb := hlastbound last hl (by
        intro i hi; simpa only [hs, ChainShape.active, mem_Iic] using hi)
        (by intro r; simp [upper, hs])
      have hact : ∀ n : ℤ, n ≤ k → n ∈ C.shape.active := by
        intro n hn; simpa only [hs, ChainShape.active, mem_Iic] using hn.trans hh
      simp only [V, hs, mem_ofPred_eq]
      rw [← hs]
      constructor
      · rintro ⟨i, hi, _, hiz⟩; exact hiz.trans_le (hlb i hi z.1)
      · intro hz
        obtain ⟨m, hmk, hm, hmz⟩ := hleftescape hact z.1 z.2
        exact hblock m hm last (hmk.trans hh) hl z.1 z.2 hmz
          (by simpa only [hi, if_neg hn] using hz)
    | biInfinite =>
      have hact : ∀ n : ℤ, n ∈ C.shape.active := by intro n; simp [hs, ChainShape.active]
      simp only [V, hs, mem_univ, iff_true]
      rw [← hs]
      obtain ⟨m, hmk, hm, hmz⟩ := hleftescape (fun n _ => hact n) z.1 z.2
      obtain ⟨n, hkn, hn, hzn⟩ := hrightescape (fun n _ => hact n) z.1 z.2
      exact hblock m hm n (hmk.trans hkn) hn z.1 z.2 hmz hzn
  have hagreeNext (i : ℤ) (hai : i ∈ C.shape.active) (hn : i + 1 ∈ C.shape.active) :
      EqOn (P i) (P (i + 1)) (W i ∩ W (i + 1)) ∧
      EqOn (P i).symm (P (i + 1)).symm (Vlocal i ∩ Vlocal (i + 1)) := by
    constructor
    · intro x hx
      have hxreg : x ∈ (C.neck i).region a b := hWadj i hai hn ▸ hx
      have hxc : x ∈ (e i).target := hWsub i hx.1
      have hz : ((e i).symm x).2 ∈ Icc a b := by
        rw [(he i hai).2.2.2.2.2.1 x hxreg.1]
        exact ⟨hxreg.2.1.le, hxreg.2.2.le⟩
      have hd := (hband i hai hn ((e i).symm x) hz).2.1
      rw [(e i).right_inv hxc] at hd
      change F i ((e i).symm x) = F (i + 1) ((e (i + 1)).symm x)
      rw [hFrec, hd]
    · intro z hz
      have hz' : alpha i z.1 < z.2 ∧ z.2 < beta i z.1 := by
        change z ∈ {z | alpha i z.1 < z.2 ∧ z.2 < beta i z.1}
        rw [← hVadj i hai hn]
        exact hz
      have ha' : a < ((F i).symm z).2 := by
        apply (hmono i (q i z.1)).lt_iff_lt.mp
        simpa only [← hTi i z] using hz'.1
      have hb' : ((F i).symm z).2 < b := by
        apply (hmono i (q i z.1)).lt_iff_lt.mp
        simpa only [← hTi i z] using hz'.2
      have hd := (hband i hai hn ((F i).symm z) ⟨ha'.le, hb'.le⟩).2.2
      have hf : (F (i + 1)).symm z = D i ((F i).symm z) := by
        apply (F (i + 1)).injective
        change F (i + 1) ((F (i + 1)).symm z) = F (i + 1) (D i ((F i).symm z))
        rw [Diffeomorph.apply_symm_apply, ← hFrec, Diffeomorph.apply_symm_apply]
      change e i ((F i).symm z) = e (i + 1) ((F (i + 1)).symm z)
      rw [hf]
      exact hd.symm
  have hagreeLe (i j : ℤ) (hij : i ≤ j) :
      EqOn (P i) (P j) (W i ∩ W j) ∧
      EqOn (P i).symm (P j).symm (Vlocal i ∩ Vlocal j) := by
    by_cases hai : i ∈ C.shape.active
    · by_cases haj : j ∈ C.shape.active
      · by_cases heq : i = j
        · subst j; exact ⟨fun _ _ => rfl, fun _ _ => rfl⟩
        · by_cases hnext : j = i + 1
          · subst j; exact hagreeNext i hai haj
          · have hfar : i + 1 < j := by omega
            exact ⟨fun x hx => ((Set.disjoint_left.mp (hWfar i hai j haj hfar)) hx.1 hx.2).elim,
              fun z hz => ((Set.disjoint_left.mp (hVfar i hai j haj hfar)) hz.1 hz.2).elim⟩
      · have hw : W j = ∅ := by simp [W, haj]
        have hv : Vlocal j = ∅ := by simp [Vlocal, haj]
        exact ⟨fun _ hx => (hw ▸ hx.2).elim, fun _ hz => (hv ▸ hz.2).elim⟩
    · have hw : W i = ∅ := by simp [W, hai]
      have hv : Vlocal i = ∅ := by simp [Vlocal, hai]
      exact ⟨fun _ hx => (hw ▸ hx.1).elim, fun _ hz => (hv ▸ hz.1).elim⟩
  refine ⟨e, F, B, hFk, hBk, ?_, hfirst, hmono, hellsmooth, huppersmooth, hends,
    fun i => ⟨hTsmooth i a, hTsmooth i b⟩,
    fun i => ⟨hPsource i, hPtarget i, hPsmooth i⟩, hWU, hVunion,
    fun i _ r => habpoint i r, horder, ?_, ?_, fun i _ => hpositive i,
    hnegative, ?_⟩
  · intro i hai
    obtain ⟨hes, het, hesm, heism, heh, _, hlo, _⟩ := he i hai
    refine ⟨hes, het, by simpa only [hes] using hesm,
      by simpa only [het] using heism, ?_, ?_, (hQ i hai).2.2.2.2⟩
    · intro z hz; exact heh z (hes ▸ hz)
    · intro v; exact hlo (v, 0) ⟨mem_univ _, by linarith, hL⟩ (by linarith)
  · intro i hai hn; exact ⟨hWadj i hai hn, hVadj i hai hn⟩
  · intro i hai j haj hij; exact ⟨hWfar i hai j haj hij, hVfar i hai j haj hij⟩
  · intro i j
    rcases le_total i j with hij | hji
    · exact hagreeLe i j hij
    · have hh := hagreeLe j i hji
      exact ⟨fun x hx => (hh.1 ⟨hx.2, hx.1⟩).symm,
        fun z hz => (hh.2 ⟨hz.2, hz.1⟩).symm⟩

end PoincareConjecture.BalancedNeckChain
