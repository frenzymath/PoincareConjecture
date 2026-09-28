import PoincareConjecture.Proofs.M25.AppA_1_Necks.SmoothChainChart
import PoincareConjecture.Proofs.M25.AppA_1_Necks.FiberwiseCylinderModel
import PoincareConjecture.Proofs.M25.AppA_1_Necks.CentralSphere
import PoincareConjecture.Proofs.M25.Mathlib.SmoothGraph
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Geometry.Manifold.Algebra.Structures
import Mathlib.Topology.OpenPartialHomeomorph.Composition











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.BalancedNeckChain



theorem exists_epsilonTubeCertificate_of_separating :
    ∃ epsilon0 : ℝ, 0 < epsilon0 ∧ epsilon0 ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
      [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
      [T3Space M] {g : RiemannianMetric 3 M} {epsilon : ℝ},
      ∀ (C : BalancedNeckChain g epsilon) (X : Set M),
      epsilon ≤ epsilon0 →
      (∀ i ∈ C.shape.active, (C.neck i).IsSeparating) →
      X ⊆ (⋃ i ∈ C.shape.active, (C.neck i).carrier) →
      ∃ T : EpsilonTubeCertificate g X,
        T.epsilon = epsilon ∧ HEq T.chain C ∧
        T.carrier = (⋃ i ∈ C.shape.active, (C.neck i).carrier) := by
  classical
  obtain ⟨epsilon0, he0, he0cap, hchart⟩ := exists_smooth_chain_partial_chart.{u}
  refine ⟨epsilon0, he0, he0cap, ?_⟩
  intro M _ _ _ _ _ _ g epsilon C X hepsilon hsep hcontains
  obtain ⟨k, hk⟩ := C.active_nonempty
  have hepos : 0 < epsilon := by
    rw [← C.epsilon_eq k hk]
    exact (C.neck k).epsilon_pos
  let L : ℝ := epsilon⁻¹
  let a : ℝ := 23 * L / 32
  let b : ℝ := 25 * L / 32
  let d : ℝ := 3 * L / 4
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
  have hLpos : 0 < L := inv_pos.mpr hepos
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hdmem : d ∈ Ioo (-L) L := by
    dsimp [d]
    constructor <;> linarith
  have hmemU (i : ℤ) (hi : i ∈ C.shape.active) {x : M}
      (hx : x ∈ (C.neck i).carrier) : x ∈ U :=
    mem_iUnion₂.mpr ⟨i, hi, hx⟩
  have hWsub (i : ℤ) (hi : i ∈ C.shape.active) : W i ⊆ U := by
    intro x hx
    dsimp only [W] at hx
    rw [if_pos hi] at hx
    exact hmemU i hi hx.1.1
  obtain ⟨e, F, B, P, _, _, he, hfirst, _, hell, hupper, hbounds,
    hPsource, hPtarget, hPs, hPi, hformula⟩ := hchart C hepsilon hsep k hk
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
  change ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ ell at hell
  change ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ upper at hupper
  change ∀ r : UnitTwoSphere, ell r ≤ -L ∧ L ≤ upper r at hbounds
  change P.source = U at hPsource
  change P.target = V at hPtarget
  have hwidth (r : UnitTwoSphere) : ell r < upper r := by
    have hr := hbounds r
    linarith
  have htarget : P.target = match C.shape with
      | .finite _ _ => {z | ell z.1 < z.2 ∧ z.2 < upper z.1}
      | .forward _ => {z | ell z.1 < z.2}
      | .backward _ => {z | z.2 < upper z.1}
      | .biInfinite => univ := by
    simpa [V] using hPtarget
  obtain ⟨T0, middle, hmiddle, hmidmem, hmidrange⟩ :
      ∃ (T0 : OpenCylinderModel U) (middle : UnitTwoSphere → ℝ),
        ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ middle ∧
        (∀ q : UnitTwoSphere, (q, middle q) ∈ P.target) ∧
        T0.middleSphere = range (fun q => P.symm (q, middle q)) := by
    obtain ⟨T0, _, _, hmiddle, hmidmem, hmidrange⟩ :=
      OpenCylinderModel.exists_of_fiberwise_partial_chart C.shape ell upper
        hell hupper hwidth P hPsource htarget hPs hPi
    exact ⟨T0, _, hmiddle, hmidmem, hmidrange⟩
  have hisotopies : ∀ i ∈ C.shape.active,
      SmoothSphereIsotopicIn U (C.neck i).central_sphere T0.middleSphere := by
    intro i hi
    obtain ⟨hesource, hetarget, hes, hei, _, hezero, hed⟩ := he i hi
    change (e i).source = univ ×ˢ Ioo (-L) L at hesource
    change ∀ r : UnitTwoSphere, e i (r, d) ∈ W i at hed
    let q : UnitTwoSphere → UnitTwoSphere := (B i).symm
    let height : UnitTwoSphere → ℝ := fun r => (F i (q r, d)).2
    have hheight : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ height :=
      ((F i).contMDiff.comp
        ((B i).symm.contMDiff.prodMk contMDiff_const)).snd
    have hdsource (r : UnitTwoSphere) : (q r, d) ∈ (e i).source := by
      rw [hesource]
      exact ⟨mem_univ _, hdmem⟩
    have hFpair (r : UnitTwoSphere) : F i (q r, d) = (r, height r) := by
      apply Prod.ext
      · exact ((hfirst i (q r, d)).1).trans ((B i).apply_symm_apply r)
      · rfl
    have hPg (r : UnitTwoSphere) : P (e i (q r, d)) = (r, height r) := by
      calc
        P (e i (q r, d)) = F i ((e i).symm (e i (q r, d))) :=
          (hformula i).1 (hed (q r))
        _ = F i (q r, d) := congrArg (F i) ((e i).left_inv (hdsource r))
        _ = (r, height r) := hFpair r
    have hheightMem (r : UnitTwoSphere) : (r, height r) ∈ P.target := by
      rw [← hPg r]
      exact P.map_source (hPsource.symm ▸ hWsub i hi (hed (q r)))
    have hjoin (r : UnitTwoSphere) : P.symm (r, height r) = e i (q r, d) := by
      rw [← hPg r]
      exact P.left_inv (hPsource.symm ▸ hWsub i hi (hed (q r)))
    let R : Diffeomorph ((𝓡 2).prod 𝓘(ℝ, ℝ))
        ((𝓡 2).prod 𝓘(ℝ, ℝ)) RoundCylinderSpace RoundCylinderSpace ∞ :=
      (B i).symm.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
    let J : OpenPartialHomeomorph RoundCylinderSpace M :=
      R.toHomeomorph.toOpenPartialHomeomorph.trans (e i)
    have hJsource : J.source = univ ×ˢ Ioo (-L) L := by
      ext z
      change (z ∈ univ ∧ (q z.1, z.2) ∈ (e i).source) ↔
        z ∈ univ ×ˢ Ioo (-L) L
      rw [hesource]
      simp only [mem_prod, mem_univ, true_and]
    have hJs : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ J J.source :=
      hes.comp R.contMDiff.contMDiffOn (fun z hz => hz.2)
    have hJi : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ J.symm J.target :=
      R.symm.contMDiff.comp_contMDiffOn (hei.mono (fun x hx => hx.1))
    have hslice (c : ℝ) (hc : c ∈ Ioo (-L) L) :
        Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
          (fun r : UnitTwoSphere => e i (q r, c)) := by
      have h := J.m25_isSmoothEmbedding_slice hJs hJi
        (RiemannianMetric.lineModelEquiv 2) c
        (fun r => hJsource.symm ▸ ⟨mem_univ r, hc⟩)
      exact h
    let alpha : ℝ → ℝ := fun t => Real.smoothTransition (4 * t)
    let beta : ℝ → ℝ := fun t => Real.smoothTransition (4 * t - 3)
    have has : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ alpha :=
      (Real.smoothTransition.contDiff.comp
        (contDiff_const.mul contDiff_id)).contMDiff
    have hbs : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ beta :=
      (Real.smoothTransition.contDiff.comp
        ((contDiff_const.mul contDiff_id).sub contDiff_const)).contMDiff
    have habounds (t : ℝ) : alpha t ∈ Icc (0 : ℝ) 1 :=
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    have hbbounds (t : ℝ) : beta t ∈ Icc (0 : ℝ) 1 :=
      ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
    have haone (t : ℝ) (ht : 1 / 4 ≤ t) : alpha t = 1 := by
      apply Real.smoothTransition.one_of_one_le
      linarith
    have hbzero (t : ℝ) (ht : t ≤ 3 / 4) : beta t = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      linarith
    have hfirstHeight (t : ℝ) : d * alpha t ∈ Ioo (-L) L := by
      have ha := habounds t
      refine ⟨lt_of_lt_of_le (neg_lt_zero.mpr hLpos) (mul_nonneg hdpos.le ha.1), ?_⟩
      calc
        d * alpha t ≤ d * 1 := mul_le_mul_of_nonneg_left ha.2 hdpos.le
        _ = d := mul_one d
        _ < L := hdmem.2
    have hconvex (r : UnitTwoSphere) :
        @Convex ℝ ℝ _ _ _ DistribMulAction.toDistribSMul.toSMul
          {s : ℝ | (r, s) ∈ P.target} := by
      rw [hPtarget]
      cases hshape : C.shape with
      | finite first last =>
        simp only [V, hshape, Set.mem_ofPred_eq]
        change @Convex ℝ ℝ _ _ _ DistribMulAction.toDistribSMul.toSMul
          (Ioo (ell r) (upper r))
        exact convex_Ioo _ _
      | forward first =>
        simp only [V, hshape, Set.mem_ofPred_eq]
        change @Convex ℝ ℝ _ _ _ DistribMulAction.toDistribSMul.toSMul
          (Ioi (ell r))
        exact convex_Ioi _
      | backward last =>
        simp only [V, hshape, Set.mem_ofPred_eq]
        change @Convex ℝ ℝ _ _ _ DistribMulAction.toDistribSMul.toSMul
          (Iio (upper r))
        exact convex_Iio _
      | biInfinite =>
        simp only [V, hshape]
        change @Convex ℝ ℝ _ _ _ DistribMulAction.toDistribSMul.toSMul
          (univ : Set ℝ)
        exact convex_univ
    let blend : ℝ × UnitTwoSphere → ℝ := fun z =>
      (1 - beta z.1) * height z.2 + beta z.1 * middle z.2
    have hblend : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ blend :=
      ((contMDiff_const.sub (hbs.comp contMDiff_fst)).mul
        (hheight.comp contMDiff_snd)).add
        ((hbs.comp contMDiff_fst).mul (hmiddle.comp contMDiff_snd))
    have hblendMem (t : ℝ) (r : UnitTwoSphere) : (r, blend (t, r)) ∈ P.target := by
      change (1 - beta t) * height r + beta t * middle r ∈
        {s : ℝ | (r, s) ∈ P.target}
      simpa only [smul_eq_mul] using
        (hconvex r (hheightMem r) (hmidmem r)
          (sub_nonneg.mpr (hbbounds t).2) (hbbounds t).1 (by ring))
    let H0 : ℝ × UnitTwoSphere → M := fun z => e i (q z.2, d * alpha z.1)
    let H1 : ℝ × UnitTwoSphere → M := fun z => P.symm (z.2, blend z)
    have h0s : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ H0 := by
      apply hes.comp_contMDiff
        (((B i).symm.contMDiff.comp contMDiff_snd).prodMk
          (contMDiff_const.mul (has.comp contMDiff_fst)))
      intro z
      rw [hesource]
      exact ⟨mem_univ _, hfirstHeight z.1⟩
    have h1s : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ H1 :=
      hPi.comp_contMDiff (contMDiff_snd.prodMk hblend)
        (fun z => hblendMem z.1 z.2)
    have h0embed (t : ℝ) : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
        (fun r : UnitTwoSphere => H0 (t, r)) :=
      hslice (d * alpha t) (hfirstHeight t)
    have h1embed (t : ℝ) : Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
        (fun r : UnitTwoSphere => H1 (t, r)) :=
      let hgraph : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun r : UnitTwoSphere => blend (t, r)) := by
        change ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞
          (fun r : UnitTwoSphere => (1 - beta t) * height r + beta t * middle r)
        exact (contMDiff_const.mul hheight).add (contMDiff_const.mul hmiddle)
      P.symm.m25_isSmoothEmbedding_graph hPi hPs (RiemannianMetric.lineModelEquiv 2)
        (fun r => blend (t, r))
        hgraph
        (hblendMem t)
    have h0range (t : ℝ) : range (fun r : UnitTwoSphere => H0 (t, r)) ⊆ U := by
      rintro x ⟨r, rfl⟩
      apply hmemU i hi
      rw [← hetarget]
      apply (e i).map_source
      rw [hesource]
      exact ⟨mem_univ _, hfirstHeight t⟩
    have h1range (t : ℝ) : range (fun r : UnitTwoSphere => H1 (t, r)) ⊆ U := by
      rintro x ⟨r, rfl⟩
      exact hPsource ▸ P.map_target (hblendMem t r)
    have h0flat (t : ℝ) (ht : 1 / 4 ≤ t) (r : UnitTwoSphere) :
        H0 (t, r) = e i (q r, d) := by
      dsimp only [H0]
      rw [haone t ht, mul_one]
    have h1flat (t : ℝ) (ht : t ≤ 3 / 4) (r : UnitTwoSphere) :
        H1 (t, r) = e i (q r, d) := by
      dsimp only [H1, blend]
      rw [hbzero t ht, sub_zero, one_mul, zero_mul, add_zero]
      exact hjoin r
    let H : ℝ × UnitTwoSphere → M := fun z =>
      if z.1 ≤ 1 / 2 then H0 z else H1 z
    have hH0 (z : ℝ × UnitTwoSphere) (hz : z.1 < 3 / 4) : H z = H0 z := by
      change (if z.1 ≤ 1 / 2 then H0 z else H1 z) = H0 z
      split_ifs with ht
      · rfl
      · exact (h1flat z.1 hz.le z.2).trans
          (h0flat z.1 (by linarith) z.2).symm
    have hH1 (z : ℝ × UnitTwoSphere) (hz : 1 / 4 < z.1) : H z = H1 z := by
      change (if z.1 ≤ 1 / 2 then H0 z else H1 z) = H1 z
      split_ifs with ht
      · exact (h0flat z.1 hz.le z.2).trans
          (h1flat z.1 (by linarith) z.2).symm
      · rfl
    have hHs : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ H univ := by
      have h0on : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ H0 univ :=
        h0s.contMDiffOn
      have h1on : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 3) ∞ H1 univ :=
        h1s.contMDiffOn
      apply contMDiffOn_of_locally_contMDiffOn
      intro z _
      by_cases ht : z.1 < 3 / 4
      · refine ⟨{w : ℝ × UnitTwoSphere | w.1 < 3 / 4},
          isOpen_lt continuous_fst continuous_const, ht, ?_⟩
        exact h0on.congr_mono (fun w hw => hH0 w hw.2) (subset_univ _)
      · refine ⟨{w : ℝ × UnitTwoSphere | 1 / 4 < w.1},
          isOpen_lt continuous_const continuous_fst, ?_, ?_⟩
        · change (1 / 4 : ℝ) < z.1
          linarith
        · exact h1on.congr_mono (fun w hw => hH1 w hw.2) (subset_univ _)
    refine ⟨H, hHs.mono (subset_univ _), ?_, ?_, ?_⟩
    · intro t _
      by_cases ht : t ≤ 1 / 2
      · have hf : (fun r : UnitTwoSphere => H (t, r)) = fun r => H0 (t, r) := by
          funext r
          exact if_pos ht
        rw [hf]
        exact ⟨h0embed t, h0range t⟩
      · have hf : (fun r : UnitTwoSphere => H (t, r)) = fun r => H1 (t, r) := by
          funext r
          exact if_neg ht
        rw [hf]
        exact ⟨h1embed t, h1range t⟩
    · have ha0 : alpha 0 = 0 :=
        Real.smoothTransition.zero_of_nonpos (by norm_num)
      have hf : (fun r : UnitTwoSphere => H (0, r)) =
          fun r => (C.neck i).coordinate_map (q r, 0) := by
        funext r
        change (if (0 : ℝ) ≤ 1 / 2 then H0 (0, r) else H1 (0, r)) = _
        rw [if_pos (by norm_num)]
        dsimp only [H0]
        rw [ha0, mul_zero]
        exact hezero (q r)
      rw [hf, ← (C.neck i).coordinate_zero_range]
      ext x
      constructor
      · rintro ⟨r, rfl⟩
        exact ⟨q r, rfl⟩
      · rintro ⟨r, rfl⟩
        refine ⟨B i r, ?_⟩
        change (C.neck i).coordinate_map ((B i).symm (B i r), 0) = _
        rw [(B i).symm_apply_apply]
    · have hb1 : beta 1 = 1 :=
        Real.smoothTransition.one_of_one_le (by norm_num)
      rw [hmidrange]
      congr 1
      funext r
      change (if (1 : ℝ) ≤ 1 / 2 then H0 (1, r) else H1 (1, r)) = _
      rw [if_neg (by norm_num)]
      dsimp only [H1, blend]
      rw [hb1, sub_self, zero_mul, one_mul, zero_add]
  let T : EpsilonTubeCertificate g X :=
    { epsilon := epsilon
      epsilon_pos := hepos
      epsilon_le_threshold := hepsilon.trans he0cap
      carrier := U
      carrier_open := hPsource ▸ P.open_source
      contains_X := hcontains
      chain := C
      carrier_eq_chain_union := by
        ext x
        constructor
        · intro hx
          obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
          exact mem_iUnion.mpr ⟨⟨i, hi⟩, hxi⟩
        · intro hx
          obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
          exact mem_iUnion₂.mpr ⟨i.1, i.2, hxi⟩
      cylinder := T0
      central_sphere_isotopy := hisotopies }
  exact ⟨T, rfl, HEq.rfl, rfl⟩

end PoincareConjecture.BalancedNeckChain
