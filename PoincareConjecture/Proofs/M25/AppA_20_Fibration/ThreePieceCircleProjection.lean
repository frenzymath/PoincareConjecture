import PoincareConjecture.Definitions.Ch09.NeckCapTopology
import PoincareConjecture.Proofs.M25.Mathlib.TwoEndedFiberwiseInterpolation
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.ThreePieceCollars
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.CompatibleProductClocks
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.FullPreimageRestriction
import PoincareConjecture.Proofs.M25.AppA_20_Fibration.SmoothPeriodCircleArcs
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.OpenPartialHomeomorph.Composition

set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology
universe u
namespace PoincareConjecture.M25
open Topology3D

theorem exists_circle_projection_of_three_product_charts
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M]
    {eta : ℝ} (heta : 0 < eta)
    (e : Fin 3 → OpenPartialHomeomorph RoundCylinderSpace M)
    (hsource : ∀ i : Fin 3,
      (e i).source = univ ×ˢ Ioo (-eta) (1 + eta))
    (hsmooth : ∀ i : Fin 3,
      ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ (e i) (e i).source ∧
      ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ (e i).symm (e i).target)
    (hboundary : ∀ i : Fin 3,
      range (fun q : UnitTwoSphere => e i (q, 1)) =
        range (fun q : UnitTwoSphere => e (i + 1) (q, 0)))
    (hinter : ∀ i : Fin 3,
      (e i '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
          (e (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) =
        range (fun q : UnitTwoSphere => e (i + 1) (q, 0)))
    (hcover : (⋃ i : Fin 3, e i '' (univ ×ˢ Icc (0 : ℝ) 1)) = univ) :
    ∃ projection : M → UnitCircle,
      Continuous projection ∧ Function.Surjective projection ∧
      ContMDiff (𝓡 3) (𝓡 1) ∞ projection ∧
      (∀ b : UnitCircle, ∃ V : Set UnitCircle, IsOpen V ∧ b ∈ V ∧
        ∃ T : OpenPartialHomeomorph M (UnitTwoSphere × UnitCircle),
          T.source = projection ⁻¹' V ∧ T.target = univ ×ˢ V ∧
          ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞
            T T.source ∧
          ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ T.symm T.target ∧
          ∀ x ∈ T.source, (T x).2 = projection x) ∧
      (∀ i : Fin 3, projection ⁻¹' {periodCircleParam 3 (i.val : ℝ)} =
        range (fun q : UnitTwoSphere => e i (q, 0))) := by
  classical
  obtain ⟨D, delta, hd, hdeta, hd8, hangular, hfixed, _hderiv, hslabs, hcollar⟩ :=
    exists_compatible_product_clocks heta e hsource hsmooth hboundary hinter hcover
  let C : Set RoundCylinderSpace := univ ×ˢ Icc (0 : ℝ) 1
  let K : Fin 3 → Set M := fun i => e i '' C
  let S : Fin 3 → Set M := fun i => range (fun q : UnitTwoSphere => e i (q, 0))
  have hCsource (i : Fin 3) : C ⊆ (e i).source := by
    intro z hz
    rw [hsource i]
    exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hzero (q : UnitTwoSphere) : (q, (0 : ℝ)) ∈ C := by simp [C]
  have hone (q : UnitTwoSphere) : (q, (1 : ℝ)) ∈ C := by simp [C]
  have hKtarget (i : Fin 3) : K i ⊆ (e i).target := by
    rintro x ⟨z, hz, rfl⟩
    exact (e i).map_source (hCsource i hz)
  have hKcoord (i : Fin 3) {x : M} (hx : x ∈ K i) : (e i).symm x ∈ C := by
    obtain ⟨z, hz, rfl⟩ := hx
    rwa [(e i).left_inv (hCsource i hz)]
  have hcompact (i : Fin 3) : IsCompact (K i) :=
    (isCompact_univ.prod isCompact_Icc).image_of_continuousOn
      ((e i).continuousOn.mono (hCsource i))
  have hwhole : (⋃ i : Fin 3, K i) = univ := hcover
  let : CompactSpace M := isCompact_univ_iff.mp
    (hwhole ▸ isCompact_iUnion hcompact)
  let gamma : ℝ → UnitCircle := periodCircleParam 3
  let J := periodUnitCircleHomeomorph 3 (by norm_num : (3 : ℝ) ≠ 0)
  let : Fact (0 < (3 : ℝ)) := ⟨by norm_num⟩
  have hgamma (s : ℝ) : J (s : AddCircle (3 : ℝ)) = gamma s :=
    periodUnitCircleHomeomorph_coe 3 (by norm_num) s
  have hperiod (s : ℝ) : gamma (s + 3) = gamma s := by
    rw [← hgamma, ← hgamma, AddCircle.coe_add_period]
  have hperiodZero : gamma 3 = gamma 0 := by simpa only [zero_add] using hperiod 0
  have hgammaIco {s t : ℝ} (hs : s ∈ Ico (0 : ℝ) 3)
      (ht : t ∈ Ico (0 : ℝ) 3) (h : gamma s = gamma t) : s = t := by
    apply (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (a := (0 : ℝ)) (by simpa using hs) (by simpa using ht)).mp
    apply J.injective
    simpa only [hgamma] using h
  have hgammaClosed {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 3)
      (ht : t ∈ Icc (0 : ℝ) 3) (h : gamma s = gamma t) :
      s = t ∨ (s = 0 ∧ t = 3) ∨ (s = 3 ∧ t = 0) := by
    by_cases hs3 : s = 3
    · subst s
      by_cases ht3 : t = 3
      · exact Or.inl ht3.symm
      · right; right
        refine ⟨rfl, ?_⟩
        apply Eq.symm
        apply hgammaIco (by norm_num) ⟨ht.1, lt_of_le_of_ne ht.2 ht3⟩
        exact hperiodZero.symm.trans h
    by_cases ht3 : t = 3
    · subst t
      right; left
      refine ⟨?_, rfl⟩
      apply hgammaIco ⟨hs.1, lt_of_le_of_ne hs.2 hs3⟩ (by norm_num)
      exact h.trans hperiodZero
    exact Or.inl (hgammaIco ⟨hs.1, lt_of_le_of_ne hs.2 hs3⟩
      ⟨ht.1, lt_of_le_of_ne ht.2 ht3⟩ h)
  have hival (i : Fin 3) : (0 : ℝ) ≤ i.val ∧ (i.val : ℝ) ≤ 2 := by
    fin_cases i <;> norm_num
  have hnextPhase (i : Fin 3) : gamma ((i.val : ℝ) + 1) = gamma ((i + 1).val : ℝ) := by
    fin_cases i <;> norm_num [Fin.add_def]
    exact hperiodZero
  let phi : Fin 3 → M → ℝ := fun i x => (D i ((e i).symm x)).2
  have hphi (i : Fin 3) {x : M} (hx : x ∈ K i) : phi i x ∈ Icc (0 : ℝ) 1 := by
    have hy : D i ((e i).symm x) ∈ C := by
      change D i ((e i).symm x) ∈ univ ×ˢ Icc (0 : ℝ) 1
      rw [← (hslabs i).1]
      exact ⟨(e i).symm x, hKcoord i hx, rfl⟩
    exact hy.2
  have hphiZero (i : Fin 3) (q : UnitTwoSphere) : phi i (e i (q, 0)) = 0 := by
    simp only [phi, (e i).left_inv (hCsource i (hzero q)), (hfixed i q).1]
  have hphiOne (i : Fin 3) (q : UnitTwoSphere) : phi i (e i (q, 1)) = 1 := by
    simp only [phi, (e i).left_inv (hCsource i (hone q)), (hfixed i q).2]
  have hphaseAdjacent (i : Fin 3) {x : M} (hx : x ∈ K i ∩ K (i + 1)) :
      gamma ((i.val : ℝ) + phi i x) = gamma (((i + 1).val : ℝ) + phi (i + 1) x) := by
    change x ∈ (e i '' (univ ×ˢ Icc (0 : ℝ) 1)) ∩
      (e (i + 1) '' (univ ×ˢ Icc (0 : ℝ) 1)) at hx
    rw [hinter i] at hx
    obtain ⟨q, hq⟩ := hx
    have hu : x ∈ range (fun p : UnitTwoSphere => e i (p, 1)) := by
      rw [hboundary i]
      exact ⟨q, hq⟩
    obtain ⟨p, hp⟩ := hu
    rw [← hp, hphiOne]
    rw [hp, ← hq, hphiZero, add_zero]
    exact hnextPhase i
  have hphaseAgree (i j : Fin 3) {x : M} (hi : x ∈ K i) (hj : x ∈ K j) :
      gamma ((i.val : ℝ) + phi i x) = gamma ((j.val : ℝ) + phi j x) := by
    have hcases : j = i ∨ j = i + 1 ∨ i = j + 1 := by
      fin_cases i <;> fin_cases j <;> decide
    rcases hcases with h | h | h
    · subst j; rfl
    · subst j; exact hphaseAdjacent i ⟨hi, hj⟩
    · subst i; exact (hphaseAdjacent j ⟨hj, hi⟩).symm
  have hchoose (x : M) : ∃ i : Fin 3, x ∈ K i := by
    apply mem_iUnion.mp
    rw [hwhole]
    exact mem_univ x
  let index : M → Fin 3 := fun x => (hchoose x).choose
  let projection : M → UnitCircle := fun x => gamma ((index x).val + phi (index x) x)
  have hp (i : Fin 3) {x : M} (hx : x ∈ K i) :
      projection x = gamma ((i.val : ℝ) + phi i x) :=
    hphaseAgree (index x) i (hchoose x).choose_spec hx
  have hraw (i : Fin 3) (q : UnitTwoSphere) {s : ℝ} (hs : s ∈ Ioo (-delta) delta) :
      projection (e i (q, s)) = gamma ((i.val : ℝ) + s) := by
    obtain ⟨ht, hcur, hprev, _, hclock, hpreviousClock⟩ := hcollar i q s hs
    have hz : (q, s) ∈ (e i).source := by
      rw [hsource i]
      exact ⟨mem_univ _, by constructor <;> linarith [hs.1, hs.2]⟩
    by_cases hs0 : 0 ≤ s
    · rw [hp i (hcur.mpr hs0)]
      simp only [phi, (e i).left_inv hz, hclock]
    · rw [hp (i - 1) (hprev.mpr (le_of_not_ge hs0))]
      change gamma (((i - 1).val : ℝ) +
        (D (i - 1) ((e (i - 1)).symm (e i (q, s)))).2) = _
      rw [hpreviousClock]
      fin_cases i <;> norm_num [Fin.sub_def]
      · rw [show (2 : ℝ) + (1 + s) = s + 3 by ring, hperiod]
      · congr 1
        ring
  have hendpoint (i : Fin 3) {x : M} (hx : x ∈ K i) {t : ℝ}
      (ht : t = 0 ∨ t = 1) (hv : phi i x = t) :
      x ∈ range (fun q : UnitTwoSphere => e i (q, t)) := by
    let z := (e i).symm x
    have hz : D i z = (z.1, t) := Prod.ext (hangular i z).1 hv
    have hfix : D i (z.1, t) = (z.1, t) := by
      rcases ht with rfl | rfl
      · exact (hfixed i z.1).1
      · exact (hfixed i z.1).2
    have heq : z = (z.1, t) := (D i).injective (hz.trans hfix.symm)
    refine ⟨z.1, ?_⟩
    change e i (z.1, t) = x
    rw [← heq]
    exact (e i).right_inv (hKtarget i hx)
  have hseamFiber (i : Fin 3) : projection ⁻¹' {gamma (i.val : ℝ)} = S i := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := hchoose x
      have hv := hphi j hj
      have hphase : gamma ((j.val : ℝ) + phi j x) = gamma (i.val : ℝ) := (hp j hj).symm.trans hx
      have hval := hgammaClosed
        (show (j.val : ℝ) + phi j x ∈ Icc (0 : ℝ) 3 by
          constructor <;> linarith [(hival j).1, (hival j).2, hv.1, hv.2])
        ⟨(hival i).1, (hival i).2.trans (by norm_num)⟩ hphase
      have hcases : (j = i ∧ phi j x = 0) ∨ (j + 1 = i ∧ phi j x = 1) := by
        rcases hval with h | ⟨h, h'⟩ | ⟨h, h'⟩ <;>
          fin_cases i <;> fin_cases j <;> norm_num [Fin.add_def] at h hv ⊢
        all_goals try norm_num at h'
        all_goals linarith only [h, hv.1, hv.2]
      rcases hcases with ⟨rfl, hz⟩ | ⟨hji, hz⟩
      · exact hendpoint j hj (Or.inl rfl) hz
      · have hx' := hendpoint j hj (Or.inr rfl) hz
        rw [hboundary j, hji] at hx'
        exact hx'
    · rintro ⟨q, rfl⟩
      have hx : e i (q, 0) ∈ K i := ⟨(q, 0), hzero q, rfl⟩
      change projection (e i (q, 0)) = gamma (i.val : ℝ)
      rw [hp i hx, hphiZero, add_zero]
  have hinteriorFiber (i : Fin 3) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
      {x : M} (hx : projection x = gamma ((i.val : ℝ) + s)) :
      x ∈ K i ∧ phi i x = s := by
    obtain ⟨j, hj⟩ := hchoose x
    have hv := hphi j hj
    have hphase := hgammaClosed
      (show (j.val : ℝ) + phi j x ∈ Icc (0 : ℝ) 3 by
        constructor <;> linarith [(hival j).1, (hival j).2, hv.1, hv.2])
      (show (i.val : ℝ) + s ∈ Icc (0 : ℝ) 3 by
        constructor <;> linarith [(hival i).1, (hival i).2, hs.1, hs.2])
      ((hp j hj).symm.trans hx)
    have hreal : (j.val : ℝ) + phi j x = (i.val : ℝ) + s := by
      rcases hphase with h | ⟨_, h⟩ | ⟨_, h⟩
      · exact h
      · linarith [(hival i).2, hs.2]
      · linarith [(hival i).1, hs.1]
    have hji : j = i := by
      fin_cases i <;> fin_cases j <;> norm_num at hreal hv hs ⊢ <;>
        linarith only [hreal, hv.1, hv.2, hs.1, hs.2]
    subst j
    exact ⟨hj, by linarith⟩
  have hlocalChart (a b v : ℝ) (hab : a < b) (hlen : b < a + 3)
      (E : OpenPartialHomeomorph RoundCylinderSpace M)
      (hEsource : E.source = univ ×ˢ Ioo a b)
      (hEs : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ E E.source)
      (hEi : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ E.symm E.target)
      (hEformula : ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo a b →
        projection (E (q, s)) = gamma (v + s)) :
      ∃ W : Set UnitCircle, IsOpen W ∧
        (∀ s ∈ Ioo a b, gamma (v + s) ∈ W) ∧
        ∃ j : OpenPartialHomeomorph M (UnitTwoSphere × UnitCircle),
          j.source = E.target ∧ j.target = univ ×ˢ W ∧
          ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ j j.source ∧
          ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ j.symm j.target ∧
          ∀ x ∈ j.source, (j x).2 = projection x := by
    obtain ⟨c0, hc0source, _, hc0formula, hc0s, hc0i⟩ :=
      exists_smooth_period_circle_arc 3 (by norm_num) (v + a) (v + b)
        (by linarith) (by linarith)
    let A := (Homeomorph.addLeft v).toOpenPartialHomeomorph
    let c := A.trans c0
    have hcsource : c.source = Ioo a b := by
      ext s
      change (s ∈ univ ∧ v + s ∈ c0.source) ↔ s ∈ Ioo a b
      rw [hc0source]
      simp only [mem_univ, true_and, mem_Ioo]
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    have hcformula (s : ℝ) : c s = gamma (v + s) := hc0formula (v + s)
    have hcs : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 1) ∞ c c.source :=
      hc0s.comp (contMDiff_const.add contMDiff_id).contMDiffOn (fun _ hz => hz.2)
    have hci : ContMDiffOn (𝓡 1) 𝓘(ℝ, ℝ) ∞ c.symm c.target := by
      exact contMDiff_const.contMDiffOn.neg.add (hc0i.mono (fun _ hz => hz.1))
    let B := (OpenPartialHomeomorph.refl UnitTwoSphere).prod c
    have hBsource : B.source = E.source := by
      change univ ×ˢ c.source = E.source
      rw [hcsource, hEsource]
    have hBs : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) ((𝓡 2).prod (𝓡 1)) ∞
        B B.source := contMDiff_id.contMDiffOn.prodMap hcs
    have hBi : ContMDiffOn ((𝓡 2).prod (𝓡 1)) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞
        B.symm B.target := contMDiff_id.contMDiffOn.prodMap hci
    let j := E.symm.trans B
    have hjsource : j.source = E.target := by
      apply inter_eq_left.mpr
      intro x hx
      exact hBsource.symm ▸ E.map_target hx
    have hjtarget : j.target = univ ×ˢ c.target := by
      change B.target ∩ B.symm ⁻¹' E.source = B.target
      apply inter_eq_left.mpr
      intro y hy
      exact hBsource ▸ B.map_target hy
    refine ⟨c.target, c.open_target, ?_, j, hjsource, hjtarget, ?_, ?_, ?_⟩
    · intro s hs
      rw [← hcformula]
      exact c.map_source (hcsource.symm ▸ hs)
    · exact hBs.comp (hEi.mono (fun _ hx => hx.1)) (fun _ hx => hx.2)
    · exact hEs.comp (hBi.mono (fun _ hy => hy.1)) (fun _ hy => hy.2)
    · intro x hx
      have hxt : x ∈ E.target := hjsource ▸ hx
      have hz : E.symm x ∈ univ ×ˢ Ioo a b := hEsource ▸ E.map_target hxt
      change c (E.symm x).2 = projection x
      rw [hcformula, ← hEformula (E.symm x).1 (E.symm x).2 hz.2]
      exact congrArg projection (E.right_inv hxt)
  have hseamChart (i : Fin 3) :
      ∃ W : Set UnitCircle, IsOpen W ∧ gamma (i.val : ℝ) ∈ W ∧
        ∃ j : OpenPartialHomeomorph M (UnitTwoSphere × UnitCircle),
          j.target = univ ×ˢ W ∧
          ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ j j.source ∧
          ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ j.symm j.target ∧
          (∀ x ∈ j.source, (j x).2 = projection x) ∧
          projection ⁻¹' {gamma (i.val : ℝ)} ⊆ j.source := by
    let U : Set RoundCylinderSpace := univ ×ˢ Ioo (-delta) delta
    have hU : U ⊆ (e i).source := by
      intro z hz
      rw [hsource i]
      exact ⟨mem_univ _, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
    let E := (e i).restrOpen U (isOpen_univ.prod isOpen_Ioo)
    have hEs : E.source = U := inter_eq_right.mpr hU
    obtain ⟨W, hW, hWin, j, hjs, hjt, hjsm, hjim, hjsecond⟩ :=
      hlocalChart (-delta) delta (i.val : ℝ) (by linarith) (by linarith) E hEs
        ((hsmooth i).1.mono (fun _ hz => hz.1))
        ((hsmooth i).2.mono (fun _ hz => hz.1)) (fun q _ hs => hraw i q hs)
    refine ⟨W, hW, ?_, j, hjt, hjsm, hjim, hjsecond, ?_⟩
    · simpa using hWin 0 ⟨by linarith, hd⟩
    · intro x hx
      rw [hseamFiber i] at hx
      obtain ⟨q, rfl⟩ := hx
      rw [hjs]
      exact E.map_source (hEs.symm ▸ ⟨mem_univ _, by constructor <;> linarith⟩)
  have hinteriorChart (i : Fin 3) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
      ∃ W : Set UnitCircle, IsOpen W ∧ gamma ((i.val : ℝ) + s) ∈ W ∧
        ∃ j : OpenPartialHomeomorph M (UnitTwoSphere × UnitCircle),
          j.target = univ ×ˢ W ∧
          ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ j j.source ∧
          ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ j.symm j.target ∧
          (∀ x ∈ j.source, (j x).2 = projection x) ∧
          projection ⁻¹' {gamma ((i.val : ℝ) + s)} ⊆ j.source := by
    let U : Set RoundCylinderSpace := univ ×ˢ Ioo (0 : ℝ) 1
    let G := (D i).symm.toHomeomorph.toOpenPartialHomeomorph.trans (e i)
    have hDinv (z : RoundCylinderSpace) (hz : z ∈ U) : (D i).symm z ∈ U := by
      have heq := (hslabs i).2.2.1
      change z ∈ univ ×ˢ Ioo (0 : ℝ) 1 at hz
      rw [← heq] at hz
      obtain ⟨y, hy, hyeq⟩ := hz
      simpa only [← hyeq, Diffeomorph.symm_apply_apply] using hy
    have hU : U ⊆ G.source := by
      intro z hz
      exact ⟨mem_univ _, hCsource i ⟨mem_univ _, (hDinv z hz).2.1.le,
        (hDinv z hz).2.2.le⟩⟩
    let E := G.restrOpen U (isOpen_univ.prod isOpen_Ioo)
    have hEs : E.source = U := inter_eq_right.mpr hU
    have hEsm : ContMDiffOn ((𝓡 2).prod 𝓘(ℝ, ℝ)) (𝓡 3) ∞ E E.source :=
      (hsmooth i).1.comp (D i).symm.contMDiff.contMDiffOn (fun _ hz => hz.1.2)
    have hEim : ContMDiffOn (𝓡 3) ((𝓡 2).prod 𝓘(ℝ, ℝ)) ∞ E.symm E.target :=
      (D i).contMDiff.comp_contMDiffOn ((hsmooth i).2.mono (fun _ hz => hz.1.1))
    have hEf (q : UnitTwoSphere) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
        projection (E (q, t)) = gamma ((i.val : ℝ) + t) := by
      have hz : (D i).symm (q, t) ∈ C :=
        ⟨mem_univ _, (hDinv (q, t) ⟨mem_univ _, ht⟩).2.1.le,
          (hDinv (q, t) ⟨mem_univ _, ht⟩).2.2.le⟩
      have hx : E (q, t) ∈ K i := ⟨(D i).symm (q, t), hz, rfl⟩
      rw [hp i hx]
      change gamma ((i.val : ℝ) + (D i ((e i).symm (e i ((D i).symm (q, t))))).2) = _
      rw [(e i).left_inv (hCsource i hz), (D i).apply_symm_apply]
    obtain ⟨W, hW, hWin, j, hjs, hjt, hjsm, hjim, hjsecond⟩ :=
      hlocalChart 0 1 (i.val : ℝ) (by norm_num) (by norm_num) E hEs hEsm hEim hEf
    refine ⟨W, hW, hWin s hs, j, hjt, hjsm, hjim, hjsecond, ?_⟩
    intro x hx
    obtain ⟨hxK, hv⟩ := hinteriorFiber i hs hx
    let z := D i ((e i).symm x)
    have hz : z ∈ U := by
      refine ⟨mem_univ _, ?_⟩
      change phi i x ∈ Ioo (0 : ℝ) 1
      rw [hv]
      exact hs
    have hzx : E z = x := by
      change e i ((D i).symm (D i ((e i).symm x))) = x
      rw [(D i).symm_apply_apply]
      exact (e i).right_inv (hKtarget i hxK)
    rw [hjs, ← hzx]
    exact E.map_source (hEs.symm ▸ hz)
  have hcharts (b : UnitCircle) :
      ∃ W : Set UnitCircle, IsOpen W ∧ b ∈ W ∧
        ∃ j : OpenPartialHomeomorph M (UnitTwoSphere × UnitCircle),
          j.target = univ ×ˢ W ∧
          ContMDiffOn (𝓡 3) ((𝓡 2).prod (𝓡 1)) ∞ j j.source ∧
          ContMDiffOn ((𝓡 2).prod (𝓡 1)) (𝓡 3) ∞ j.symm j.target ∧
          (∀ x ∈ j.source, (j x).2 = projection x) ∧
          projection ⁻¹' {b} ⊆ j.source := by
    obtain ⟨t, ht, htb⟩ := AddCircle.eq_coe_Ico (J.symm b)
    have hgb : gamma t = b := by rw [← hgamma, htb, J.apply_symm_apply]
    have hsplit : ∃ i : Fin 3, ∃ s ∈ Ico (0 : ℝ) 1, t = (i.val : ℝ) + s := by
      by_cases ht1 : t < 1
      · exact ⟨0, t, ⟨ht.1, ht1⟩, by simp⟩
      by_cases ht2 : t < 2
      · refine ⟨1, t - 1, ⟨by linarith, by linarith⟩, ?_⟩
        norm_num
      · refine ⟨2, t - 2, ⟨by linarith, by linarith [ht.2]⟩, ?_⟩
        norm_num
    obtain ⟨i, s, hs, rfl⟩ := hsplit
    rw [← hgb]
    by_cases hs0 : s = 0
    · simpa only [hs0, add_zero] using hseamChart i
    · exact hinteriorChart i ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩
  have hps : ContMDiff (𝓡 3) (𝓡 1) ∞ projection := by
    intro x
    obtain ⟨W, _, _, j, _, hjs, _, hsecond, hfiber⟩ := hcharts (projection x)
    have hx : x ∈ j.source := hfiber rfl
    have hon : ContMDiffOn (𝓡 3) (𝓡 1) ∞ projection j.source :=
      (contMDiff_snd.comp_contMDiffOn hjs).congr (fun y hy => (hsecond y hy).symm)
    exact hon.contMDiffAt (j.open_source.mem_nhds hx)
  have hsurj : Function.Surjective projection := by
    intro b
    obtain ⟨W, _, hb, j, hjt, _, _, hsecond, _⟩ := hcharts b
    let q : UnitTwoSphere := Classical.choice
      ((NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 3))) (r := 1)).mpr
        zero_le_one).coe_sort
    have hy : (q, b) ∈ j.target := hjt.symm ▸ ⟨mem_univ q, hb⟩
    refine ⟨j.symm (q, b), ?_⟩
    rw [← hsecond _ (j.map_target hy), j.right_inv hy]
  refine ⟨projection, hps.continuous, hsurj, hps, ?_, hseamFiber⟩
  intro b
  obtain ⟨W, hW, hb, j, hjt, hjs, hji, hsecond, hfiber⟩ := hcharts b
  obtain ⟨V, hV, hbV, _, T, hTs, hTt, hTsm, hTim, hTsecond⟩ :=
    exists_full_preimage_product_restriction projection hps.continuous j W hW hjt
      hjs hji hsecond hb hfiber
  exact ⟨V, hV, hbV, T, hTs, hTt, hTsm, hTim, hTsecond⟩

end PoincareConjecture.M25
